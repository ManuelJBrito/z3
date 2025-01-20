#include "math/lp/dioph_eq.h"

#include <algorithm>
#include <limits>
#include <list>
#include <numeric>
#include <queue>

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"
#include "math/lp/var_register_dio.h"
/*
   Following paper: "A Practical Approach to Satisfiability  Modulo Linear
   Integer Arithmetic" by Alberto Griggio(griggio@fbk.eu).
    Data structures are:
    -- term_o: inherits lar_term and differs from it by having a constant, while
   lar_term is just a sum of monomials
    -- entry : has a dependency lar_term, keeping the history of the entry
   updates, the rational constant of the corresponding term_o, and the entry
   status that is in {F,S, NO_S_NO_F}. The entry status is used for efficiency
    reasons. It allows quickly check if an entry belongs to F, S, or neither.
    dioph_eq::imp main fields are
    -- lra: pointer to lar_solver.
    -- lia: point to int_solver.
    -- m_entries: it keeps all "entry" objects.
    -- m_e_matrix: i-th row of this matrix keeps the term corresponding to
   m_entries[i]. The actual term corresponding to m_entry[i] is the sum of the 
   matrix i-th row and the constant m_entry[].m_c. 
   The mapping between the columns of lar_solver and m_e_matrix is controlled by m_var_register. 
   local_to_lar_solver(lar_solver_to_local(j)) == j. If local_to_lar_solver(j) == -1 
   then j is a fresh variable, that is such that got introduced when normalizing a term like 3x-6y + 5z +11 = 0,
   when no variable has a coefficient +-1.
   
    -- get_term_from_entry(unsigned i) return a term corresponding i-th entry.
   If t = get_term_from_entry(i) then we have equality t = 0. Initially
   get_term_from_entry(i) is set to initt(j) = lra.get_term(j) - j, for some
   column j,where all fixed variables are replaced by their values. To track the
   explanations of equality t = 0 we initially set m_entries[i].m_l =
   lar_term(j), and update m_l accordingly with the pivot operations. The
   explanation is obtained by replacing term m_l = sum(aj*j) by the linear
    combination sum (aj*initt(j)) and joining the explanations of all fixed
   variables in the latter sum. entry_invariant(i) guarantees the validity of
   the i-th entry.
 */
namespace lp {
    template <typename T, typename K> bool contains(const T& t, K j) {
        return t.find(j) != t.end();
    }

    class dioph_eq::imp {
        // This class represents a term with an added constant number c, in form sum
        // {x_i*a_i} + c.
        class term_o : public lar_term {
            mpq m_c;

           public:
            term_o clone() const {
                term_o ret;
                for (const auto& p : *this) {
                    ret.add_monomial(p.coeff(), p.j());
                }
                ret.c() = c();
                ret.set_j(j());
                return ret;
            }
            term_o(const lar_term& t) : lar_term(t), m_c(0) {
                SASSERT(m_c.is_zero());
            }
            const mpq& c() const {
                return m_c;
            }
            mpq& c() {
                return m_c;
            }
            term_o() : m_c(0) {}
            void substitute_var_with_term(const term_o& t, unsigned col_to_subs) {
                mpq a = get_coeff(
                    col_to_subs);  // need to copy it becase the pointer value can be
                // changed during the next loop
                const mpq& coeff = t.get_coeff(col_to_subs);
                SASSERT(coeff.is_one() || coeff.is_minus_one());
                if (coeff.is_one()) {
                    a = -a;
                }
                for (auto p : t) {
                    if (p.j() == col_to_subs)
                        continue;
                    this->add_monomial(a * p.coeff(), p.j());
                }
                this->c() += a * t.c();
                this->m_coeffs.erase(col_to_subs);
            }

            friend term_o operator*(const mpq& k, const term_o& term) {
                term_o r;
                for (const auto& p : term)
                    r.add_monomial(p.coeff() * k, p.j());
                r.c() = k * term.c();
                return r;
            }

            friend term_o operator+(const term_o& a, const term_o& b) {
                term_o r = a.clone();
                for (const auto& p : b) {
                    r.add_monomial(p.coeff(), p.j());
                }
                r.c() += b.c();
                return r;
            }

            friend term_o operator-(const term_o& a, const term_o& b) {
                term_o r = a.clone();
                for (const auto& p : b)
                    r.sub_monomial(p.coeff(), p.j());
                r.c() -= b.c();
                return r;
            }
#if Z3DEBUG
            friend bool operator==(const term_o& a, const term_o& b) {
                term_o t = a.clone();
                t += mpq(-1) * b;
                return t.c() == mpq(0) && t.size() == 0;
            }
#endif
            term_o& operator+=(const term_o& t) {
                for (const auto& p : t) {
                    add_monomial(p.coeff(), p.j());
                }
                m_c += t.c();
                return *this;
            }
        };        

        std::ostream& print_S(std::ostream& out) {
            out << "S:\n";
            for (unsigned i : m_s) {
                print_entry(i, out);
            }
            return out;
        }

        std::ostream& print_lar_term_L(const lar_term& t, std::ostream& out) const {
            return print_linear_combination_customized(
                t.coeffs_as_vector(),
                [](int j) -> std::string { return "x" + std::to_string(j); }, out);
        }

        std::ostream& print_term_o(term_o const& term, std::ostream& out) const {
            if (term.size() == 0 && term.c().is_zero()) {
                out << "0";
                return out;
            }
            bool first = true;
            // Copy term to a std_vector and sort by p.j()
            std_vector<std::pair<mpq, unsigned>> sorted_term;
            sorted_term.reserve(term.size());
            for (const auto& p : term) {
                sorted_term.emplace_back(p.coeff(), p.j());
            }
            std::sort(
                sorted_term.begin(), sorted_term.end(),
                [](const auto& a, const auto& b) {
                    return a.second < b.second;
                });

            // Print the sorted term
            for (auto& [val, j] : sorted_term) {
                if (first) {
                    first = false;
                } else if (is_pos(val)) {
                    out << " + ";
                } else {
                    out << " - ";
                    val = -val;
                }
                if (val == -numeric_traits<mpq>::one())
                    out << " - ";
                else if (val != numeric_traits<mpq>::one())
                    out << T_to_string(val);
                out << "x";
                out << j;
            }

            // Handle the constant term separately
            if (!term.c().is_zero()) {
                if (!first) {
                    if (term.c().is_pos())
                        out << " + ";
                    else
                        out << " - ";
                }
                out << abs(term.c());
            }

            return out;
        }

        /*
          An annotated state is a triple ⟨E′, λ, σ⟩, where E′ is a set of pairs ⟨e,
          ℓ⟩ in which e is an equation and ℓ is a linear combination of variables
          from L
        */
        //
        enum class entry_status { F,
                                  S,
                                  NO_S_NO_F
        };
        struct entry {
            //lar_term m_l; the term is taken from matrix m_l_matrix of the index entry
            mpq m_c;  // the constant of the term, the term is taken from the row of
            // m_e_matrix with the same index as the entry
            entry_status m_entry_status;
        };

        var_register_dio m_var_register;
        std_vector<entry> m_entries;
        // the terms are stored in m_A and m_c
        static_matrix<mpq, mpq> m_e_matrix;  // the rows of the matrix are the terms,
        static_matrix<mpq, mpq> m_l_matrix;  // the rows of the matrix are the l_terms providing the certificate to the entries modulo the constant part
        int_solver& lia;
        lar_solver& lra;
        explanation m_infeas_explanation;
        indexed_vector<mpq> m_indexed_work_vector;
        bool m_report_branch = false;

        // set F
        std::list<unsigned> m_f;  // F = {λ(t):t in m_f}
        // set S
        std::list<unsigned> m_s;  // S = {λ(t): t in m_s}
        mpq m_c;                  // the constant of the equation
        lar_term m_tmp_l;
        // the dependency of the equation
        // map to open the term e.m_l
        // suppose e.m_l = sum {coeff*k}, then subst(e.m_e) = fix_var(sum
        // {coeff*lar.get_term(k)})

        std_vector<unsigned> m_k2s;
        struct fresh_definition {
            unsigned m_ei;
            unsigned m_origin;
            fresh_definition(unsigned i, unsigned o) : m_ei(i), m_origin(o) {}
        };
        std_vector<fresh_definition> m_fresh_definitions;

        unsigned m_conflict_index = -1;  // m_entries[m_conflict_index] gives the conflict
        unsigned m_max_number_of_iterations = 100;
        unsigned m_number_of_iterations;
        struct branch {
            unsigned m_j = UINT_MAX;
            mpq m_rs;
            // if m_left is true, then the branch is interpreted
            // as x[j] <= m_rs
            // otherwise x[j] >= m_rs
            bool m_left;
            bool m_fully_explored = false;
            void flip() {
                SASSERT(m_fully_explored == false);
                m_left = !m_left;
                m_fully_explored = true;
            }
        };
        struct variable_branch_stats {
            std::vector<unsigned> m_ii_after_left;
            // g_right[i] - the rumber of int infeasible after taking the i-ith
            // right branch
            std::vector<unsigned> m_ii_after_right;

            double score() const {
                double avm_lefts =
                    m_ii_after_left.size()
                        ? static_cast<double>(std::accumulate(
                              m_ii_after_left.begin(), m_ii_after_left.end(), 0)) /
                              m_ii_after_left.size()
                        : std::numeric_limits<double>::infinity();
                double avm_rights = m_ii_after_right.size()
                                        ? static_cast<double>(std::accumulate(
                                              m_ii_after_right.begin(),
                                              m_ii_after_right.end(), 0)) /
                                              m_ii_after_right.size()
                                        : std::numeric_limits<double>::infinity();
                return std::min(avm_lefts, avm_rights);
            }
        };

        void remove_term_callback(const lar_term *t) { 
            TRACE("d_undo", tout << "t:"<< t<<", t->j():"<< t->j() << std::endl;);
            TRACE("dioph_eq", lra.print_term(*t, tout); tout << ", t->j() =" << t->j() << std::endl;);
            if (!contains(m_active_terms, t)) {
                for (int i = m_added_terms.size() - 1; i >= 0; --i) {
                    if (m_added_terms[i] != t) continue;
                    if (i != m_added_terms.size() -1) 
                        m_added_terms[i] = m_added_terms.back();
                    m_added_terms.pop_back();
                    break; // all is done since the term has not made it to m_active_terms
                }
                return;
            }
            // deregister the term that has been activated
            for (const auto & p: t->ext_coeffs()) {        
                TRACE("dio_reg", tout << "derigister p.var():" << p.var() <<"->" << t->j() << std::endl; ); 
                auto it = m_columns_to_terms.find(p.var());
                SASSERT(it != m_columns_to_terms.end());
                it->second.erase(t->j());
                if (it->second.size() == 0) {
                    m_columns_to_terms.erase(it);
                }
            }
            SASSERT(std::find(m_added_terms.begin(), m_added_terms.end(), t) == m_added_terms.end());
            SASSERT(contains(m_active_terms, t));
            m_active_terms.erase(t);
            TRACE("dioph_eq", 
                  tout << "the deleted term column in m_l_matrix" << std::endl;
                  for  (auto p: m_l_matrix.column(t->j())) {
                      tout << "p.coeff():" << p.coeff()<< ", row " << p.var() << std::endl;
                  }
                  tout << "m_l_matrix has " << m_l_matrix.column_count() << " columns"<< std::endl;
                  tout << "and " << m_l_matrix.row_count() << " rows" << std::endl;
                  print_lar_term_L(*t, tout); tout << "; t->j()=" << t->j() << std::endl;
                );
            shrink_L_to_sizes();
        }
      
        struct undo_fixed_column : public trail {
            imp& m_imp;
            unsigned m_j;  // the column that has been added
            const mpq m_fixed_val;
            undo_fixed_column(imp& s, unsigned j) : m_imp(s), m_j(j) , m_fixed_val(s.lra.get_lower_bound(j).x) {
                SASSERT(s.lra.column_is_fixed(j));
            }

            void undo() override {
                m_imp.add_changed_column(m_j);
            }
        };
        
        void remove_last_entry() {
            unsigned ei = m_entries.size() - 1;
        
            if (m_entries.back().m_entry_status == entry_status::F) {
                remove_entry_index(this->m_f, ei);        
            } else {
                remove_entry_index(this->m_s, ei);        
            }
            m_entries.pop_back();
        }

        void eliminate_last_term_column() {
            unsigned j = m_l_matrix.column_count() - 1;
            make_sure_j_is_in_the_last_row_of_l_matrix();
            const auto &last_e_row = m_l_matrix.m_rows.back();
            mpq alpha;
            for (const auto p: last_e_row) {
                if (p.var() == j) {
                    alpha = p.coeff();
                    break;
                }
            }
            unsigned last_row_index= m_l_matrix.row_count() - 1;
            m_l_matrix.divide_row(last_row_index, alpha); // divide the last row by alpha
            std_vector<unsigned> rows_to_change;

            auto &column = m_l_matrix.m_columns[j];
            int pivot_col_cell_index = -1;
            for (unsigned k = 0; k < column.size(); k++) {
                if (column[k].var() == last_row_index) {
                    pivot_col_cell_index = k;
                    break;
                }
            }
            SASSERT(pivot_col_cell_index >= 0);
            
            if (pivot_col_cell_index != 0) {
                SASSERT(column.size() > 1);
                // swap the pivot column cell with the head cell
                auto c = column[0];
                column[0]  = column[pivot_col_cell_index];
                column[pivot_col_cell_index] = c;
                
                m_l_matrix.m_rows[last_row_index][column[0].offset()].offset() = 0;
                m_l_matrix.m_rows[c.var()][c.offset()].offset() = pivot_col_cell_index;
            }
            while (column.size() > 1) {
                auto & c = column.back();
                SASSERT(c.var() != last_row_index);
                m_l_matrix.pivot_row_to_row_given_cell(last_row_index, c, j);
                rows_to_change.push_back(c.var());
            }

            for (unsigned i : rows_to_change) {
                recalculate_entry(i);
            }
        }
        
        void make_sure_j_is_in_the_last_row_of_l_matrix() {
            unsigned j = m_l_matrix.column_count() - 1;
            const auto &last_e_row = m_l_matrix.m_rows.back();
            mpq alpha;
            for (const auto p: last_e_row) {
                if (p.var() == j) {
                    return;
                }
            }
            SASSERT(m_l_matrix.m_columns.back().size());
            unsigned i = m_l_matrix.m_columns[j][0].var();
            m_l_matrix.add_rows(mpq(1), i, m_l_matrix.row_count() - 1);
        }

        void shrink_L_to_sizes() {
            unsigned i = m_l_matrix.row_count() - 1;            
            eliminate_last_term_column();
            remove_last_row_in_matrix(m_l_matrix);
            remove_last_row_in_matrix(m_e_matrix);
            while(m_l_matrix.column_count() && m_l_matrix.m_columns.back().size() == 0) {
                m_l_matrix.m_columns.pop_back();
            }
            while(m_e_matrix.column_count() && m_e_matrix.m_columns.back().size() == 0) {                
                m_e_matrix.m_columns.pop_back();
            }
            m_var_register.shrink(m_e_matrix.column_count());

            auto it = std::find_if(m_fresh_definitions.begin(), m_fresh_definitions.end(), [i](auto const& fe) {
               return fe.m_origin == i;
            });
            if (it != m_fresh_definitions.end())
                *it = fresh_definition(-1, -1); 
            for (unsigned k = 0; k < m_k2s.size() ; k++) {
                if (m_k2s[k] == i) {
                    m_k2s[k] = -1;
                    break;
                }
            } 
            
            remove_entry_index(m_f, i);
            remove_entry_index(m_s, i);
            m_entries.pop_back();            
        }
        
        
        void remove_last_row_in_matrix(static_matrix<mpq, mpq>& m) {
                auto & last_row = m.m_rows.back();
                for (unsigned k = last_row.size(); k-- > 0;) {                
                    m.remove_element(last_row, last_row[k]);
                }
                m.m_rows.pop_back();                                
        }
        
        void remove_entry_index(std::list<unsigned> & l, unsigned ei) {
            auto it = std::find(l.begin(), l.end(), ei);
            if (it != l.end())
                l.erase(it);
        }
        
        std::unordered_set<unsigned> m_changed_columns;
        // m_column_to_terms[j] is the set of all k such lra.get_term(k) depends on j
        std::unordered_map<unsigned, std::unordered_set<unsigned>> m_columns_to_terms;  
        void add_changed_column(unsigned j) {
            TRACE("dioph_eq", lra.print_column_info(j, tout););
            m_changed_columns.insert(j);
        }
        std_vector<const lar_term*> m_added_terms;
        std::unordered_set<const lar_term*> m_active_terms;
        std_vector<variable_branch_stats> m_branch_stats;
        std_vector<branch> m_branch_stack;
        std_vector<constraint_index> m_explanation_of_branches;
        void add_term_callback(const lar_term* t) {
            unsigned j = t->j();
            TRACE("dioph_eq", tout << "term column t->j():" << j << std::endl; lra.print_term(*t, tout) << std::endl; );
            if (!lra.column_is_int(j)) {
               TRACE("dioph_eq", tout << "ignored a non-integral column" << std::endl;);
               return;
            }

            CTRACE("dioph_eq", !lra.column_has_term(j), tout << "added term that is not associated with a column yet" << std::endl;);

            if (!all_vars_are_int(*t)) {
                TRACE("dioph_eq", tout << "not all vars are integrall\n";);
                return;
            }
            m_added_terms.push_back(t);    
        }

        void update_column_bound_callback(unsigned j) {
            if (!lra.column_is_int(j) || !lra.column_is_fixed(j))
               return;
            m_changed_columns.insert(j);
            auto undo = undo_fixed_column(*this, j);
            lra.trail().push(undo) ;
        }

       public:
        imp(int_solver& lia, lar_solver& lra) : lia(lia), lra(lra) {
            lra.m_add_term_callback=[this](const lar_term*t){add_term_callback(t);};
            lra.m_remove_term_callback = [this](const lar_term*t){remove_term_callback(t);};
            lra.m_update_column_bound_callback = [this](unsigned j){update_column_bound_callback(j);};
        }
        term_o get_term_from_entry(unsigned i) const {
            term_o t;
            for (const auto& p : m_e_matrix.m_rows[i]) {
                t.add_monomial(p.coeff(), p.var());
            }
            t.c() = m_entries[i].m_c;
            return t;
        }

        // adds variable j of lar_solver to the local diophantine handler
        unsigned add_var(unsigned j) {
            return this->m_var_register.add_var(j, true);
        }

        unsigned local_to_lar_solver(unsigned j) const {
            return m_var_register.local_to_external(j);
        }

        void register_columns_to_term(const lar_term& t) {
            TRACE("dioph_eq", tout << "register term:"; lra.print_term(t, tout); tout << ", t.j()=" << t.j() << std::endl;);
            for (const auto &p: t.ext_coeffs()) {
                auto it = m_columns_to_terms.find(p.var());
                TRACE("dio_reg", tout << "register p.var():" << p.var() <<"->" << t.j() << std::endl; ); 
                
                if (it != m_columns_to_terms.end()) {
                    it->second.insert(t.j());
                }
                else {
                    std::unordered_set<unsigned> s;
                    s.insert(t.j());
                    m_columns_to_terms[p.var()] = s;                    
                }                
            }
        }
        // the term has form sum(a_i*x_i) - t.j() = 0,
        void fill_entry(const lar_term& t) {
            TRACE("dioph_eq", print_lar_term_L(t, tout) << std::endl;);
            entry te = { mpq(0), entry_status::F};
            unsigned entry_index = (unsigned) m_entries.size();
            m_f.push_back(entry_index);
            m_entries.push_back(te);
            entry& e = m_entries.back();
            SASSERT(m_l_matrix.row_count() == m_e_matrix.row_count());
// fill m_l_matrix row
            m_l_matrix.add_row();
            // todo: consider to compress variables t.j() by using a devoted var_register for term columns
            m_l_matrix.add_columns_up_to(t.j());
            m_l_matrix.add_new_element(entry_index, t.j(), mpq(1));
// fill E-entry
            m_e_matrix.add_row();
            
            SASSERT(m_e_matrix.row_count() == m_entries.size());

            for (const auto& p : t.ext_coeffs()) {
                SASSERT(p.coeff().is_int());
                if (is_fixed(p.var()))
                    e.m_c += p.coeff() * lia.lower_bound(p.var()).x;
                else {
                    unsigned lj = add_var(p.var());
                    m_e_matrix.add_columns_up_to(lj);
                    m_e_matrix.add_new_element(entry_index, lj, p.coeff());
                }
            }
            SASSERT(entry_invariant(entry_index));
        }

        bool all_vars_are_int(const lar_term& term) const {
            for (const auto& p : term) {
                if (!lia.column_is_int(p.var()))
                    return false;
            }
            return true;
        } 

        void delete_column(unsigned j) {
            NOT_IMPLEMENTED_YET();
        }

        void clear_e_row(unsigned ei) {
            auto & row = m_e_matrix.m_rows[ei];
            while (row.size() > 0) {
                auto& c = row.back();
                m_e_matrix.remove_element(row, c);
            }
        }
        
        void recalculate_entry(unsigned ei) {
            TRACE("dioph_eq", print_entry(ei, tout) << std::endl;);
            mpq &c = m_entries[ei].m_c;
            c = mpq(0);
            open_l_term_to_work_vector(ei, c);
            clear_e_row(ei);
            mpq denom(1);
            for (const auto & p: m_indexed_work_vector) {
                unsigned lj = add_var(p.var());
                m_e_matrix.add_columns_up_to(lj);
                m_e_matrix.add_new_element(ei, lj, p.coeff());
                if (!denominator(p.coeff()).is_one()) {
                    denom = lcm(denom, denominator(p.coeff()));
                }
            }
            if (!denom.is_one()) {
                c *= denom;
                m_l_matrix.multiply_row(ei, denom);
                m_e_matrix.multiply_row(ei, denom);
            }
            SASSERT(entry_invariant(ei));
        }

        
        void process_changed_columns() {
            for (unsigned j : m_changed_columns) {
                if (j >= this->lra.column_count()) {
                    delete_column(j);
                }
            }
            std::unordered_set<unsigned> entries_to_recalculate;
            std::unordered_set<unsigned> changed_terms; // a term is signified by the term column, like j in lra.get_term(j)
            std_vector<unsigned> fresh_entries_to_remove;
            
            for (unsigned j : m_changed_columns) {  
                const auto it = m_columns_to_terms.find(j);
                if (it != m_columns_to_terms.end())                
                    for (unsigned k : it->second) {
                        changed_terms.insert(k);
                    }
                if (!m_var_register.external_is_used(j)) 
                    continue;
                for (const auto& p : m_e_matrix.column(this->lar_solver_to_local(j))) {
                    entries_to_recalculate.insert(p.var());
                }
            }
            for (unsigned j : changed_terms) {
                for (const auto & cs: m_l_matrix.column(j)) {
                    entries_to_recalculate.insert(cs.var());
                }
            }

            TRACE("dioph_eq", tout << "entries_to_recalculate:"; for (unsigned j : entries_to_recalculate) {tout << " " << j;});
            for (unsigned j = 0; j < m_fresh_definitions.size(); j++) {
                const fresh_definition& fd  = m_fresh_definitions[j];
                if (fd.m_ei == UINT_MAX) continue;
                if (contains(entries_to_recalculate, fd.m_origin)) {
                    fresh_entries_to_remove.push_back(j);
                    continue;
                }
             }

            TRACE("dioph_eq", tout << "found " << fresh_entries_to_remove.size() << " fresh entries to remove\n";
                  tout << "m_changed_columns:\n";
                  std::vector<unsigned> v(m_changed_columns.begin(), m_changed_columns.end());
                  std::sort(v.begin(), v.end());
                  for (unsigned j : v) {
                     tout << j << " ";
                  }
                 tout << std::endl;
             ); 
             while (fresh_entries_to_remove.size()) {
//                 enable_trace("d_once");
                 unsigned xt = fresh_entries_to_remove.back();
                 fresh_entries_to_remove.pop_back();
                 const fresh_definition & fd = m_fresh_definitions[xt];
                 TRACE("d_once", print_entry(fd.m_ei, tout) << std::endl; tout << "xt:" << xt << std::endl;);
                 unsigned last_ei = m_entries.size() - 1;
                 if (fd.m_ei != last_ei) { // not the last entry
                    transpose_entries(fd.m_ei, m_entries.size() -1 );
                    // we are not going to recalculate fd.m_ei
                    // but we might need to recalculate last_ei, which becomes fd.m_ei
                    if (contains(entries_to_recalculate, last_ei )) {
                        entries_to_recalculate.erase(last_ei),
                        entries_to_recalculate.insert(fd.m_ei);
                    }
                 }
                 for (const auto p: m_e_matrix.m_columns[xt]) {
                    entries_to_recalculate.insert(p.var());
                 }
                    
                 m_fresh_definitions[xt] = fresh_definition(-1,-1);
                 remove_last_entry();
                 remove_last_row_in_matrix(m_l_matrix);
                 remove_last_row_in_matrix(m_e_matrix);
             }
             
             for(unsigned k : entries_to_recalculate) {
                if (k >= m_entries.size())
                    continue;;
                recalculate_entry(k);
                move_entry_from_s_to_f(k);
                if (m_e_matrix.m_columns.back().size() == 0) {
                    m_e_matrix.m_columns.pop_back();
                    m_var_register.shrink(m_e_matrix.column_count());
                }
                if (m_l_matrix.m_columns.back().size() == 0) {
                    m_l_matrix.m_columns.pop_back();                    
                }
            }            
            m_changed_columns.clear();
        }

        void transpose_entries(unsigned i, unsigned k) {
            SASSERT(i != k);
            m_l_matrix.transpose_rows(i, k);
            m_e_matrix.transpose_rows(i, k);
            remove_entry_from_lists(i);
            remove_entry_from_lists(k);
            std::swap(m_entries[i], m_entries[k]);
            add_entry_to_lists(i);
            add_entry_to_lists(k);
            // transpose fresh definitions
            for (auto & fd: m_fresh_definitions) {
                if (fd.m_ei == i) 
                    fd.m_ei = k;
                else if (fd.m_ei == k)    
                    fd.m_ei = i;
            }
            //transpose m_k2s
            for (unsigned& t :  m_k2s) {
                if (t == i) 
                   t = k;
                else if (t == k)   
                   t = i;
            }
        }
        
        void remove_entry_from_lists(unsigned ei) {
            auto status = m_entries[ei].m_entry_status;
            if (status == entry_status::F) {
                m_f.remove(ei);
            } else {
                m_s.remove(ei);
            }
        }
        
        void add_entry_to_lists(unsigned ei) {
            auto status = m_entries[ei].m_entry_status;
            if (status == entry_status::F) {
                m_f.push_back(ei);
            } else {
                m_s.push_back(ei);
            }
        }
        

        void move_recalculated_to_F(const std::unordered_set<unsigned> &entries_to_recalculate) {
            for (auto it = this->m_s.begin(); it != m_s.end(); ) {
                if (contains(entries_to_recalculate, *it)) {
                    auto nit = it;
                    nit++;
                    m_s.erase(it);
                    it = nit;
                }
                else it++;
            }
            for (unsigned k = 0; k < m_k2s.size(); k++) {
                if (m_k2s[k] != UINT_MAX && contains(entries_to_recalculate, m_k2s[k])) {
                    m_k2s[k] = -1;
                }
            }
            for (unsigned ei: entries_to_recalculate) {
                SASSERT(std::find(m_f.begin(), m_f.end(), ei) == m_f.end());
                m_f.push_back(ei);
                m_entries[ei].m_entry_status = entry_status::F;
            }
        }

        bool entries_are_ok() {
            for (unsigned ei = 0; ei < m_entries.size();  ei++) {
                if (entry_invariant(ei) == false) {
                    TRACE("dioph_deb_eq", tout << "bad entry:"; print_entry(ei, tout););
                    return false;
                }
            }
            return true;
         }
        
        void init() {
            m_report_branch = false;
            m_conflict_index = -1;
            m_infeas_explanation.clear();
            lia.get_term().clear();
            m_number_of_iterations = 0;
            m_branch_stack.clear();
            m_lra_level = 0;
            process_changed_columns();
            for (const lar_term* t: m_added_terms) {
                m_active_terms.insert(t);
                fill_entry(*t);
                register_columns_to_term(*t);
            }
            
            SASSERT(is_in_sync());            
            
            m_added_terms.clear();
            SASSERT(entries_are_ok());
         }

        template <typename K>
        mpq gcd_of_coeffs(const K& k) {
            mpq g(0);
            for (const auto& p : k) {
                if (g.is_zero())
                    g = abs(p.coeff());
                else
                    g = gcd(g, p.coeff());
                if (g.is_one())
                    break;
            }
            return g;
        }

        std::ostream& print_dep(std::ostream& out, u_dependency* dep) {
            explanation ex(lra.flatten(dep));
            return lra.print_expl(out, ex);
        }

        bool has_fresh_var(unsigned row_index) const {
            for (const auto& p : m_e_matrix.m_rows[row_index]) {
                if (is_fresh_var(p.var()))
                    return true;
            }
            return false;
        }

        void prepare_lia_branch_report(unsigned ei, const entry& e, const mpq& g,
                                       const mpq new_c) {
            /* We have ep.m_e/g = 0, or sum((coff_i/g)*x_i) + new_c = 0,
               or sum((coeff_i/g)*x_i) = -new_c, where new_c is not an integer
               Then sum((coeff_i/g)*x_i) <= floor(-new_c) or sum((coeff_i/g)*x_i) >=
               ceil(-new_c)
            */
            lar_term& t = lia.get_term();
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                t.add_monomial(p.coeff() / g, local_to_lar_solver(p.var()));
            }
            lia.offset() = floor(-new_c);
            lia.is_upper() = true;
            m_report_branch = true;
            TRACE("dioph_eq", tout << "prepare branch:"; print_lar_term_L(t, tout)
                                                         << " <= " << lia.offset()
                                                         << std::endl;);
        }

        // A conflict is reported when the gcd of the monomial coefficients does not divide the free coefficent.
        // If there is no conflict the entry is divided, normalized, by gcd.
        // The function returns true if and only if there is no conflict. In the case of a conflict a branch 
        // can be returned as well.
        bool normalize_e_by_gcd(unsigned ei) {
            entry& e = m_entries[ei];
            TRACE("dioph_eq", print_entry(ei, tout) << std::endl;);
            mpq g = gcd_of_coeffs(m_e_matrix.m_rows[ei]);
            if (g.is_zero() || g.is_one()) {
                SASSERT(g.is_one() || e.m_c.is_zero());
                return true;
            }
            TRACE("dioph_eq", tout << "g:" << g << std::endl;);
            mpq c_g = e.m_c / g;
            if (c_g.is_int()) {
                for (auto& p : m_e_matrix.m_rows[ei]) {
                    p.coeff() /= g;
                }
                m_entries[ei].m_c = c_g;
                // e.m_l *= (1 / g);
                for (auto& p : m_l_matrix.m_rows[ei]) {
                    p.coeff() /= g;
                }

                TRACE("dioph_eq", tout << "ep_m_e:";
                      print_entry(ei, tout) << std::endl;);
                SASSERT(entry_invariant(ei));
                return true;
            }
            // c_g is not integral
            if (lra.stats().m_dio_calls %
                        lra.settings().dio_cut_from_proof_period() ==
                    0 &&
                !has_fresh_var(ei))
                prepare_lia_branch_report(ei, e, g, c_g);
            return false;
        }

        // returns true if no conflict is found and false otherwise
        bool normalize_by_gcd() {
            for (unsigned l : m_f) {
                if (!normalize_e_by_gcd(l)) {
                    SASSERT(entry_invariant(l));
                    m_conflict_index = l;
                    return false;
                }
                SASSERT(entry_invariant(l));
            }
            return true;
        }

        void init_term_from_constraint(term_o& t, const lar_base_constraint& c) {
            for (const auto& p : c.coeffs()) {
                t.add_monomial(p.first, p.second);
            }
            t.c() = -c.rhs();
        }

        // We look at term e.m_e: it is in form (+-)x_k + sum {a_i*x_i} + c = 0.
        // We substitute x_k in t by (+-)coeff*(sum {a_i*x_i} + c), where coeff is
        // the coefficient of x_k in t.

        void subs_front_in_indexed_vector(std::queue<unsigned>& q) {
            unsigned k = pop_front(q);
            if (m_indexed_work_vector[k].is_zero())
                return;
            const entry& e = entry_for_subs(k);
            SASSERT(e.m_entry_status == entry_status::S);
            TRACE("dioph_eq", tout << "k:" << k << ", in ";
                  print_term_o(create_term_from_ind_c(), tout) << std::endl;
                  tout << "subs with e:";
                  print_entry(m_k2s[k], tout) << std::endl;);
            mpq coeff =
                m_indexed_work_vector[k];    // need to copy since it will be zeroed
            m_indexed_work_vector.erase(k);  // m_indexed_work_vector[k] = 0;

            const auto& e_row = m_e_matrix.m_rows[m_k2s[k]];
            auto it = std::find_if(e_row.begin(), e_row.end(),
                                   [k](const auto& c) {
                                       return c.var() == k;
                                   });
            const mpq& k_coeff_in_e = it->coeff();
            bool is_one = k_coeff_in_e.is_one();
            SASSERT(is_one || k_coeff_in_e.is_minus_one());
            if (is_one)
                coeff = -coeff;

            for (const auto& p : e_row) {
                unsigned j = p.var();
                if (j == k)
                    continue;
                m_indexed_work_vector.add_value_at_index(j, p.coeff() * coeff);
                // do we need to add j to the queue?
                if (!is_fresh_var(j) && !m_indexed_work_vector[j].is_zero() &&
                    can_substitute(j))
                    q.push(j);
            }
            m_c += coeff * e.m_c;
            
            m_tmp_l += coeff * l_term_from_row(sub_index(k)); // improve later
            TRACE("dioph_eq", tout << "after subs k:" << k << "\n";
                  print_term_o(create_term_from_ind_c(), tout) << std::endl;
                  tout << "m_tmp_l:{"; print_lar_term_L(m_tmp_l, tout);
                  tout << "}, opened:"; print_ml(m_tmp_l, tout) << std::endl;);
        }

        lar_term l_term_from_row(unsigned k) const {
            lar_term ret;
            for (const auto & p: m_l_matrix.m_rows[k])
                ret.add_monomial(p.coeff(), p.var());

            return ret;
        }

        term_o create_term_from_l(const lar_term& l) {
            term_o ret;
            for (const auto& p : l) {
                const auto& t = lra.get_term(local_to_lar_solver(p.j()));
                ret.add_monomial(-mpq(1), p.j());
                for (const auto& q : t) {
                    ret.add_monomial(p.coeff() * q.coeff(), q.j());
                }
            }
            return ret;
        }

        bool is_fixed(unsigned j) const {
            return lra.column_is_fixed(j);
        }

        template <typename T>
        term_o fix_vars(const T& t) const {
            term_o ret;
            for (const auto& p : t) {
                if (is_fixed(p.var())) {
                    ret.c() += p.coeff() * this->lra.get_lower_bound(p.var()).x;
                } else {
                    ret.add_monomial(p.coeff(), p.var());
                }
            }
            return ret;
        }
        const entry& entry_for_subs(unsigned k) const {
            return m_entries[m_k2s[k]];
        }

        entry& entry_for_subs(unsigned k) {
            return m_entries[m_k2s[k]];
        }

        const unsigned sub_index(unsigned k) const {
            return m_k2s[k];
        }

        template <typename T>
        T pop_front(std::queue<T>& q) const {
            T value = q.front();
            q.pop();
            return value;
        }

        void subs_indexed_vector_with_S(std::queue<unsigned>& q) {
            while (!q.empty())
                subs_front_in_indexed_vector(q);
        }

        lia_move tighten_terms_with_S() {
            for (unsigned j = 0; j < lra.column_count(); j++) {
                if (!lra.column_has_term(j) || lra.column_is_free(j) ||
                    is_fixed(j) || !lia.column_is_int(j))
                    continue;

                if (tighten_bounds_for_term_column(j))
                    return lia_move::conflict;
            }

            return lia_move::undef;
        }

        std::ostream& print_queue(std::queue<unsigned> q, std::ostream& out) {
            out << "qu: ";
            while (!q.empty()) {
                out << q.front() << " ";
                q.pop();
            }
            out << std::endl;
            return out;
        }

        term_o create_term_from_ind_c() {
            term_o t;
            for (const auto& p : m_indexed_work_vector) {
                t.add_monomial(p.coeff(), p.var());
            }
            t.c() = m_c;
            return t;
        }

        void fill_indexed_work_vector_from_term(const lar_term& lar_t) {
            m_indexed_work_vector.clear();
            m_indexed_work_vector.resize(m_e_matrix.column_count());
            m_c = 0;
            m_tmp_l = lar_term();
            for (const auto& p : lar_t) {
                SASSERT(p.coeff().is_int());
                if (is_fixed(p.j()))
                    m_c += p.coeff() * lia.lower_bound(p.j()).x;
                else
                    m_indexed_work_vector.set_value(p.coeff(),
                                                    lar_solver_to_local(p.j()));
            }
        }
        unsigned lar_solver_to_local(unsigned j) const {
            return m_var_register.external_to_local(j);
        }
        // j is the index of the column representing a term
        // return true if a conflict was found
        bool tighten_bounds_for_term_column(unsigned j) {
            term_o term_to_tighten = lra.get_term(j);  // copy the term aside
            if (!all_vars_are_int(term_to_tighten))
                return false;
            std::queue<unsigned> q;
            for (const auto& p : term_to_tighten) {
                if (!lra.column_is_fixed(p.j()) &&
                    can_substitute(lar_solver_to_local(p.j())))
                    q.push(lar_solver_to_local(p.j()));
            }
            if (q.empty()) {
                return false;
            }
            TRACE("dioph_eq", tout << "j:" << j << ", t: ";
                  print_lar_term_L(term_to_tighten, tout) << std::endl;);
            fill_indexed_work_vector_from_term(term_to_tighten);
            TRACE("dioph_eq", tout << "t orig:";
                  print_lar_term_L(term_to_tighten, tout) << std::endl;
                  tout << "from ind:";
                  print_term_o(create_term_from_ind_c(), tout) << std::endl;
                  tout << "m_tmp_l:";
                  print_lar_term_L(m_tmp_l, tout) << std::endl;);
            subs_indexed_vector_with_S(q);

            TRACE("dioph_eq", tout << "after subs\n";
                  print_term_o(create_term_from_ind_c(), tout) << std::endl;
                  tout << "term_to_tighten:";
                  print_lar_term_L(term_to_tighten, tout) << std::endl;
                  tout << "m_tmp_l:"; print_lar_term_L(m_tmp_l, tout) << std::endl;
                  tout << "open_ml:";
                  print_lar_term_L(open_ml(m_tmp_l), tout) << std::endl;
                  tout << "term_to_tighten + open_ml:";
                  print_term_o(term_to_tighten + open_ml(m_tmp_l), tout)
                  << std::endl;
                  tout << "ls:"; print_term_o(fix_vars(term_to_tighten + open_ml(m_tmp_l)),tout) << std::endl;
                  tout << "rs:"; print_term_o(term_to_lar_solver(remove_fresh_vars(create_term_from_ind_c())), tout ) << std::endl;

                );
            SASSERT(
                fix_vars(term_to_tighten + open_ml(m_tmp_l)) ==
                term_to_lar_solver(remove_fresh_vars(create_term_from_ind_c())));
            mpq g = gcd_of_coeffs(m_indexed_work_vector);
            TRACE("dioph_eq", tout << "after process_q_with_S\nt:";
                  print_term_o(create_term_from_ind_c(), tout) << std::endl;
                  tout << "g:" << g << std::endl;
                  /*tout << "dep:"; print_dep(tout, m_tmp_l) << std::endl;*/);

            if (g.is_one())
                return false;
            if (g.is_zero()) {
                handle_constant_term(j);
                return !m_infeas_explanation.empty();
            }
            // g is not trivial, trying to tighten the bounds
            return tighten_bounds_for_non_trivial_gcd(g, j, true) ||
                   tighten_bounds_for_non_trivial_gcd(g, j, false);
        }

        void get_expl_from_meta_term(const lar_term& t, explanation& ex) {
            u_dependency* dep = explain_fixed_in_meta_term(t);
            for (constraint_index ci : lra.flatten(dep))
                ex.push_back(ci);
        }

        void handle_constant_term(unsigned j) {
            if (m_c.is_zero()) {
                return;
            }
            mpq rs;
            bool is_strict;
            u_dependency* b_dep = nullptr;
            if (lra.has_upper_bound(j, b_dep, rs, is_strict)) {
                if (m_c > rs || (is_strict && m_c == rs)) {
                    u_dependency* dep =
                        lra.mk_join(explain_fixed(lra.get_term(j)),
                                    explain_fixed_in_meta_term(m_tmp_l));
                    dep = lra.mk_join(
                        dep, lra.get_bound_constraint_witnesses_for_column(j));
                    for (constraint_index ci : lra.flatten(dep)) {
                        m_infeas_explanation.push_back(ci);
                    }
                    return;
                }
            }
            if (lra.has_lower_bound(j, b_dep, rs, is_strict)) {
                if (m_c < rs || (is_strict && m_c == rs)) {
                    u_dependency* dep =
                        lra.mk_join(explain_fixed(lra.get_term(j)),
                                    explain_fixed_in_meta_term(m_tmp_l));
                    dep = lra.mk_join(
                        dep, lra.get_bound_constraint_witnesses_for_column(j));
                    for (constraint_index ci : lra.flatten(dep)) {
                        m_infeas_explanation.push_back(ci);
                    }
                }
            }
        }

        // m_indexed_work_vector contains the coefficients of the term
        // m_c contains the constant term
        // m_tmp_l is the linear combination of the equations that removes the
        // substituted variables.
        // returns true iff the conflict is found
        bool tighten_bounds_for_non_trivial_gcd(const mpq& g, unsigned j,
                                                bool is_upper) {
            mpq rs;
            bool is_strict;
            u_dependency* b_dep = nullptr;
            SASSERT(!g.is_zero());

            if (lra.has_bound_of_type(j, b_dep, rs, is_strict, is_upper)) {
                TRACE("dioph_eq", tout << "current upper bound for x:" << j << ":"
                                       << rs << std::endl;);
                rs = (rs - m_c) / g;
                TRACE("dioph_eq", tout << "(rs - m_c) / g:" << rs << std::endl;);
                if (!rs.is_int()) {
                    if (tighten_bound_kind(g, j, rs, is_upper, b_dep))
                        return true;
                }
            }
            return false;
        }

        // returns true only on a conflict
        bool tighten_bound_kind(const mpq& g, unsigned j, const mpq& ub, bool upper,
                                u_dependency* prev_dep) {
            // ub = (upper_bound(j) - m_c)/g.
            // we have x[j] = t = g*t_+ m_c <= upper_bound(j), then
            // t_ <= floor((upper_bound(j) - m_c)/g) = floor(ub)
            //
            // so xj = g*t_+m_c <= g*floor(ub) + m_c is new upper bound
            // <= can be replaced with >= for lower bounds, with ceil instead of
            // floor
            mpq bound = g * (upper ? floor(ub) : ceil(ub)) + m_c;
            TRACE("dioph_eq", tout << "is upper:" << upper << std::endl;
                  tout << "new " << (upper ? "upper" : "lower")
                       << " bound:" << bound << std::endl;);

            SASSERT((upper && bound < lra.get_upper_bound(j).x) ||
                    (!upper && bound > lra.get_lower_bound(j).x));
            lconstraint_kind kind =
                upper ? lconstraint_kind::LE : lconstraint_kind::GE;
            u_dependency* dep = prev_dep;
            dep = lra.mk_join(dep, explain_fixed_in_meta_term(m_tmp_l));
            u_dependency* j_bound_dep = upper
                                            ? lra.get_column_upper_bound_witness(j)
                                            : lra.get_column_lower_bound_witness(j);
            dep = lra.mk_join(dep, j_bound_dep);
            dep = lra.mk_join(dep, explain_fixed(lra.get_term(j)));
            dep =
                lra.mk_join(dep, lra.get_bound_constraint_witnesses_for_column(j));
            TRACE("dioph_eq", tout << "jterm:";
                  print_lar_term_L(lra.get_term(j), tout) << "\ndep:";
                  print_dep(tout, dep) << std::endl;);
            lra.update_column_type_and_bound(j, kind, bound, dep);
            lp_status st = lra.find_feasible_solution();
            if ((int)st >= (int)lp::lp_status::FEASIBLE) {
                return false;
            }
            if (st == lp_status::CANCELLED) return false;
            lra.get_infeasibility_explanation(m_infeas_explanation);
            return true;            
        }

        template <typename T> u_dependency* explain_fixed_in_meta_term (const T& t) {
            return explain_fixed(open_ml(t));
        }

        u_dependency* explain_fixed(const lar_term& t) {
            u_dependency* dep = nullptr;
            for (const auto& p : t) {
                if (is_fixed(p.j())) {
                    u_dependency* bound_dep =
                        lra.get_bound_constraint_witnesses_for_column(p.j());
                    dep = lra.mk_join(dep, bound_dep);
                }
            }
            return dep;
        }

        lia_move process_f() {
            while (m_f.size()) {
                if (!normalize_by_gcd()) {
                    if (m_report_branch) {
                        lra.stats().m_dio_cut_from_proofs++;
                        m_report_branch = false;
                        return lia_move::branch;
                    } else {
                        lra.stats().m_dio_normalize_conflicts++;
                    }
                    return lia_move::conflict;
                }
                rewrite_eqs();
                if (m_conflict_index != UINT_MAX) {
                    lra.stats().m_dio_rewrite_conflicts++;
                    return lia_move::conflict;
                }
            }
            return lia_move::undef;
        }

        lia_move process_f_and_tighten_terms() {
            lia_move ret = process_f();
            if (ret != lia_move::undef) 
                return ret;
            TRACE("dioph_eq", print_S(tout););
            ret = tighten_terms_with_S();
            if (ret == lia_move::conflict) {
                lra.stats().m_dio_tighten_conflicts++;
                return lia_move::conflict;
            }
            return lia_move::undef;
        }

        void collect_evidence() {
            lra.get_infeasibility_explanation(m_infeas_explanation);
            for (const auto& p : m_infeas_explanation) {
                m_explanation_of_branches.push_back(p.ci());
            }
        }
        
        // returns true if the left and the right branches were explored
        void undo_explored_branches() {
            TRACE("dio_br", tout << "m_branch_stack.size():" << m_branch_stack.size() <<  std::endl;);            
            while (m_branch_stack.size() && m_branch_stack.back().m_fully_explored) {
                m_branch_stack.pop_back();
                lra_pop();
            } 
            TRACE("dio_br", tout << "after pop:m_branch_stack.size():" << m_branch_stack.size() <<  std::endl;);                        
        }

        lia_move check_fixing(unsigned j) const {
            // do not change entry here
            unsigned ei = m_k2s[j]; // entry index
            mpq g  = mpq(0); // gcd
            mpq c = m_entries[ei].m_c;
            for (const auto& p : m_e_matrix.m_rows[m_k2s[j]]) {
                if (p.var() == j) {
                    const mpq & j_coeff = p.coeff();
                    SASSERT(j_coeff.is_one() || j_coeff.is_minus_one());
                    c += j_coeff * lra.get_lower_bound(local_to_lar_solver(j)).x;
                    TRACE("dio_br", tout << "the value of the vixed var is:" <<  lra.get_lower_bound(local_to_lar_solver(j)).x<<", m_entries[" << ei << "].m_c:" << m_entries[ei].m_c << ", new free coeff c:" << c << std::endl;);
                    continue;
                } 
                if (g.is_zero()) {
                    g = abs(p.coeff());                    
                } else {
                    g = gcd(g, p.coeff());
                }
                if (g.is_one()) return lia_move::undef;                
            }
            if (!(c/g).is_int()) {
                return lia_move::conflict;
            }
            return lia_move::undef;
        }
       // here j is a local variable
        lia_move fix_var(unsigned j) {
            SASSERT(is_fixed(local_to_lar_solver(j)));
            /* 
            We only can get a conflict when j is substituted, and the entry m_k2s[j], the entry defining the substitution  becomes infeaseable, that is the gcd of the monomial coeffitients does not dive the free coefficient. In other cases the gcd of the monomials will remain to be 1.
            */
            if (can_substitute(j)) {
                TRACE("dio_br",
                      tout << "fixed j:" << j <<", was substited by "; print_entry(m_k2s[j], tout););
                if (check_fixing(j) == lia_move::conflict) {
                    for (auto ci : lra.flatten(explain_fixed_in_meta_term(m_l_matrix.m_rows[m_k2s[j]]))) {
                        m_explanation_of_branches.push_back(ci);
                    }
                    return lia_move::conflict;
                }
            } 
            return lia_move::undef;
        }

        void undo_branching() {
            while (m_lra_level --) {
                lra.pop();
            }
            lra.find_feasible_solution();
            SASSERT(lra.get_status() == lp_status::CANCELLED || lra.is_feasible());
        }
        // Returns true if a branch is created, and false if not.
        // The latter case can happen if we have a sat.
        bool push_branch() {
            branch br = create_branch();
            if (br.m_j == UINT_MAX) 
                return false;
            m_branch_stack.push_back(br);
            lra.stats().m_dio_branching_depth = std::max(lra.stats().m_dio_branching_depth, (unsigned)m_branch_stack.size());
            return true;
        }

        lia_move add_var_bound_for_branch(const branch& b) {            
            if (b.m_left) {
                lra.add_var_bound(b.m_j, lconstraint_kind::LE, b.m_rs);
             } else {
                lra.add_var_bound(b.m_j, lconstraint_kind::GE, b.m_rs + mpq(1));
            }
            TRACE("dio_br", lra.print_column_info(b.m_j, tout) <<"add bound" << std::endl;);
            if (lra.column_is_fixed(b.m_j)) {
                unsigned local_bj;
                if (! m_var_register.external_is_used(b.m_j, local_bj))
                    return lia_move::undef;

                if (fix_var(local_bj) == lia_move::conflict) {
                   TRACE("dio_br", tout << "conflict in fix_var" << std::endl;) ;
                   return lia_move::conflict;
                }
            }
            return lia_move::undef;
        }

        unsigned m_lra_level = 0;
        void lra_push() {
            m_lra_level++;
            lra.push();
            SASSERT(m_lra_level == m_branch_stack.size());
        }
        void lra_pop() {
            m_lra_level--;
            SASSERT(m_lra_level != UINT_MAX);
            lra.pop();
            lra.find_feasible_solution();            
            SASSERT(lra.get_status() == lp_status::CANCELLED || lra.is_feasible());
        }

        void transfer_explanations_from_closed_branches() {
            m_infeas_explanation.clear();
            for (auto ci : m_explanation_of_branches) {
                if (this->lra.constraints().valid_index(ci))
                    m_infeas_explanation.push_back(ci);
            }
            
        }

        lia_move branching_on_undef() {
            m_explanation_of_branches.clear();
            bool need_create_branch = true;
            m_number_of_iterations = 0;
            while (++m_number_of_iterations < m_max_number_of_iterations) {
                lra.stats().m_dio_branch_iterations++;
                if (need_create_branch) {
                    if (!push_branch()) {
                        undo_branching();
                        lra.stats().m_dio_branching_sats++;
                        return lia_move::sat;
                    }
                    need_create_branch = false;
                }
                lra_push();  // exploring a new branch

                if (add_var_bound_for_branch(m_branch_stack.back()) == lia_move::conflict) {
                    undo_explored_branches();
                    if (m_branch_stack.size() == 0) {
                        lra.stats().m_dio_branching_infeasibles++;
                        transfer_explanations_from_closed_branches();
                        return lia_move::conflict;
                    }
                    need_create_branch = false;
                    m_branch_stack.back().flip();
                    lra_pop();
                    continue;                    
                }
                auto st = lra.find_feasible_solution();
                TRACE("dio_br", tout << "st:" << lp_status_to_string(st) << std::endl;);
                if ((int)st >= (int)(lp_status::FEASIBLE)) {
                    // have a feasible solution
                    unsigned n_of_ii = get_number_of_int_inf();
                    TRACE("dio_br", tout << "n_of_ii:" << n_of_ii << "\n";);
                    if (n_of_ii == 0) {
                        undo_branching();
                        lra.stats().m_dio_branching_sats++;                        
                        return lia_move::sat;
                    }
                    // got to create a new branch
                    update_branch_stats(m_branch_stack.back(), n_of_ii);
                    need_create_branch = true;
                } else {  
                    if (st == lp_status::CANCELLED) return lia_move::undef;
                    collect_evidence();
                    undo_explored_branches();
                    if (m_branch_stack.size() == 0) {
                           lra.stats().m_dio_branching_infeasibles++;
                           transfer_explanations_from_closed_branches();
                           return lia_move::conflict;
                    }
                    TRACE("dio_br", tout << lp_status_to_string(lra.get_status()) << std::endl;
                          tout << "explanation:\n"; lra.print_expl(tout, m_infeas_explanation););
                    
                    need_create_branch = false;
                    lra_pop();
                    m_branch_stack.back().flip();
                }
            }
            undo_branching();
            return lia_move::undef;
        }

        unsigned get_number_of_int_inf() const {
            return (unsigned) std::count_if(
                lra.r_basis().begin(), lra.r_basis().end(),
                [this](unsigned j) {
                    return lia.column_is_int_inf(j);
                });
        }

        double get_branch_score(unsigned j) {
            if (j >= m_branch_stats.size())
                m_branch_stats.resize(j + 1);
            return m_branch_stats[j].score();
        }

        void update_branch_stats(const branch& b, unsigned n_of_ii) {
            // Ensure the branch stats vector is large enough
            if (b.m_j >= m_branch_stats.size()) {
                m_branch_stats.resize(b.m_j + 1);
            }

            if (b.m_left) {
                m_branch_stats[b.m_j].m_ii_after_left.push_back(n_of_ii);
            } else {
                m_branch_stats[b.m_j].m_ii_after_right.push_back(n_of_ii);
            }
        }
                

        branch create_branch() {
            unsigned bj = UINT_MAX;
            double score = std::numeric_limits<double>::infinity();
            // looking for the minimal score
            unsigned n = 0;
            for (unsigned j : lra.r_basis()) {
                if (!lia.column_is_int_inf(j))
                    continue;
                double sc = get_branch_score(j);
                if (sc < score ||
                    (sc == score && lra.settings().random_next() % (++n) == 0)) {
                    score = sc;
                    bj = j;
                }
            }
            branch br;
            if (bj == UINT_MAX) { // it the case when we cannot create a branch
                SASSERT(
                    lra.settings().get_cancel_flag() ||
                    (lra.is_feasible() && [&]() {
                        for (unsigned j = 0; j < lra.column_count(); ++j) {
                            if (lia.column_is_int_inf(j)) {
                                return false;
                            }
                        }
                        return true;
                    }()));
                return br; // to signal that we have no ii variables 
            }
            
            br.m_j = bj;
            br.m_left = (lra.settings().random_next() % 2 == 0);
            br.m_rs = floor(lra.get_column_value(bj).x);

            TRACE("dio_br", tout << "score:" << score << "; br.m_j:" << br.m_j << ","
                                 << (br.m_left ? "left" : "right") << ", br.m_rs:" << br.m_rs << std::endl;);
            return br;
        }

        bool columns_to_terms_is_correct() const {
            std::unordered_map<unsigned, std::unordered_set<unsigned>> c2t;
            for (unsigned k = 0; k < lra.terms().size(); k ++ ) {
                const lar_term* t = lra.terms()[k];
                if (!all_vars_are_int(*t)) continue;
                SASSERT(t->j() != UINT_MAX);
                for (const auto& p: (*t).ext_coeffs()) {
                    unsigned j = p.var();
                    auto it = c2t.find(j);
                    if (it == c2t.end()) {
                        std::unordered_set<unsigned> s;
                        s.insert(t->j());
                        c2t[j] = s;
                    } else {
                        it->second.insert(t->j());                        
                    }

                    
                }
            }
            for (const auto & p : c2t) {
                unsigned j = p.first;
                const auto it = m_columns_to_terms.find(j);
                if (it == m_columns_to_terms.end()) {
                    TRACE("dioph_eq", tout << "column j" << j  << " is not registered" << std::endl;
                          tout << "the column belongs to the the following terms:";
                          for (unsigned tj : p.second) {
                              tout << " " << tj;
                          }
                          tout << std::endl;
                        );
                    
                    return false;
                } 
                if (it->second != p.second) {                    
                    return false;
                }
            }
            // reverse inclusion
            for (const auto & p : m_columns_to_terms) {
                unsigned j = p.first;
                const auto it = c2t.find(j);
                if (it == c2t.end()) {
                    TRACE("dioph_eq", tout << "should not be registered j " << j << std::endl;
                    lra.print_terms(tout););
                    return false;
                } 
                if (it->second != p.second) {
                    return false;
                }
            }
            return true;
        }
        bool is_in_sync() const {
            unsigned n_local_columns = m_e_matrix.column_count();
            for (unsigned j = 0; j < n_local_columns; j++) {
                unsigned external_j = m_var_register.local_to_external(j);
                if (external_j == UINT_MAX) continue;
                if (external_j >=  lra.column_count())
                    return false;
            }
            
            return columns_to_terms_is_correct();
        }

       public:
        lia_move check() {
            lra.stats().m_dio_calls++;
            TRACE("dioph_eq", tout << lra.stats().m_dio_calls << std::endl;);
            init();
            lia_move ret = process_f_and_tighten_terms();
            if (ret == lia_move::branch || ret == lia_move::conflict)
                return ret;
            SASSERT(ret == lia_move::undef);
            ret = branching_on_undef();
            if (ret == lia_move::sat || ret == lia_move::conflict) {
                return ret;
            }
            SASSERT(ret == lia_move::undef);
            m_max_number_of_iterations = std::max((unsigned)5, (unsigned)m_max_number_of_iterations/2);
            
            return lia_move::undef;
        }

       private:
        void add_operator(lar_term& t, const mpq& k, const lar_term& l) {
            for (const auto& p : l) {
                t.add_monomial(k * p.coeff(), p.j());
            }
        }

        std::tuple<mpq, unsigned, int> find_minimal_abs_coeff(unsigned ei) const {
            bool first = true;
            mpq ahk;
            unsigned k;
            int k_sign;
            mpq t;
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                t = abs(p.coeff());
                if (first || t < ahk ||
                    (t == ahk && p.var() < k)) {  // the last condition is for debug
                    ahk = t;
                    k_sign = p.coeff().is_pos() ? 1 : -1;
                    k = p.var();
                    first = false;
                    if (ahk.is_one())
                        break;
                }
            }

            return std::make_tuple(ahk, k, k_sign);
        }

        term_o get_term_to_subst(const term_o& eh, unsigned k, int k_sign) {
            term_o t;
            for (const auto& p : eh) {
                if (p.j() == k)
                    continue;
                t.add_monomial(-k_sign * p.coeff(), p.j());
            }
            t.c() = -k_sign * eh.c();
            TRACE("dioph_eq", tout << "subst_term:";
                  print_term_o(t, tout) << std::endl;);
            return t;
        }

        std::ostream& print_e_row(unsigned i, std::ostream& out) {
            return print_term_o(get_term_from_entry(i), out);
        }
        bool j_sign_is_correct(unsigned ei, unsigned j, int j_sign) {
            const auto& row = m_e_matrix.m_rows[ei];
            auto it = std::find_if (row.begin(), row.end(), [j](const auto& p) {return p.var() == j;} );
            if (it == row.end()) return false;
            return it->coeff() == mpq(1)&& j_sign == 1 ||
                   it->coeff() == mpq(-1) && j_sign == -1;
        }
        // j is the variable to eliminate, it appears in row ei of m_e_matrix with
        // a coefficient equal to j_sign which is +-1 
        void eliminate_var_in_f(unsigned ei, unsigned j, int j_sign) {
            const auto & e = m_entries[ei];
            SASSERT(j_sign_is_correct(ei, j, j_sign));
            TRACE("dioph_eq", tout << "eliminate var:" << j << " by using:";
                  print_entry(ei, tout) << std::endl;);
            auto& column = m_e_matrix.m_columns[j];
            auto it =
                std::find_if(column.begin(), column.end(),
                             [ei](const auto& cell) {
                                 return cell.var() == ei;
                             });
            unsigned pivot_col_cell_index = (unsigned) std::distance(column.begin(), it);
            if (pivot_col_cell_index != 0) {
                // swap the pivot column cell with the head cell
                auto c = column[0];
                column[0] = column[pivot_col_cell_index];
                column[pivot_col_cell_index] = c;

                m_e_matrix.m_rows[ei][column[0].offset()].offset() = 0;
                m_e_matrix.m_rows[c.var()][c.offset()].offset() =
                    pivot_col_cell_index;
            }

            unsigned cell_to_process = column.size() - 1;
            while (cell_to_process > 0) {
                auto& c = column[cell_to_process];
                if (m_entries[c.var()].m_entry_status != entry_status::F) {
                    cell_to_process--;
                    continue;
                }

                SASSERT(c.var() != ei && entry_invariant(c.var()));
                mpq coeff = m_e_matrix.get_val(c);
                unsigned i = c.var();
                TRACE("dioph_eq", tout << "before pivot entry :";
                      print_entry(i, tout) << std::endl;);
                m_entries[i].m_c -= j_sign * coeff * e.m_c;
                m_e_matrix.pivot_row_to_row_given_cell_with_sign(ei, c, j, j_sign);
                //m_entries[i].m_l -= j_sign * coeff * e.m_l;
                m_l_matrix.add_rows( -j_sign*coeff, ei, i);
                TRACE("dioph_eq", tout << "after pivoting c_row:";
                      print_entry(i, tout););
                CTRACE(
                    "dioph_eq", !entry_invariant(i), tout << "invariant delta:"; {
                        print_term_o(get_term_from_entry(ei) -
                                     fix_vars(open_ml(m_l_matrix.m_rows[ei])),
                                     tout)
                            << std::endl;
                    });
                SASSERT(entry_invariant(i));
                cell_to_process--;
            }
        }

        term_o term_to_lar_solver(const term_o& eterm) const {
            term_o ret;
            for (const auto& p : eterm) {
                ret.add_monomial(p.coeff(), local_to_lar_solver(p.var()));
            }
            ret.c() = eterm.c();
            return ret;
        }

        bool entry_invariant(unsigned ei) const {
            for (const auto &p: m_e_matrix.m_rows[ei]) {
                if (!p.coeff().is_int()) {
                    return false;
                }
            }
            
            bool ret =
                term_to_lar_solver(remove_fresh_vars(get_term_from_entry(ei))) ==
                fix_vars(open_ml(m_l_matrix.m_rows[ei]));

            CTRACE( "dioph_deb_eq", !ret,
                    {
                        tout << "get_term_from_entry(" << ei << "):";
                        print_term_o(get_term_from_entry(ei), tout) << std::endl;
                        tout << "ls:";
                        print_term_o(remove_fresh_vars(get_term_from_entry(ei)), tout)
                            << std::endl;
                        tout << "e.m_l:"; print_lar_term_L(l_term_from_row(ei), tout) << std::endl;
                        tout << "open_ml(e.m_l):";
                        print_lar_term_L(open_ml(l_term_from_row(ei)), tout) << std::endl;
                        tout << "rs:";
                        print_term_o(fix_vars(open_ml(m_l_matrix.m_rows[ei])), tout) << std::endl;
                    }
                );
            return ret;
        }

        term_o remove_fresh_vars(const term_o& tt) const {
            term_o t = tt;
            std::queue<unsigned> q;
            for (const auto& p : t) {
                if (is_fresh_var(p.j())) {
                    q.push(p.j());
                }
            }
            while (!q.empty()) {
                unsigned xt = pop_front(q);
                term_o fresh_t = get_term_from_entry(m_fresh_definitions[xt].m_ei);
                SASSERT(fresh_t.get_coeff(xt).is_minus_one());
                fresh_t.erase_var(xt);
                if (!t.contains(xt))
                    continue;
                mpq xt_coeff = t.get_coeff(xt);
                t.erase_var(xt);
                t += xt_coeff * fresh_t;
                for (const auto& p : t) {
                    if (is_fresh_var(p.j())) {
                        q.push(p.j());
                    }
                }
            }
            return t;
        }

        std::ostream& print_ml(const lar_term& ml, std::ostream& out) {
            term_o opened_ml = open_ml(ml);
            return print_lar_term_L(opened_ml, out);
        }

        template <typename T> term_o open_ml(const T& ml) const {
            term_o r;
            for (const auto& p : ml) {
                r += p.coeff() * (lra.get_term(p.var()) - lar_term(p.var()));
            }
            return r;
        }

        void make_space_in_work_vector(unsigned j) {
            if (j >= m_indexed_work_vector.data_size())
                m_indexed_work_vector.resize(j + 1);
        }

        void open_l_term_to_work_vector(unsigned ei, mpq& c) {
            m_indexed_work_vector.clear();
            for (const auto & p: m_l_matrix.m_rows[ei]) {
                const lar_term& t = lra.get_term(p.var());
                for (const auto & q: t.ext_coeffs()) {
                    if (is_fixed(q.var())) {
                        c += p.coeff()*q.coeff()*lia.lower_bound(q.var()).x;
                    } else { 
                        make_space_in_work_vector(q.var());
                        m_indexed_work_vector.add_value_at_index(q.var(), p.coeff() * q.coeff());
                    }
                }
            } 
        }
        
        // it clears the row, and puts the term in the work vector
        void move_row_to_work_vector(unsigned ei) {
            m_indexed_work_vector.clear();
            m_indexed_work_vector.resize(m_e_matrix.column_count());
            auto& row = m_e_matrix.m_rows[ei];
            for (const auto& cell : row)
                m_indexed_work_vector.set_value(cell.coeff(), cell.var());
            clear_e_row(ei);
        }

        // k is the variable to substitute
        void fresh_var_step(unsigned h, unsigned k, const mpq& ahk) {
            move_row_to_work_vector(h);  // it clears the row, and puts the term in the work vector
            
            // step 7 from the paper
            // xt is the fresh variable
            unsigned xt = add_var(UINT_MAX);
            unsigned fresh_row = m_e_matrix.row_count();
            m_e_matrix.add_row();  // for the fresh variable definition
            while (xt >= m_e_matrix.column_count())
                m_e_matrix.add_column();
            // Add a new row for the fresh variable definition
            /* Let eh = sum(ai*xi) + c. For each i != k, let ai = qi*ahk + ri, and
               let c = c_q * ahk + c_r. eh = ahk*(x_k + sum{qi*xi|i != k} + c_q) +
               sum {ri*xi|i!= k} + c_r. Then -xt + x_k + sum {qi*x_i)| i != k} + c_q
               will be the fresh row eh = ahk*xt +  sum {ri*x_i | i != k} + c_r  is
               the row m_e_matrix[e.m_row_index]
            */
            auto& e = m_entries[h];
            mpq q, r;
            q = machine_div_rem(e.m_c, ahk, r);
            e.m_c = r;
            m_e_matrix.add_new_element(h, xt, ahk);

            m_entries.push_back({q, entry_status::NO_S_NO_F});
            m_e_matrix.add_new_element(fresh_row, xt, -mpq(1));
            m_e_matrix.add_new_element(fresh_row, k, mpq(1));
            for (unsigned i : m_indexed_work_vector.m_index) {
                mpq ai = m_indexed_work_vector[i];
                if (i == k)
                    continue;
                q = machine_div_rem(ai, ahk, r);
                if (!r.is_zero())
                    m_e_matrix.add_new_element(h, i, r);
                if (!q.is_zero())
                    m_e_matrix.add_new_element(fresh_row, i, q);
            }

            m_l_matrix.add_row();
            
            m_k2s.resize(k + 1, -1);
            m_k2s[k] = fresh_row;
            fresh_definition fd(-1, -1);
                
            m_fresh_definitions.resize(xt + 1, fd);
            m_fresh_definitions[xt] = fresh_definition(fresh_row, h);
            TRACE("dioph_eq", tout << "changed entry:";
                  print_entry(h, tout) << std::endl;
                  tout << "added entry for fresh var:\n";
                  print_entry(fresh_row, tout) << std::endl;);
            SASSERT(entry_invariant(h));
            SASSERT(entry_invariant(fresh_row));
            eliminate_var_in_f(fresh_row, k, 1);
        }

        std::ostream& print_entry(unsigned i, std::ostream& out,
                                  bool print_dep = true) {
            out << "m_entries[" << i << "]:";
            return print_entry(i, m_entries[i], out, print_dep);
        }

        std::ostream& print_entry(unsigned ei, const entry& e, std::ostream& out,
                                  bool need_print_dep = true) {
            out << "{\n";
            print_term_o(get_term_from_entry(ei), out << "\tm_e:") << ",\n";
            // out << "\tstatus:" << (int)e.m_entry_status;
            if (need_print_dep) {
                out << "\tm_l:{";
                print_lar_term_L(l_term_from_row(ei), out) << "}, ";
                print_ml(l_term_from_row(ei), out) << std::endl;
                out << "expl of fixed in m_l:{\n";
                print_dep(out, explain_fixed_in_meta_term(l_term_from_row(ei)));
                out << "}\n";
            }
            switch (e.m_entry_status) {
                case entry_status::F:
                    out << "in F\n";
                    break;
                case entry_status::S:
                    out << "in S\n";
                    break;
                default:
                    out << "NOSF\n";
            }
            out << "}\n";
            return out;
        }

        void move_entry_from_s_to_f(unsigned ei) {
            if (m_entries[ei].m_entry_status == entry_status::F) return;
            m_entries[ei].m_entry_status = entry_status::F;
            for (unsigned l = 0; l < m_k2s.size(); l++) {
                if (m_k2s[l] == ei) {
                    m_k2s[l] = -1;
                }
            }
            m_s.remove(ei);
            m_f.push_back(ei);            
        }

        // k is the index of the variable that is being substituted
        void move_entry_from_f_to_s(unsigned k, unsigned h) {
            SASSERT(m_entries[h].m_entry_status == entry_status::F);
            m_entries[h].m_entry_status = entry_status::S;
            if (k >= m_k2s.size()) {  // k is a fresh variable
                m_k2s.resize(k + 1, -1);
            }
            m_s.push_back(h);
            TRACE("dioph_eq", tout << "removed " << h << "th entry from F" << std::endl;);
            m_k2s[k] = h;
            m_f.remove(h);
        }

        // this is the step 6 or 7 of the algorithm
        void rewrite_eqs() {
            unsigned h = -1;
            auto it = m_f.begin();
            while (it != m_f.end()) {
                if (m_e_matrix.m_rows[*it].size() == 0) {
                    if (m_entries[*it].m_c.is_zero()) {
                        it = m_f.erase(it);
                        continue;
                    } else {
                        m_conflict_index = *it;
                        return;
                    }
                }
                h = *it;
                break;
            }
            if (h == UINT_MAX)
                return;
            auto [ahk, k, k_sign] = find_minimal_abs_coeff(h);
            TRACE("dioph_eq", tout << "eh:"; print_entry(h, tout);
                  tout << "ahk:" << ahk << ", k:" << k << ", k_sign:" << k_sign
                       << std::endl;);

            if (ahk.is_one()) {
                TRACE("dioph_eq", tout << "push to S:\n"; print_entry(h, tout););
                move_entry_from_f_to_s(k, h);
                eliminate_var_in_f(h, k, k_sign);
            } else {
                fresh_var_step(h, k, ahk * mpq(k_sign));
            }
        }

       public:
        void explain(explanation& ex) {
            if (m_conflict_index == UINT_MAX) {
                for (auto ci : m_infeas_explanation) {
                    ex.push_back(ci.ci());
                }
                TRACE("dioph_eq", lra.print_expl(tout, ex););
                return;
            }
            SASSERT(ex.empty());
            TRACE("dioph_eq", tout << "conflict:";
                  print_entry(m_conflict_index, tout, true) << std::endl;);
            for (auto ci : lra.flatten(explain_fixed_in_meta_term(m_l_matrix.m_rows[m_conflict_index]))) {
                ex.push_back(ci);
            }
            TRACE("dioph_eq", lra.print_expl(tout, ex););
        }

        bool is_fresh_var(unsigned j) const {
            return m_var_register.local_to_external(j) == UINT_MAX;
        }
        bool can_substitute(unsigned k) {
            return k < m_k2s.size() && m_k2s[k] != UINT_MAX;
        }
    };
    // Constructor definition
    dioph_eq::dioph_eq(int_solver& lia) {
        m_imp = alloc(imp, lia, lia.lra);
    }
    dioph_eq::~dioph_eq() {
        dealloc(m_imp);
    }

    lia_move dioph_eq::check() {
        return m_imp->check();
    }

    void dioph_eq::explain(lp::explanation& ex) {
        m_imp->explain(ex);
    }

}  // namespace lp
