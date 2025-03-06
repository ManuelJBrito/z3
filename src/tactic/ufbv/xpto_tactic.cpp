#include "tactic/tactical.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/var_subst.h"
#include "tactic/ufbv/xpto_tactic.h"

using namespace std;

class xpto_tactic : public tactic {
    struct imp {
        typedef obj_hashtable<expr> expr_set;

        ast_manager &             m;
        array_util                m_arrutil;
        bv_util                   m_bvutil;
        obj_map<expr, expr_set>   m_arr2offsets;
        obj_map<expr, expr_set>   m_arr2axioms;
        ptr_vector<expr>          m_todo;
        var_subst                 m_subst;

        imp(ast_manager & _m):
            m(_m),
            m_arrutil(_m),
            m_bvutil(m),
            m_subst(m) {
        }

        void checkpoint() {
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
        }

        void visit(expr * t, ast_mark & visited) {
            if (!visited.is_marked(t)) {
                if (!is_var(t) && !(is_app(t) && get_depth(t) == 1))
                    visited.mark(t, true);
                m_todo.push_back(t);
            }
        }

        void visit_args(expr * t, ast_mark & visited) {
            if (is_app(t)) {
                for (expr * arg : *to_app(t)) {
                    visit(arg, visited);
                }
            }
        }

        void collect(goal const & g) {
            ast_mark visited;
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++) {
                expr_set arrays;
                expr_set idxs;
                expr * form = g.form(i);
                bool maybe_axiom = is_quantifier(form) &&
                    !has_quantifiers(to_quantifier(form)->get_expr());
                visited.mark(form, true);
                m_todo.push_back(form);
                while (!m_todo.empty()) {
                    checkpoint();
                    expr * t = m_todo.back();
                    m_todo.pop_back();
                    if (is_var(t)) 
                        maybe_axiom = false;
                    else if (is_app(t)) {
                        app *t_app = to_app(t);
                        expr * skip_var = nullptr;
                        if (m_arrutil.is_select(t)) {
                            expr * sel_arr = t_app->get_arg(0);
                            expr * sel_off = t_app->get_arg(1);
                            if (is_var(sel_off))
                                skip_var = sel_off;
                            else    
                                maybe_axiom = false;
                            idxs.insert(sel_off);
                        } else if (m_arrutil.is_array(t) && get_depth(t) == 1){
                            arrays.insert(t);
                        }
                        for (expr * arg : *t_app) {
                            if (!visited.is_marked(arg) && arg != skip_var) {
                                 if (!is_var(t) && !(is_app(t) && get_depth(t) == 1))
                                    visited.mark(arg, true);
                                m_todo.push_back(arg);
                            }
                        }
                    } else {
                        SASSERT(is_quantifier(t));
                        expr * body = to_quantifier(t)->get_expr();
                        visited.mark(body, true);
                        m_todo.push_back(body);
                    }
                }

                if (maybe_axiom && arrays.size() == 1) {
                    expr * arr = *arrays.begin();
                    m_arr2axioms.insert_if_not_there(arr, expr_set()).insert(form);
                } else if (idxs.size()) {
                    // Combinations of every array and select offset that appears in the formula.
                    // This give us an overapproximation of the required idxs.
                    for (expr * arr : arrays) {
                        for (expr * idx : idxs) {
                            m_arr2offsets.insert_if_not_there(arr, expr_set()).insert(idx);
                        }
                    }
                } 
                visited.reset();
            }
        }

        void operator()(goal_ref const &g, goal_ref_buffer & result) {
            tactic_report report("xpto", *g);
            fail_if_proof_generation("xpto", g);
            fail_if_unsat_core_generation("xpto", g);
            ast_mark visited;
            collect(*g);
            expr_ref_vector forms(m);
            expr_set elim_axioms;
            const unsigned MaxInst = 100;
            for (auto & [arr, axioms] : m_arr2axioms) {
                // Check if we read from the array. 
                // If we don't there is nothing to instantiate - eliminate all axioms.
                if (m_arr2offsets.contains(arr)) {
                    expr_set idxs = m_arr2offsets[arr];
                    // If this array requires more than MaxInst instantiations or if some of the idxs
                    // are not ground, then skip its axioms.
                    if (idxs.size() > MaxInst || 
                        any_of(idxs, [](expr * idx){ return !is_app(idx) || !to_app(idx)->is_ground();}))
                        continue;
                    // Iterate through the axioms and instantiate for the read idxs.
                    for (auto & ax : axioms) {
                        for (auto & offset : m_arr2offsets[arr]) {
                            g->assert_expr(m_subst(to_quantifier(ax)->get_expr(), 1, &offset));
                        }
                    }
                }
                for (auto & ax : axioms) {
                    elim_axioms.insert(ax);
                }
            }

            // Reconstruct the goal skipping the eliminated axioms.
            for (unsigned idx = 0; idx < g->size(); idx++) {
                if (!elim_axioms.contains(g->form(idx))) {
                    forms.push_back(g->form(idx));
                }
            }
            g->reset();
            for (unsigned i = 0; i < forms.size(); i++)
                g->assert_expr(forms.get(i), nullptr, nullptr);

            result.push_back(g.get());
        }
    };

    imp *   m_imp;
public:
    xpto_tactic(ast_manager & m) {
        m_imp = alloc(imp, m);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(xpto_tactic, m);
    }

    ~xpto_tactic() override {
        dealloc(m_imp);
    }

    char const* name() const override { return "xpto"; }

    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        (*m_imp)(in, result);
    }
    
    void cleanup() override {
        imp * d = alloc(imp, m_imp->m);
        std::swap(d, m_imp);        
        dealloc(d);
    }

};

tactic * mk_xpto_tactic(ast_manager & m) {
    return alloc(xpto_tactic, m);
}