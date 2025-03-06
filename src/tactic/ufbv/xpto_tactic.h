/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    xpto_tactic.h

Abstract:

    XPTO

Author:

TODO

Tactic Documentation

## Tactic macro-finder

TODO

### Short Description 

TODO

### Long Description

TODO

```

### Notes

* Does not support proofs, unsat cores nor goals with recursive function definitions.

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_xpto_tactic(ast_manager & m);

/*
  ADD_TACTIC("xpto",  "Top secret tactic", "mk_xpto_tactic(m)")
*/

