# [MathLogic · Ticket 7452] First-Order Logic AST and Capture-Avoiding Substitution

**Repository:** `MathLogic`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T21:37:15Z`  
**Completed:** `2026-11-13T21:40:00Z`  

## Problem Description
The repository completely lacked first-order logic representation, terms, predicates, quantifiers, and capture-avoiding substitution algorithms.

## Accomplishments
- Implemented First-Order Term hierarchy: `Var`, `Const`, `Fn`.
- Implemented First-Order Formula AST: `Pred`, `Eq`, `FoBot`, `FoTop`, `FoNot`, `FoConj`, `FoDisj`, `FoImpl`, `FoIff`, `Forall`, `Exists`.
- Implemented syntactic variable hygiene according to FACTBOOK: free variable analysis (`free_vars()`), bound variable analysis (`bound_vars()`), and sentence detection (`is_sentence()`).
- Implemented capture-avoiding substitution with alpha-renaming (`subst()`) preventing accidental binder capture.
- Verified substitution behavior in `tests/test_first_order.py`.
