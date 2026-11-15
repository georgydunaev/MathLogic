# Project Overview: Propositional, First-Order, and Equational Automated Reasoning (`MathLogic`)

## 1. Purpose and Scope
`MathLogic` (`/botworkspace/MathLogic`) implements automated theorem proving algorithms in Python alongside mechanized Coq soundness and completeness developments (`Propositional.v`, `Completeness_And_Deduction.v`). Compiled `.vo` files are strictly immutable per Fact 11.

## 2. Core Modules
- [Propositional.py](file:///botworkspace/MathLogic/Propositional.py) — Propositional formula AST, truth-table generator, NNF/CNF/DNF converters, and Davis-Putnam-Logemann-Loveland (`DPLL`) SAT solver with unit propagation and pure literal elimination.
- [FirstOrder.py](file:///botworkspace/MathLogic/FirstOrder.py) — First-order terms and formulas, free/bound variable analysis, capture-avoiding substitution with alpha-renaming, and Robinson's syntactic unification algorithm with occurs-check.
- [Herbrand.py](file:///botworkspace/MathLogic/Herbrand.py) — Prenex Normal Form (`PNF`) and Skolem Normal Form (`SNF`) conversion, Herbrand universe enumeration, Gilmore/Davis-Putnam ground instantiation, and first-order resolution refutation prover with factoring.
- [Equational.py](file:///botworkspace/MathLogic/Equational.py) — Term rewriting systems, Lexicographic Path Ordering (`LPO`), Knuth-Bendix completion, and congruence closure.
- [Propositional.v](file:///botworkspace/MathLogic/Propositional.v) and [Completeness_And_Deduction.v](file:///botworkspace/MathLogic/Completeness_And_Deduction.v) — Coq formalizations of Hilbert propositional calculus, the Deduction Theorem, Lindenbaum maximal consistent extensions, and truth-valuation soundness/completeness.
- [ARCHITECTURE_AND_THEOREMS.md](file:///botworkspace/MathLogic/ARCHITECTURE_AND_THEOREMS.md) and [COMPLETENESS_PROOF_NOTES.md](file:///botworkspace/MathLogic/COMPLETENESS_PROOF_NOTES.md) — Detailed theorem and module index.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/MathLogic/tests -p "test_*.py"
```
