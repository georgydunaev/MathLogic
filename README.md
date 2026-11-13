# MathLogic

MathLogic is a formal logic and automated reasoning repository implementing propositional and first-order predicate logic engines, normal form transformations, SAT solvers, unification algorithms, and resolution refutation provers.

## Contents

- **Propositional Logic (`Propositional.py` & `Propositional.v`)**:
  - Full AST with operator overloading (`Atom`, `Bot`, `Top`, `Not`, `Conj`, `Disj`, `Impl`, `Iff`).
  - Valuation evaluation and complete truth table generation.
  - Tautology, contradiction, and satisfiability decision procedures.
  - Normal form conversions: Negation Normal Form (NNF), Conjunctive Normal Form (CNF), Disjunctive Normal Form (DNF).
  - Davis-Putnam-Logemann-Loveland (DPLL) SAT solver with unit propagation and pure literal elimination.
  - Formal Coq proofs of tautology properties, Hilbert deductive calculus (`Prf`), identity theorem, and soundness in `Propositional.v`.

- **First-Order Logic (`FirstOrder.py`)**:
  - Terms: Individual variables (`Var`), constants (`Const`), function applications (`Fn`).
  - Formulas: Predicates (`Pred`), Equality (`Eq`), connectives, and quantifiers (`Forall`, `Exists`).
  - Syntactic variable analysis: free variables, bound variables, sentence classification.
  - Capture-avoiding substitution with automatic alpha-renaming.
  - Robinson's first-order syntactic unification algorithm with occurs-check.
  - First-order semantic structure evaluator over finite interpretation domains.
  - Clausal first-order resolution refutation theorem prover with factoring and variable standardization apart.
  - Normal forms and Skolemization: NNF, Prenex normal form (`to_prenex`), Skolem normal form (`skolemize`), and clausal conversion (`formula_to_clauses`).
  - Automated validity refutation via clausal resolution (`prove_validity_by_resolution`).
  - Analytic first-order Semantic Tableau prover (`SemanticTableau`, `prove_by_tableau`).

- **Verification and Testing (`tests/`)**:
  - `verify_syntax.py`: Automated syntax and file integrity checker.
  - `test_propositional.py`: Unit test suite for propositional logic and DPLL.
  - `test_first_order.py`: Unit test suite for FOL terms, substitution, unification, models, and resolution.

## Quick Start

### Running Verification & Tests

To verify syntax across all files:
```bash
python3 tests/verify_syntax.py
```

To run the complete unit test suite:
```bash
python3 -m unittest discover -s tests
```

### Python Interactive Example

```python
import Propositional as P
import FirstOrder as FO

# Propositional Logic
p = P.Atom("P")
q = P.Atom("Q")
peirce = ((p >> q) >> p) >> p
print("Peirce's Law is tautology:", P.is_tautology(peirce))

# First-Order Logic Unification
x = FO.Var("x")
y = FO.Var("y")
c = FO.Const("c")
t1 = FO.Fn("f", [x, FO.Fn("g", [y])])
t2 = FO.Fn("f", [c, FO.Fn("g", [FO.Const("d")])])
mgu = FO.unify_terms(t1, t2)
print("MGU:", mgu)
```

## Documentation

See [DOCS.md](file:///botworkspace/MathLogic/DOCS.md) for detailed class references and mathematical definitions.

## License

This project is licensed under the MIT License - see the LICENSE file for details.
