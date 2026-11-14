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

- **Equational Reasoning and Term Rewriting (`Equational.py`)**:
  - Subterm tree navigation and replacement (`get_subterm`, `replace_subterm`, `all_subterm_positions`, `all_literal_positions`, `replace_literal_subterm`).
  - Formal equality predicate and congruence axioms generator (`generate_equality_axioms`, `generate_equality_clauses`).
  - Polynomial-time ground Congruence Closure algorithm (`CongruenceClosure`, `check_ground_validity`, `check_ground_satisfiability`).
  - Paramodulation inference rule and equality resolution for first-order equational resolution refutations (`paramodulate`, `equality_resolution`, `prove_by_paramodulation`, `prove_equational_validity`).
  - Term Rewriting System (TRS) with syntactic matching (`match_term`), term normalization (`normalize_term`), Lexicographic Path Ordering (`lpo_greater`), critical pair calculation (`critical_pairs`), and Knuth-Bendix completion (`knuth_bendix_completion`, `solve_word_problem`).

- **Herbrand Theory, Skolemization, and Semantic Tableaux (`Herbrand.py`)**:
  - Robinson first-order syntactic unification with strict occurs-check (`robinson_unify`, `robinson_unify_all`, `robinson_unify_predicates`, `robinson_unify_atoms`).
  - Prenex Normal Form conversion via explicit quantifier movement rules respecting variable captures and alpha-renaming (`to_prenex_by_movement`, `prenex_normal_form`, `is_prenex`, `split_prenex`).
  - Dual Skolemization and Herbrandization (`skolemize_formula`, `herbrandize_formula`, `skolemize_to_clauses`).
  - Signature extraction and Herbrand Universe construction (`FolSignature`, `extract_fol_signature`, `herbrand_universe_level`, `herbrand_universe_strata`, `herbrand_universe_stream`, `herbrand_universe`).
  - Herbrand Base generation (`herbrand_base_level`, `herbrand_base`).
  - Herbrand Expansion Theorem decision procedure and refutation prover with DPLL SAT solving (`ground_instances_of_clause`, `ground_instances_of_clauses`, `HerbrandExpansionProver`, `prove_by_herbrand_expansion`).
  - Free-Variable Semantic Tableaux with Alpha, Beta, Delta (Skolem), and Gamma (fresh variable) rules and global MGU unification (`FvSignedFormula`, `FvTableauBranch`, `FreeVariableTableau`, `prove_by_free_variable_tableau`).

- **Verification and Testing (`tests/`)**:
  - `verify_syntax.py`: Automated syntax and file integrity checker.
  - `test_propositional.py`: Unit test suite for propositional logic and DPLL.
  - `test_first_order.py`: Unit test suite for FOL terms, substitution, unification, models, and resolution.
  - `test_equational.py`: Unit test suite for congruence closure, paramodulation, and Knuth-Bendix completion.
  - `test_herbrand.py`: Unit test suite for Prenex movement, Skolemization, Herbrand Universe/Base, Robinson unification, and Tableaux.

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
