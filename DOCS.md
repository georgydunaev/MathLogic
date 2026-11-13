# MathLogic Documentation

This repository provides logical systems, theorem proving algorithms, and formal verification tools in both Python and Coq.

## 1. Propositional Logic Engine (`Propositional.py`)

### Core AST
- `Atom(name)`: Atomic proposition identified by an integer or string.
- `Bot()`: Contradiction / false proposition.
- `Top()`: Tautology / true proposition.
- `Not(inner)`: Logical negation.
- `Conj(left, right)`: Conjunction (`&`).
- `Disj(left, right)`: Disjunction (`|`).
- `Impl(left, right)`: Implication (`>>`).
- `Iff(left, right)`: Equivalence (`iff()`).

### Evaluation and Decision Procedures
- `evaluate(valuation)`: Evaluate formula against a boolean valuation dictionary.
- `foIb(valuation, formula)`: Python implementation of Coq's formula evaluation function.
- `truth_table(formula)`: Generates complete truth table for all valuations.
- `is_tautology(formula)`: Checks whether formula is true under every valuation.
- `is_contradiction(formula)`: Checks whether formula is false under every valuation.
- `is_satisfiable(formula)`: Checks whether there exists a satisfying valuation.
- `find_model(formula)`: Returns a satisfying model if satisfiable, or `None`.

### Normal Forms and SAT Solver
- `to_nnf(formula)`: Converts to Negation Normal Form using De Morgan laws and double negation elimination.
- `to_cnf_formula(formula)`: Converts to Conjunctive Normal Form.
- `to_dnf_formula(formula)`: Converts to Disjunctive Normal Form.
- `formula_to_clauses(formula)`: Extracts clause sets from CNF formulas.
- `dpll_solve(clauses)`: Davis-Putnam-Logemann-Loveland SAT solver with unit propagation and pure literal elimination.
- `sat_solve(formula)`: Top-level SAT solver for arbitrary propositional formulas.

---

## 2. First-Order Logic Engine (`FirstOrder.py`)

### First-Order Terms
- `Var(name)`: Individual variable.
- `Const(name)`: Individual constant.
- `Fn(name, args)`: Function application.
- `term.vars()`: Set of variable names occurring in term.
- `term.subst(mapping)`: Term substitution.

### First-Order Formulas
- `Pred(name, args)`: Atomic predicate application.
- `Eq(left, right)`: Equality predicate.
- `FoBot()`, `FoTop()`: Truth constants.
- `FoNot(inner)`: Negation.
- `FoConj(left, right)`, `FoDisj(left, right)`: Conjunction and disjunction.
- `FoImpl(left, right)`, `FoIff(left, right)`: Implication and equivalence.
- `Forall(var, body)`: Universal quantification.
- `Exists(var, body)`: Existential quantification.

### Variable Hygiene and Substitution
- `free_vars()`: Returns set of free variable names.
- `bound_vars()`: Returns set of bound variable names.
- `is_sentence()`: Returns True if formula has no free variables.
- `subst(mapping)`: Capture-avoiding substitution with automatic alpha-renaming of bound variables.

### Unification and Resolution Prover
- `unify_terms(t1, t2)`: Robinson's syntactic term unification with occurs-check.
- `unify_predicates(p1, p2)`: Unification for atomic predicates.
- `Structure(domain, constants, functions, predicates)`: First-order semantic structure / model evaluator over finite domains.
- `FoLiteral(pred, is_positive)`: Clausal first-order literal.
- `FoClause(literals)`: Clausal first-order clause with variable standardization apart.
- `resolve_clauses(c1, c2)`: Binary resolution resolvents generator.
- `factor_clause(clause)`: Clause factoring generator.
- `prove_by_resolution(clauses)`: Automated resolution refutation theorem prover.

### Normal Forms, Skolemization, and Tableau Prover
- `to_nnf(formula)`: Converts first-order formulas to Negation Normal Form (NNF).
- `standardize_apart_formula(formula)`: Standardizes all bound variables across quantifiers.
- `to_prenex(formula)`: Extracts quantifiers to the prefix, producing Prenex Normal Form.
- `skolemize(formula, drop_universal)`: Replaces existential quantifiers with Skolem functions or constants.
- `formula_to_clauses(formula)`: Converts an arbitrary first-order formula into clausal form.
- `prove_validity_by_resolution(formula, max_steps)`: Proves validity of first-order formulas by refuting the negation using resolution.
- `SignedFormula(formula, sign)`: Signed first-order formula for semantic tableau.
- `TableauBranch`: Represents and expands individual branches in an analytic tableau.
- `SemanticTableau`: First-order analytic semantic tableau theorem prover.
- `prove_by_tableau(formula, max_steps)`: Proves validity using semantic tableau refutation.

---

## 3. Coq Formalization (`Propositional.v`)

- `AtomVars`: Atomic variables represented as `nat`.
- `Fo`: Inductive type for propositional formulas (`Atom`, `Bot`, `Conj`, `Disj`, `Impl`).
- `Top`: Definition of tautology constant (`Bot --> Bot`).
- `Valuations`: Mapping `AtomVars -> bool`.
- `foIb`: Fixpoint computing boolean truth value under valuation.
- `isTauto`: Definition of propositional tautology (`forall v, foIb v f = true`).
- `top_is_tauto`: Verified theorem proving `Top` is a tautology.
- `conj_tauto`: Verified theorem proving conjunction of tautologies is a tautology.
- `Prf`: Hilbert-style propositional deductive calculus (`AxK`, `AxS`, `AxContra`, `MP`).
- `prf_id`: Verified theorem proving syntactic identity `Prf (A --> A)`.
- `soundness`: Verified theorem proving soundness of Hilbert deduction (`forall f, Prf f -> isTauto f`).

---

## 4. Verification and Testing

Run the syntax verification script:
```bash
python3 tests/verify_syntax.py
```

Run the complete test suite:
```bash
python3 -m unittest discover -s tests
```
