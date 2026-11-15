# Architecture, Axiom Systems, Formalizations, and Theorems Guide

## 1. Repository Architecture Overview

`MathLogic` is a formal mathematical logic and automated theorem proving repository combining mechanized Coq developments (`Propositional.v`, `examples/propositional_logic_example.v`) with four self-contained Python reasoning engines (`Propositional.py`, `FirstOrder.py`, `Equational.py`, `Herbrand.py`).

### Module Map

| File | Lines | Scope and Formalization Role |
|---|---:|---|
| [`Propositional.v`](file:///botworkspace/MathLogic/Propositional.v) | 134 | Coq formalization of propositional syntax (`Fo`), boolean valuation semantics (`foIb`), tautology predicate (`isTauto`), Łukasiewicz/Church Hilbert deductive calculus (`Prf`), syntactic identity (`prf_id`), and deductive soundness (`soundness`). |
| [`Completeness_And_Deduction.v`](file:///botworkspace/MathLogic/Completeness_And_Deduction.v) | 525 | Constructive Coq formalization (`Qed.`) of contextual Hilbert derivability (`PrfInCtx`), the syntactic Deduction Theorem (`Deduction_Theorem`), classical combinators (`prf_syllogism`, `prf_ex_falso`, `prf_dne`, `prf_case_split`, `prf_peirce_dne`), and Kalmár's Semantic Completeness Theorem (`kalmar_completeness`, `soundness_and_completeness_iff`), documented in [`COMPLETENESS_PROOF_NOTES.md`](file:///botworkspace/MathLogic/COMPLETENESS_PROOF_NOTES.md). |
| [`examples/propositional_logic_example.v`](file:///botworkspace/MathLogic/examples/propositional_logic_example.v) | 38 | Introductory Coq formalization of finite-atom propositional formulas, boolean evaluation (`eval`), and verified evaluation (`example_eval_true`). |
| [`Propositional.py`](file:///botworkspace/MathLogic/Propositional.py) | 504 | Propositional AST (`Atom`, `Bot`, `Top`, `Not`, `Conj`, `Disj`, `Impl`, `Iff`), valuation evaluator (`foIb`), truth table generator, semantic decision procedures, NNF/CNF/DNF transformations, and DPLL SAT solver with unit propagation and pure literal elimination. |
| [`FirstOrder.py`](file:///botworkspace/MathLogic/FirstOrder.py) | 1395 | First-order terms (`Var`, `Const`, `Fn`) and formulas (`Pred`, `Eq`, connectives, `Forall`, `Exists`), capture-avoiding substitution with alpha-renaming, Robinson unification, finite-domain Tarski structure evaluation (`Structure`), NNF/Prenex/Skolem/clausal transformations, binary resolution + factoring theorem prover, and analytic semantic tableau prover. |
| [`Equational.py`](file:///botworkspace/MathLogic/Equational.py) | 880 | Subterm position navigation, equality reflexivity/symmetry/transitivity and function/predicate congruence axiom generators, polynomial-time ground Congruence Closure (`CongruenceClosure`), first-order Paramodulation and Equality Resolution refutation prover, Lexicographic Path Ordering (`lpo_greater`), critical pairs, and Knuth-Bendix completion (`knuth_bendix_completion`, `solve_word_problem`). |
| [`Herbrand.py`](file:///botworkspace/MathLogic/Herbrand.py) | 1093 | Strict Robinson syntactic unification, quantifier-movement Prenex Normal Form converter, dual Skolemization and Herbrandization, signature extraction, stratified and lazy Herbrand Universe and Herbrand Base construction, Herbrand Expansion Theorem prover via ground DPLL, and Free-Variable Semantic Tableaux with MGU branch closure. |
| [`notes/propositional_logic.md`](file:///botworkspace/MathLogic/notes/propositional_logic.md) | 61 | Tutorial note accompanying `examples/propositional_logic_example.v` and `Propositional.v`. |

---

## 2. Formalized Axiom Systems and Deductive Calculi

### 2.1 Classical Hilbert Propositional Calculus (`Prf` in [`Propositional.v`](file:///botworkspace/MathLogic/Propositional.v#L83-L87))
Defined over the inductive formula type `Fo` (`Atom`, `Bot`, `Conj`, `Disj`, `Impl`, with `Top := Bot --> Bot`):
- **`AxK`**: $A \to (B \to A)$ (`Prf (A --> (B --> A))`)
- **`AxS`**: $(A \to (B \to C)) \to ((A \to B) \to (A \to C))$ (`Prf ((A --> (B --> C)) --> ((A --> B) --> (A --> C)))`)
- **`AxContra`**: $((A \to \bot) \to (B \to \bot)) \to (B \to A)$ (`Prf (((A --> Bot) --> (B --> Bot)) --> (B --> A))`)
- **`MP` (Modus Ponens)**: From `Prf (A --> B)` and `Prf A`, infer `Prf B`.

### 2.2 First-Order Equality and Congruence Axiom System ([`Equational.py`](file:///botworkspace/MathLogic/Equational.py))
Generated both as closed first-order sentences (`generate_equality_axioms`) and as clausal normal forms (`generate_equality_clauses`) over any first-order signature $\Sigma = (\mathcal{C}, \mathcal{F}, \mathcal{P})$:
- **Reflexivity**: $\forall x,\, x = x$.
- **Symmetry**: $\forall x\, y,\, x = y \to y = x$.
- **Transitivity**: $\forall x\, y\, z,\, (x = y \land y = z) \to x = z$.
- **Function Congruence**: For every $n$-ary $f \in \mathcal{F}$, $\forall x_1 \dots x_n\, y_1 \dots y_n,\, (\bigwedge_{i=1}^n x_i = y_i) \to f(x_1, \dots, x_n) = f(y_1, \dots, y_n)$.
- **Predicate Congruence**: For every $n$-ary $P \in \mathcal{P}$, $\forall x_1 \dots x_n\, y_1 \dots y_n,\, (\bigwedge_{i=1}^n x_i = y_i \land P(x_1, \dots, x_n)) \to P(y_1, \dots, y_n)$.

### 2.3 Clausal Resolution, Factoring, and Paramodulation Calculi ([`FirstOrder.py`](file:///botworkspace/MathLogic/FirstOrder.py), [`Equational.py`](file:///botworkspace/MathLogic/Equational.py))
- **Binary Resolution (`resolve_clauses`)**: From $C_1 \lor L_1$ and $C_2 \lor \neg L_2$ (standardized apart), infer $(C_1 \lor C_2)\sigma$ where $\sigma = \mathrm{mgu}(L_1, L_2)$.
- **Positive/Negative Factoring (`factor_clause`)**: From $C \lor L_1 \lor L_2$, infer $(C \lor L_1)\sigma$ where $\sigma = \mathrm{mgu}(L_1, L_2)$.
- **Paramodulation (`paramodulate`)**: From $C_1 \lor (s = t)$ (or $t = s$) and $C_2[u]_p$ where $u$ is a non-variable subterm at position $p$ and $\sigma = \mathrm{mgu}(s, u)$, infer $(C_1 \lor C_2[t]_p)\sigma$.
- **Equality Resolution (`equality_resolution`)**: From $C \lor (s \neq t)$ where $\sigma = \mathrm{mgu}(s, t)$, infer $C\sigma$.

### 2.4 Analytic and Free-Variable Semantic Tableaux ([`FirstOrder.py`](file:///botworkspace/MathLogic/FirstOrder.py), [`Herbrand.py`](file:///botworkspace/MathLogic/Herbrand.py))
- **Signed Smullyan Rules**:
  - $\alpha$-rules (conjunctive linear expansion): $T(A \land B)$, $F(A \lor B)$, $F(A \to B)$, $T(\neg A)$, $F(\neg A)$.
  - $\beta$-rules (disjunctive branching): $F(A \land B)$, $T(A \lor B)$, $T(A \to B)$, $T(A \leftrightarrow B)$, $F(A \leftrightarrow B)$.
  - $\delta$-rules (fresh witness / Skolem instantiation): $T(\exists x\,\phi(x))$, $F(\forall x\,\phi(x))$.
  - $\gamma$-rules (universal instantiation): Ground term instantiation in `SemanticTableau` (`FirstOrder.py`) and free-variable introduction with branch-closure MGU unification in `FreeVariableTableau` (`Herbrand.py`).

---

## 3. Catalog of Verified Theorems and Implemented Algorithms

### 3.1 Mechanized Coq Theorems (`Propositional.v` & `examples/propositional_logic_example.v`)

| Theorem | File & Line | Formal Statement | Status |
|---|---|---|---|
| `top_is_tauto` | [`Propositional.v:51`](file:///botworkspace/MathLogic/Propositional.v#L51) | `isTauto Top` (`forall v, foIb v (Bot --> Bot) = true`) | `Qed.` |
| `conj_tauto` | [`Propositional.v:60`](file:///botworkspace/MathLogic/Propositional.v#L60) | `forall f1 f2 : Fo, isTauto f1 -> isTauto f2 -> isTauto (f1 -/\ f2)` | `Qed.` |
| `prf_id` | [`Propositional.v:93`](file:///botworkspace/MathLogic/Propositional.v#L93) | `forall A : Fo, Prf (A --> A)` (SK combinator derivation `S K K`) | `Qed.` |
| `soundness` | [`Propositional.v:107`](file:///botworkspace/MathLogic/Propositional.v#L107) | `forall f : Fo, Prf f -> isTauto f` (semantic soundness of Hilbert calculus) | `Qed.` |
| `Deduction_Theorem` | [`Completeness_And_Deduction.v:108`](file:///botworkspace/MathLogic/Completeness_And_Deduction.v#L108) | `forall Gamma A B, PrfInCtx (A :: Gamma) B -> PrfInCtx Gamma (A --> B)` | `Qed.` |
| `prf_ex_falso`, `prf_dne`, `prf_case_split`, `prf_peirce_dne` | [`Completeness_And_Deduction.v:157-262`](file:///botworkspace/MathLogic/Completeness_And_Deduction.v#L157-L262) | Explosion, Double Negation Elimination, Classical Case Split, and Peirce's Law in `Prf` | `Qed.` |
| `kalmar_eval_simulation` | [`Completeness_And_Deduction.v:361`](file:///botworkspace/MathLogic/Completeness_And_Deduction.v#L361) | Truth-value simulation of `foIb v f` in signed literal context `Gamma` | `Qed.` |
| `kalmar_completeness` & `soundness_and_completeness_iff` | [`Completeness_And_Deduction.v:511-534`](file:///botworkspace/MathLogic/Completeness_And_Deduction.v#L511-L534) | `is_imp_bot f = true -> (Prf f <-> isTauto f)` (Kalmár semantic completeness of `Prf`) | `Qed.` |
| `example_eval_true` | [`examples/propositional_logic_example.v:33`](file:///botworkspace/MathLogic/examples/propositional_logic_example.v#L33) | `eval (And (Atom A) (Not (Atom B))) = true` | `Qed.` |

### 3.2 Algorithmic Metatheorems and Decision Procedures in Python

1. **Propositional Normal Forms and DPLL (`Propositional.py`)**:
   - Equivalence-preserving NNF (`to_nnf`), CNF (`to_cnf_formula`), DNF (`to_dnf_formula`), and DPLL satisfiability (`dpll_solve`, `sat_solve`).
2. **Capture-Avoiding Substitution & Quantifier Transformations (`FirstOrder.py`, `Herbrand.py`)**:
   - Capture-avoiding substitution `subst` with automatic bound-variable alpha-renaming.
   - Quantifier movement Prenex Normal Form (`to_prenex`, `to_prenex_by_movement`, `prenex_normal_form`).
   - Dual Skolemization (satisfiability-preserving existential elimination `skolemize`, `skolemize_formula`) and Herbrandization (validity-preserving universal elimination `herbrandize_formula`).
3. **Herbrand's Theorem Engine (`Herbrand.py`)**:
   - Stratified Herbrand Universe $H_0, H_1, \dots, H_k$ (`herbrand_universe_level`, `herbrand_universe_strata`, `herbrand_universe_stream`) and Herbrand Base (`herbrand_base`).
   - `HerbrandExpansionProver`: Semi-decision refutation procedure reducing first-order unsatisfiability of a universal clause set to propositional unsatisfiability of a finite ground expansion solved via DPLL.
4. **Equational Decision Procedures (`Equational.py`)**:
   - Nelson-Oppen / Downey-Sethi-Tarjan ground Congruence Closure (`CongruenceClosure`, `check_ground_validity`, `check_ground_satisfiability`).
   - Lexicographic Path Ordering (`lpo_greater`) and Knuth-Bendix completion (`knuth_bendix_completion`, `solve_word_problem`) converting equational axioms into a confluent, terminating Term Rewriting System.

---

## 4. Open Problems and Future Extensions

All Coq proofs in `Propositional.v` and `examples/propositional_logic_example.v` are closed with `Qed.` (zero `Admitted` or `Abort` statements), and all 4 Python test suites pass syntax and unit verification. Open directions for future expansion documented in [`ROADMAP.md`](file:///botworkspace/MathLogic/ROADMAP.md) include:

1. **Completeness of `Prf` in Coq (`Propositional.v`)**:
   - Extending the Hilbert calculus in `Propositional.v` with conjunction/disjunction axioms (or defining `&` and `|` via `Impl` and `Bot`) and proving Kalmár/Lindenbaum semantic completeness (`forall f : Fo, isTauto f -> Prf f`).
2. **Coq Formalization of First-Order Unification and Herbrand's Theorem**:
   - Mechanizing the Python algorithms in `FirstOrder.py` and `Herbrand.py` inside Coq with verified termination measures on variable sets and term sizes.
3. **Superposition Calculus with Ordering Restrictions (`Equational.py`)**:
   - Restricting `paramodulate` and `resolve_clauses` using the already-implemented Lexicographic Path Ordering (`lpo_greater`) so that paramodulation only rewrites maximal sides of maximal literals (Ordered Resolution / Superposition).
