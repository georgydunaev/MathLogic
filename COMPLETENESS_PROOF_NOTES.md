# Propositional Deduction Theorem and Kalmar Completeness Proof Notes (`MathLogic`)

This document describes the formal mechanization in [Completeness_And_Deduction.v](Completeness_And_Deduction.v) extending [Propositional.v](Propositional.v) with contextual Hilbert derivability, the syntactic Deduction Theorem, classical combinators, and László Kalmár's constructive truth-table completeness proof (`soundness_and_completeness_iff`, `Qed.`).

---

## 1. Contextual Hilbert Calculus (`PrfInCtx`) and Syntactic Deduction Theorem

In [Propositional.v](Propositional.v#L83-L87), the Łukasiewicz/Church Hilbert system `Prf : Fo -> Prop` is defined by:
- `AxK (A B : Fo) : Prf (A --> (B --> A))`
- `AxS (A B C : Fo) : Prf ((A --> (B --> C)) --> ((A --> B) --> (A --> C)))`
- `AxContra (A B : Fo) : Prf (((A --> Bot) --> (B --> Bot)) --> (B --> A))`
- `MP (A B : Fo) : Prf (A --> B) -> Prf A -> Prf B`

In [Completeness_And_Deduction.v](Completeness_And_Deduction.v), we extend `Prf` to an explicit hypothesis context `Gamma : list Fo` via `Inductive PrfInCtx (Gamma : list Fo) : Fo -> Prop` and prove:
1. **`PrfInCtx_weaken`**: Monotonicity under context inclusion `forall X, In X Gamma -> In X Delta`.
2. **`PrfInCtx_nil_iff`**: `forall A : Fo, PrfInCtx [] A <-> Prf A`.
3. **`Deduction_Theorem`**:
   $$\forall \Gamma\, A\, B,\quad \mathrm{PrfInCtx}\; (A :: \Gamma)\; B \implies \mathrm{PrfInCtx}\; \Gamma\; (A \to B)$$
   proved by structural induction on the derivation of `B` using `ctx_id` ($S K K$) for the head hypothesis $A$, `ctx_const` ($K$) for tail hypotheses and axioms, and `CtxAxS` ($S$) for Modus Ponens steps.

---

## 2. Constructive Hilbert Combinators and Classical Derived Theorems

Using `Deduction_Theorem` and `PrfInCtx_nil_iff`, [Completeness_And_Deduction.v](Completeness_And_Deduction.v) derives the following theorems in the base system `Prf` (all closed with `Qed.`):

| Theorem | Statement | Role |
|---|---|---|
| `prf_const` | `forall A B, Prf B -> Prf (A --> B)` | $K$-combinator weakening rule |
| `prf_mp_chain` | `forall A B C, Prf (A --> (B --> C)) -> Prf (A --> B) -> Prf (A --> C)` | $S$-combinator application rule |
| `prf_syllogism` | `forall A B C, Prf ((A --> B) --> ((B --> C) --> (A --> C)))` | Hypothetical syllogism ($B$-combinator) |
| `prf_ex_falso` | `forall A, Prf (Bot --> A)` | Explosion (Ex Falso Quodlibet) from `AxContra A Bot` |
| `prf_dne` | `forall A, Prf (((A --> Bot) --> Bot) --> A)` | Double Negation Elimination via `AxContra A (Bot --> Bot)` |
| `prf_dni` | `forall A, Prf (A --> ((A --> Bot) --> Bot))` | Double Negation Introduction |
| `prf_absurd` | `forall A B, Prf (A --> ((A --> Bot) --> B))` | Contradiction elimination |
| `prf_case_split` | `forall A B, Prf ((A --> B) --> (((A --> Bot) --> B) --> B))` | Classical case analysis on $A$ vs. $A \to \bot$ |
| `prf_peirce_dne` | `forall A B, Prf (((A --> B) --> A) --> A)` | Peirce's Law derived from `prf_case_split A A` |
| `ctx_case_split` | `PrfInCtx (A :: Gamma) B -> PrfInCtx ((A --> Bot) :: Gamma) B -> PrfInCtx Gamma B` | Context variable elimination rule |

---

## 3. Kalmár's Truth-Table Completeness Proof (`kalmar_completeness`)

For any valuation $v : \mathrm{AtomVars} \to \mathrm{bool}$ and atomic variable $p$, define the signed literal:
$$\mathrm{signed\_atom}(v, p) := \begin{cases} \mathrm{Atom}\; p & \text{if } v(p) = \mathrm{true}, \\ \mathrm{Atom}\; p \to \bot & \text{if } v(p) = \mathrm{false}. \end{cases}$$

### Step 1: Truth-Value Simulation (`kalmar_eval_simulation`)
For any formula $f$ in the $\{\mathrm{Atom}, \bot, \to\}$ fragment (`is_imp_bot f = true`), any valuation $v$, and any context $\Gamma$ containing $\mathrm{signed\_atom}(v, p)$ for every atom $p \in \mathrm{fo\_vars}(f)$, structural induction on $f$ using `imp_true_r`, `imp_false_l`, and `imp_true_false` proves:
- If `foIb v f = true`, then `PrfInCtx Gamma f`.
- If `foIb v f = false`, then `PrfInCtx Gamma (f --> Bot)`.

### Step 2: Inductive Variable Elimination (`kalmar_eliminate_vars`)
By induction on any list of atomic variables `ps : list AtomVars`, if `PrfInCtx (literal_ctx v ps ++ Gamma) f` holds for every valuation $v$:
- In the inductive step `p :: ps`:
  - If $p \in \mathrm{ps}$, then $\mathrm{signed\_atom}(v, p)$ already appears in `literal_ctx v ps`, so weakening contracts the duplicate assumption.
  - If $p \notin \mathrm{ps}$, instantiating the hypothesis at `update_val v p true` and `update_val v p false` (using `literal_ctx_irrel`) yields `PrfInCtx (Atom p :: literal_ctx v ps ++ Gamma) f` and `PrfInCtx ((Atom p --> Bot) :: literal_ctx v ps ++ Gamma) f`, which combine via `ctx_case_split` to give `PrfInCtx (literal_ctx v ps ++ Gamma) f`.

### Step 3: Semantic Completeness and Equivalence (`kalmar_completeness`, `soundness_and_completeness_iff`)
If `isTauto f` holds (`forall v, foIb v f = true`), then `kalmar_eval_simulation` yields `PrfInCtx (literal_ctx v (fo_vars f)) f` for every valuation $v$, and `kalmar_eliminate_vars` eliminates all variables in `fo_vars f` to yield `PrfInCtx [] f`, hence `Prf f` (`Qed.`). Combining with `soundness` from [Propositional.v](Propositional.v#L107) establishes:
```coq
Theorem soundness_and_completeness_iff :
  forall f : Fo,
    is_imp_bot f = true ->
    (Prf f <-> isTauto f).
```
