# Propositional Logic in Coq

This note explains the implementation of propositional logic in Coq in [`examples/propositional_logic_example.v`](file:///botworkspace/MathLogic/examples/propositional_logic_example.v) and [`Propositional.v`](file:///botworkspace/MathLogic/Propositional.v). The implementation includes the definition of atoms, connectives, a boolean valuation function, recursive formula evaluation, and formal verification.

## Atoms

Atoms are the basic building blocks of propositional logic. In `examples/propositional_logic_example.v`, three finite atoms (`A`, `B`, and `C`) are defined (whereas `Propositional.v` uses `AtomVars := nat` for an unbounded supply of propositional variables):

```coq
Require Import Bool.

Inductive atom : Type := | A | B | C.
```

## Formulas

Formulas are constructed inductively using atoms and logical connectives (`Not`, `And`, `Or`, and `Implies`):

```coq
Inductive formula : Type :=
  | Atom : atom -> formula
  | Not : formula -> formula
  | And : formula -> formula -> formula
  | Or : formula -> formula -> formula
  | Implies : formula -> formula -> formula.
```

## Valuation Function

The valuation function assigns boolean truth values to atomic propositions (`A` and `C` are assigned `true`, while `B` is assigned `false`):

```coq
Definition valuation (a : atom) : bool :=
  match a with
  | A => true
  | B => false
  | C => true
  end.
```

## Evaluation Function

The evaluation function recursively computes the boolean truth value of a formula using boolean negation (`negb`), conjunction (`&&`), and disjunction (`||`):

```coq
Fixpoint eval (f : formula) : bool :=
  match f with
  | Atom a => valuation a
  | Not f1 => negb (eval f1)
  | And f1 f2 => eval f1 && eval f2
  | Or f1 f2 => eval f1 || eval f2
  | Implies f1 f2 => negb (eval f1) || eval f2
  end.
```

## Verified Example Theorem

We can formally prove that `And (Atom A) (Not (Atom B))` evaluates to `true`:

```coq
Theorem example_eval_true : eval (And (Atom A) (Not (Atom B))) = true.
Proof.
  simpl.
  reflexivity.
Qed.
```
