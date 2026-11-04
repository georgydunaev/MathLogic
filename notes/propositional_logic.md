# Propositional Logic in Coq

This note explains a basic implementation of propositional logic in Coq. The implementation includes the definition of atoms, connectives, and a valuation function.

## Atoms

Atoms are the basic building blocks of propositional logic. In this example, we define three atoms: `A`, `B`, and `C`.

```coq
Inductive atom : Type := | A | B | C.
```

## Formulas

Formulas are constructed using atoms and logical connectives. The connectives include negation (`Not`), conjunction (`And`), disjunction (`Or`), and implication (`Implies`).

```coq
Inductive formula : Type := | Atom : atom -> formula | Not : formula -> formula | And : formula -> formula -> formula | Or : formula -> formula -> formula | Implies : formula -> formula -> formula.
```

## Valuation Function

The valuation function assigns truth values to atoms. In this example, `A` and `C` are assigned `true`, while `B` is assigned `false`.

```coq
Definition valuation (a : atom) : bool := match a with | A => true | B => false | C => true end.
```

## Evaluation Function

The evaluation function recursively evaluates a formula given a valuation. It handles each connective appropriately, such as negation, conjunction, disjunction, and implication.

```coq
Fixpoint eval (f : formula) : bool := match f with | Atom a => valuation a | Not f => not (eval f) | And f1 f2 => eval f1 && eval f2 | Or f1 f2 => eval f1 || eval f2 | Implies f1 f2 => not (eval f1) || eval f2 end.
```

## Example Usage

The example demonstrates how to evaluate the formula `And (Atom A) (Not (Atom B))`.

```coq
Eval compute in eval (And (Atom A) (Not (Atom B))).
```

This implementation provides a foundational understanding of propositional logic in Coq and can be extended for more complex logical systems.