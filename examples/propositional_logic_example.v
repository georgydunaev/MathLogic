(* Propositional Logic Example in Coq *)

(* Define the type of propositional atoms *)Inductive atom : Type := | A | B | C.

(* Define the type of propositional formulas *)Inductive formula : Type := | Atom : atom -> formula | Not : formula -> formula | And : formula -> formula -> formula | Or : formula -> formula -> formula | Implies : formula -> formula -> formula.

(* Define a valuation function that assigns truth values to atoms *)Definition valuation (a : atom) : bool := match a with | A => true | B => false | C => true end.

(* Define a function to evaluate a formula given a valuation *)Fixpoint eval (f : formula) : bool := match f with | Atom a => valuation a | Not f => not (eval f) | And f1 f2 => eval f1 && eval f2 | Or f1 f2 => eval f1 || eval f2 | Implies f1 f2 => not (eval f1) || eval f2 end.

(* Example usage *)Eval compute in eval (And (Atom A) (Not (Atom B))).
