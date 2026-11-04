(* Definition for atomic variables, represented as natural numbers. *)
(* These variables serve as the basic building blocks for propositional formulas. *)
(* Each atomic variable is uniquely identified by a natural number. *)
Definition AtomVars := nat.

(* Inductive type for formulas in propositional logic. *)
(* This type defines the structure of propositional formulas using the following constructors: *)
(* - Atom p: Represents an atomic proposition identified by natural number p *)
(* - Bot: Represents the false proposition (bottom) *)
(* - Conj f1 f2: Represents the conjunction of formulas f1 and f2 *)
(* - Disj f1 f2: Represents the disjunction of formulas f1 and f2 *)
(* - Impl f1 f2: Represents the implication from f1 to f2 *)
Inductive Fo :=
 |Atom (p:AtomVars) : Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
.

Notation " x -/\ y ":=(Conj x y) (at level 80).
Notation " x -\/ y ":=(Disj x y) (at level 80).
Notation " x --> y ":=(Impl x y) (at level 80).

Definition Top:Fo := Bot --> Bot.

(* Definition for valuations, which map atomic variables to boolean values. *)
(* A valuation is a function that assigns a boolean value (true or false) to each atomic proposition. *)
(* This allows us to evaluate formulas under different interpretations of the atomic variables. *)
Definition Valuations := AtomVars -> bool.

(* Section defining the formula evaluation function. *)
Section foIb_sec.
Context (v:AtomVars -> bool).
Fixpoint foIb (f:Fo) : bool 
:= match f with
   | Atom p => v p
   | Bot => false
   | f1 -/\ f2 => andb (foIb f1) (foIb f2)
   | f1 -\/ f2 => orb (foIb f1) (foIb f2)
   | f1 --> f2 => implb (foIb f1) (foIb f2)
   end.
End foIb_sec.



(*Proof.
destruct f.
Show Proof.
Definition isTauto := forall.
Proof.
Defined.*)

