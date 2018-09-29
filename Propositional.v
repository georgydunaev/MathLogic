Definition AtomVars := nat.

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

Definition Valuations := AtomVars -> bool.

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

