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



(* Tautology definition: a formula is a tautology if it evaluates to true under all valuations. *)
Definition isTauto (f:Fo) : Prop := forall (v:Valuations), foIb v f = true.

(* Theorem: Top is a tautology *)
Theorem top_is_tauto : isTauto Top.
Proof.
  intro v.
  unfold Top.
  simpl.
  reflexivity.
Qed.

(* Theorem: Conjunction of tautologies is a tautology *)
Theorem conj_tauto (f1 f2 : Fo) :
  isTauto f1 -> isTauto f2 -> isTauto (f1 -/\ f2).
Proof.
  intros H1 H2 v.
  simpl.
  rewrite (H1 v).
  rewrite (H2 v).
  simpl.
  reflexivity.
Qed.

(* ------------------------------------------------------------- *)
(* Hilbert-Style Propositional Deductive Calculus                *)
(* ------------------------------------------------------------- *)

(*
   The deductive system Prf has three axiom schemas and inference rules for
   implication, conjunction, and disjunction:
   - AxK: A --> (B --> A)
   - AxS: (A --> (B --> C)) --> ((A --> B) --> (A --> C))
   - AxContra: ((A --> Bot) --> (B --> Bot)) --> (B --> A)
   - MP: Modus Ponens (from A --> B and A, infer B)
   - ConjI: Conjunction Introduction (from A and B, infer A -/\ B)
   - ConjEL: Left Conjunction Elimination (from A -/\ B, infer A)
   - ConjER: Right Conjunction Elimination (from A -/\ B, infer B)
   - DisjIL: Left Disjunction Introduction (from A, infer A -\/ B)
   - DisjIR: Right Disjunction Introduction (from B, infer A -\/ B)
   - DisjE: Disjunction Elimination (from A -\/ B, A --> C, and B --> C, infer C)
*)

Inductive Prf : Fo -> Prop :=
  | AxK (A B : Fo) : Prf (A --> (B --> A))
  | AxS (A B C : Fo) : Prf ((A --> (B --> C)) --> ((A --> B) --> (A --> C)))
  | AxContra (A B : Fo) : Prf (((A --> Bot) --> (B --> Bot)) --> (B --> A))
  | MP (A B : Fo) : Prf (A --> B) -> Prf A -> Prf B
  | ConjI (A B : Fo) : Prf A -> Prf B -> Prf (A -/\ B)
  | ConjEL (A B : Fo) : Prf (A -/\ B) -> Prf A
  | ConjER (A B : Fo) : Prf (A -/\ B) -> Prf B
  | DisjIL (A B : Fo) : Prf A -> Prf (A -\/ B)
  | DisjIR (A B : Fo) : Prf B -> Prf (A -\/ B)
  | DisjE (A B C : Fo) : Prf (A -\/ B) -> Prf (A --> C) -> Prf (B --> C) -> Prf C.

(* ------------------------------------------------------------- *)
(* Deduction Identity: Prf (A --> A)                             *)
(* ------------------------------------------------------------- *)

Theorem prf_id : forall A : Fo, Prf (A --> A).
Proof.
  intro A.
  apply (MP (A --> (A --> A)) (A --> A)).
  - apply (MP (A --> ((A --> A) --> A)) ((A --> (A --> A)) --> (A --> A))).
    + apply AxS.
    + apply AxK.
  - apply AxK.
Qed.

(* ------------------------------------------------------------- *)
(* Soundness Theorem: Every provable formula is a tautology      *)
(* ------------------------------------------------------------- *)

Theorem soundness : forall f : Fo, Prf f -> isTauto f.
Proof.
  intros f Hprf.
  induction Hprf as [
    A B |
    A B C |
    A B |
    A B H_impl IH_impl H_A IH_A |
    A B H_A IH_A H_B IH_B |
    A B H_AB IH_AB |
    A B H_AB IH_AB |
    A B H_A IH_A |
    A B H_B IH_B |
    A B C H_AB IH_AB H_AC IH_AC H_BC IH_BC
  ].
  - (* AxK: A --> (B --> A) *)
    intro v.
    simpl.
    destruct (foIb v A); destruct (foIb v B); reflexivity.
  - (* AxS: (A --> (B --> C)) --> ((A --> B) --> (A --> C)) *)
    intro v.
    simpl.
    destruct (foIb v A); destruct (foIb v B); destruct (foIb v C); reflexivity.
  - (* AxContra: ((A --> Bot) --> (B --> Bot)) --> (B --> A) *)
    intro v.
    simpl.
    destruct (foIb v A); destruct (foIb v B); reflexivity.
  - (* Modus Ponens: Prf (A --> B) -> Prf A -> Prf B *)
    intro v.
    specialize (IH_impl v).
    specialize (IH_A v).
    simpl in IH_impl.
    rewrite IH_A in IH_impl.
    simpl in IH_impl.
    exact IH_impl.
  - (* ConjI: Prf A -> Prf B -> Prf (A -/\ B) *)
    intro v.
    specialize (IH_A v).
    specialize (IH_B v).
    simpl.
    rewrite IH_A, IH_B.
    reflexivity.
  - (* ConjEL: Prf (A -/\ B) -> Prf A *)
    intro v.
    specialize (IH_AB v).
    simpl in IH_AB.
    destruct (foIb v A); destruct (foIb v B); try reflexivity; discriminate IH_AB.
  - (* ConjER: Prf (A -/\ B) -> Prf B *)
    intro v.
    specialize (IH_AB v).
    simpl in IH_AB.
    destruct (foIb v A); destruct (foIb v B); try reflexivity; discriminate IH_AB.
  - (* DisjIL: Prf A -> Prf (A -\/ B) *)
    intro v.
    specialize (IH_A v).
    simpl.
    rewrite IH_A.
    reflexivity.
  - (* DisjIR: Prf B -> Prf (A -\/ B) *)
    intro v.
    specialize (IH_B v).
    simpl.
    rewrite IH_B.
    destruct (foIb v A); reflexivity.
  - (* DisjE: Prf (A -\/ B) -> Prf (A --> C) -> Prf (B --> C) -> Prf C *)
    intro v.
    specialize (IH_AB v).
    specialize (IH_AC v).
    specialize (IH_BC v).
    simpl in *.
    destruct (foIb v A); destruct (foIb v B); destruct (foIb v C);
      try reflexivity; try discriminate IH_AB; try discriminate IH_AC; discriminate IH_BC.
Qed.



