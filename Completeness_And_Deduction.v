(* ========================================================================= *)
(* Completeness_And_Deduction.v                                              *)
(* Constructive Hilbert Combinators, Syntactic Deduction Theorem,            *)
(* Classical Derived Rules (Ex Falso, DNE, Case Split, Peirce's Law), and    *)
(* Kalmar's Semantic Completeness Theorem extending Propositional.v          *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Require Import Propositional.

(* ------------------------------------------------------------------------- *)
(* 1. Derived Combinators in the Base Hilbert System Prf                     *)
(* ------------------------------------------------------------------------- *)

(** Negation abbreviation: ~A is (A --> Bot). *)
Definition Neg (A : Fo) : Fo := A --> Bot.

(** Constant combinator rule: from Prf B, infer Prf (A --> B). *)
Theorem prf_const : forall A B : Fo, Prf B -> Prf (A --> B).
Proof.
  intros A B HB.
  exact (MP B (A --> B) (AxK B A) HB).
Qed.

(** S-combinator Modus Ponens chain:
    from Prf (A --> (B --> C)) and Prf (A --> B), infer Prf (A --> C). *)
Theorem prf_mp_chain :
  forall A B C : Fo,
    Prf (A --> (B --> C)) ->
    Prf (A --> B) ->
    Prf (A --> C).
Proof.
  intros A B C H1 H2.
  apply (MP (A --> B) (A --> C)).
  - apply (MP (A --> (B --> C)) ((A --> B) --> (A --> C))).
    + apply AxS.
    + exact H1.
  - exact H2.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2. Contextual Hilbert Derivability PrfInCtx and Deduction Theorem         *)
(* ------------------------------------------------------------------------- *)

Inductive PrfInCtx (Gamma : list Fo) : Fo -> Prop :=
  | CtxHyp (A : Fo) : In A Gamma -> PrfInCtx Gamma A
  | CtxBase (A : Fo) : Prf A -> PrfInCtx Gamma A
  | CtxAxK (A B : Fo) : PrfInCtx Gamma (A --> (B --> A))
  | CtxAxS (A B C : Fo) :
      PrfInCtx Gamma ((A --> (B --> C)) --> ((A --> B) --> (A --> C)))
  | CtxAxContra (A B : Fo) :
      PrfInCtx Gamma (((A --> Bot) --> (B --> Bot)) --> (B --> A))
  | CtxMP (A B : Fo) :
      PrfInCtx Gamma (A --> B) -> PrfInCtx Gamma A -> PrfInCtx Gamma B.

Theorem ctx_id : forall (Gamma : list Fo) (A : Fo), PrfInCtx Gamma (A --> A).
Proof.
  intros Gamma A.
  apply CtxBase.
  apply prf_id.
Qed.

Theorem ctx_const :
  forall (Gamma : list Fo) (A B : Fo),
    PrfInCtx Gamma B -> PrfInCtx Gamma (A --> B).
Proof.
  intros Gamma A B HB.
  exact (CtxMP Gamma B (A --> B) (CtxAxK Gamma B A) HB).
Qed.

(** Monotonicity / Weakening of PrfInCtx under context inclusion. *)
Theorem PrfInCtx_weaken :
  forall (Gamma Delta : list Fo) (A : Fo),
    (forall X : Fo, In X Gamma -> In X Delta) ->
    PrfInCtx Gamma A ->
    PrfInCtx Delta A.
Proof.
  intros Gamma Delta A Hsub Hprf.
  induction Hprf as [X Hin | X Hbase | X Y | X Y Z | X Y | X Y H1 IH1 H2 IH2].
  - exact (CtxHyp Delta X (Hsub X Hin)).
  - exact (CtxBase Delta X Hbase).
  - exact (CtxAxK Delta X Y).
  - exact (CtxAxS Delta X Y Z).
  - exact (CtxAxContra Delta X Y).
  - exact (CtxMP Delta X Y IH1 IH2).
Qed.

(** Equivalence of empty-context derivability PrfInCtx [] and base Prf. *)
Theorem PrfInCtx_nil_iff : forall A : Fo, PrfInCtx [] A <-> Prf A.
Proof.
  intro A.
  split.
  - intro H.
    induction H as [X Hin | X Hbase | X Y | X Y Z | X Y | X Y H1 IH1 H2 IH2].
    + inversion Hin.
    + exact Hbase.
    + exact (AxK X Y).
    + exact (AxS X Y Z).
    + exact (AxContra X Y).
    + exact (MP X Y IH1 IH2).
  - intro H.
    exact (CtxBase [] A H).
Qed.

(** Syntactic Deduction Theorem for Propositional Hilbert Calculus:
    If B is derivable from (A :: Gamma), then (A --> B) is derivable from Gamma. *)
Theorem Deduction_Theorem :
  forall (Gamma : list Fo) (A B : Fo),
    PrfInCtx (A :: Gamma) B ->
    PrfInCtx Gamma (A --> B).
Proof.
  intros Gamma A B H.
  induction H as [X Hin | X Hbase | X Y | X Y Z | X Y | X Y H1 IH1 H2 IH2].
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst X.
      apply ctx_id.
    + apply ctx_const.
      exact (CtxHyp Gamma X Hin).
  - apply ctx_const.
    exact (CtxBase Gamma X Hbase).
  - apply ctx_const.
    exact (CtxAxK Gamma X Y).
  - apply ctx_const.
    exact (CtxAxS Gamma X Y Z).
  - apply ctx_const.
    exact (CtxAxContra Gamma X Y).
  - eapply CtxMP.
    + eapply CtxMP.
      * exact (CtxAxS Gamma A X Y).
      * exact IH1.
    + exact IH2.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3. Classical Derived Rules via the Deduction Theorem                      *)
(* ------------------------------------------------------------------------- *)

(** Hypothetical Syllogism: (A --> B) --> ((B --> C) --> (A --> C)). *)
Theorem prf_syllogism :
  forall A B C : Fo, Prf ((A --> B) --> ((B --> C) --> (A --> C))).
Proof.
  intros A B C.
  apply PrfInCtx_nil_iff.
  repeat apply Deduction_Theorem.
  (* Context is [A; B --> C; A --> B] *)
  eapply CtxMP.
  - apply CtxHyp; simpl; right; left; reflexivity.
  - eapply CtxMP.
    + apply CtxHyp; simpl; right; right; left; reflexivity.
    + apply CtxHyp; simpl; left; reflexivity.
Qed.

(** Ex Falso Quodlibet (Explosion): Bot --> A. *)
Theorem prf_ex_falso : forall A : Fo, Prf (Bot --> A).
Proof.
  intro A.
  apply PrfInCtx_nil_iff.
  apply Deduction_Theorem.
  (* Context: [Bot] *)
  eapply CtxMP.
  - eapply CtxMP.
    + exact (CtxAxContra [Bot] A Bot).
    + (* Show (A --> Bot) --> (Bot --> Bot) *)
      apply ctx_const.
      apply ctx_id.
  - apply CtxHyp; simpl; left; reflexivity.
Qed.

(** Double Negation Elimination (DNE): ((A --> Bot) --> Bot) --> A. *)
Theorem prf_dne : forall A : Fo, Prf (((A --> Bot) --> Bot) --> A).
Proof.
  intro A.
  apply PrfInCtx_nil_iff.
  apply Deduction_Theorem.
  (* Context: [(A --> Bot) --> Bot] *)
  eapply CtxMP.
  - eapply CtxMP.
    + exact (CtxAxContra [((A --> Bot) --> Bot)] A (Bot --> Bot)).
    + repeat apply Deduction_Theorem.
      (* Context: [Bot --> Bot; A --> Bot; (A --> Bot) --> Bot] *)
      eapply CtxMP.
      * apply CtxHyp; simpl; right; right; left; reflexivity.
      * apply CtxHyp; simpl; right; left; reflexivity.
  - apply ctx_id.
Qed.

(** Double Negation Introduction (DNI): A --> ((A --> Bot) --> Bot). *)
Theorem prf_dni : forall A : Fo, Prf (A --> ((A --> Bot) --> Bot)).
Proof.
  intro A.
  apply PrfInCtx_nil_iff.
  repeat apply Deduction_Theorem.
  (* Context: [A --> Bot; A] *)
  eapply CtxMP.
  - apply CtxHyp; simpl; left; reflexivity.
  - apply CtxHyp; simpl; right; left; reflexivity.
Qed.

(** Absurdity elimination: A --> ((A --> Bot) --> B). *)
Theorem prf_absurd : forall A B : Fo, Prf (A --> ((A --> Bot) --> B)).
Proof.
  intros A B.
  apply PrfInCtx_nil_iff.
  repeat apply Deduction_Theorem.
  (* Context: [A --> Bot; A] *)
  eapply CtxMP.
  - apply CtxBase; apply prf_ex_falso.
  - eapply CtxMP.
    + apply CtxHyp; simpl; left; reflexivity.
    + apply CtxHyp; simpl; right; left; reflexivity.
Qed.

(** Classical Case Split (Law of Excluded Middle elimination):
    (A --> B) --> (((A --> Bot) --> B) --> B). *)
Theorem prf_case_split :
  forall A B : Fo, Prf ((A --> B) --> (((A --> Bot) --> B) --> B)).
Proof.
  intros A B.
  apply PrfInCtx_nil_iff.
  repeat apply Deduction_Theorem.
  (* Context: [(A --> Bot) --> B; A --> B] *)
  eapply CtxMP.
  - apply CtxBase; apply prf_dne.
  - apply Deduction_Theorem.
    (* Context: [B --> Bot; (A --> Bot) --> B; A --> B] *)
    assert (HnA : PrfInCtx [B --> Bot; (A --> Bot) --> B; A --> B] (A --> Bot)).
    {
      apply Deduction_Theorem.
      (* Context: [A; B --> Bot; (A --> Bot) --> B; A --> B] *)
      eapply CtxMP.
      - apply CtxHyp; simpl; right; left; reflexivity.
      - eapply CtxMP.
        + apply CtxHyp; simpl; right; right; right; left; reflexivity.
        + apply CtxHyp; simpl; left; reflexivity.
    }
    eapply CtxMP.
    + apply CtxHyp; simpl; left; reflexivity.
    + eapply CtxMP.
      * apply CtxHyp; simpl; right; left; reflexivity.
      * exact HnA.
Qed.

(** Peirce's Law: ((A --> B) --> A) --> A. *)
Theorem prf_peirce_dne : forall A B : Fo, Prf (((A --> B) --> A) --> A).
Proof.
  intros A B.
  apply PrfInCtx_nil_iff.
  apply Deduction_Theorem.
  (* Context: [(A --> B) --> A] *)
  eapply CtxMP.
  - eapply CtxMP.
    + apply CtxBase; exact (prf_case_split A A).
    + apply ctx_id.
  - apply Deduction_Theorem.
    (* Context: [A --> Bot; (A --> B) --> A] *)
    eapply CtxMP.
    + apply CtxHyp; simpl; right; left; reflexivity.
    + apply Deduction_Theorem.
      (* Context: [A; A --> Bot; (A --> B) --> A] *)
      eapply CtxMP.
      * apply CtxBase; apply prf_ex_falso.
      * eapply CtxMP.
        -- apply CtxHyp; simpl; right; left; reflexivity.
        -- apply CtxHyp; simpl; left; reflexivity.
Qed.

(** Context Case Split Rule:
    If B is derivable from (A :: Gamma) and from ((A --> Bot) :: Gamma),
    then B is derivable from Gamma alone. *)
Theorem ctx_case_split :
  forall (Gamma : list Fo) (A B : Fo),
    PrfInCtx (A :: Gamma) B ->
    PrfInCtx ((A --> Bot) :: Gamma) B ->
    PrfInCtx Gamma B.
Proof.
  intros Gamma A B Hpos Hneg.
  apply Deduction_Theorem in Hpos.
  apply Deduction_Theorem in Hneg.
  eapply CtxMP.
  - eapply CtxMP.
    + apply CtxBase; exact (prf_case_split A B).
    + exact Hpos.
  - exact Hneg.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4. Kalmar's Truth-Table Simulation and Completeness Theorem               *)
(* ------------------------------------------------------------------------- *)

(** Predicate identifying the {Atom, Bot, Impl} fragment of Fo
    (for which AxK, AxS, AxContra, MP form a complete axiomatization). *)
Fixpoint is_imp_bot (f : Fo) : bool :=
  match f with
  | Atom _ => true
  | Bot => true
  | Impl f1 f2 => andb (is_imp_bot f1) (is_imp_bot f2)
  | _ => false
  end.

(** Extract the list of atomic variable indices occurring in f. *)
Fixpoint fo_vars (f : Fo) : list AtomVars :=
  match f with
  | Atom p => [p]
  | Bot => []
  | Conj f1 f2 => fo_vars f1 ++ fo_vars f2
  | Disj f1 f2 => fo_vars f1 ++ fo_vars f2
  | Impl f1 f2 => fo_vars f1 ++ fo_vars f2
  end.

(** Signed literal for atomic variable p under valuation v:
    Atom p if v p = true, or (Atom p --> Bot) if v p = false. *)
Definition signed_atom (v : Valuations) (p : AtomVars) : Fo :=
  if v p then Atom p else (Atom p --> Bot).

Definition literal_ctx (v : Valuations) (ps : list AtomVars) : list Fo :=
  map (signed_atom v) ps.

(** Helper: If f1 --> f2 has f2 derivable in Gamma, then (f1 --> f2) is derivable. *)
Theorem imp_true_r :
  forall (Gamma : list Fo) (f1 f2 : Fo),
    PrfInCtx Gamma f2 ->
    PrfInCtx Gamma (f1 --> f2).
Proof.
  intros Gamma f1 f2 H2.
  exact (ctx_const Gamma f1 f2 H2).
Qed.

(** Helper: If (f1 --> Bot) is derivable in Gamma, then (f1 --> f2) is derivable. *)
Theorem imp_false_l :
  forall (Gamma : list Fo) (f1 f2 : Fo),
    PrfInCtx Gamma (f1 --> Bot) ->
    PrfInCtx Gamma (f1 --> f2).
Proof.
  intros Gamma f1 f2 Hn1.
  apply Deduction_Theorem.
  eapply CtxMP.
  - apply CtxBase; apply prf_ex_falso.
  - eapply CtxMP.
    + apply (PrfInCtx_weaken Gamma (f1 :: Gamma)).
      * intros X HX; right; exact HX.
      * exact Hn1.
    + apply CtxHyp; simpl; left; reflexivity.
Qed.

(** Helper: If f1 and (f2 --> Bot) are derivable in Gamma,
    then ((f1 --> f2) --> Bot) is derivable in Gamma. *)
Theorem imp_true_false :
  forall (Gamma : list Fo) (f1 f2 : Fo),
    PrfInCtx Gamma f1 ->
    PrfInCtx Gamma (f2 --> Bot) ->
    PrfInCtx Gamma ((f1 --> f2) --> Bot).
Proof.
  intros Gamma f1 f2 H1 Hn2.
  apply Deduction_Theorem.
  eapply CtxMP.
  - apply (PrfInCtx_weaken Gamma ((f1 --> f2) :: Gamma)).
    + intros X HX; right; exact HX.
    + exact Hn2.
  - eapply CtxMP.
    + apply CtxHyp; simpl; left; reflexivity.
    + apply (PrfInCtx_weaken Gamma ((f1 --> f2) :: Gamma)).
      * intros X HX; right; exact HX.
      * exact H1.
Qed.

(** Kalmar's Truth-Value Simulation Lemma:
    For any formula f in the {Atom, Bot, Impl} fragment, any valuation v, and any
    context Gamma containing signed_atom v p for every atom p of f:
    - if foIb v f = true,  then PrfInCtx Gamma f
    - if foIb v f = false, then PrfInCtx Gamma (f --> Bot). *)
Theorem kalmar_eval_simulation :
  forall (f : Fo) (v : Valuations) (Gamma : list Fo),
    is_imp_bot f = true ->
    (forall p : AtomVars, In p (fo_vars f) -> In (signed_atom v p) Gamma) ->
    if foIb v f then PrfInCtx Gamma f else PrfInCtx Gamma (f --> Bot).
Proof.
  induction f as [p | | f1 IH1 f2 IH2 | f1 IH1 f2 IH2 | f1 IH1 f2 IH2];
    intros v Gamma Himp Hctx; simpl in *.
  - (* Atom p *)
    specialize (Hctx p (or_introl eq_refl)).
    unfold signed_atom in Hctx.
    destruct (v p).
    + exact (CtxHyp Gamma (Atom p) Hctx).
    + exact (CtxHyp Gamma (Atom p --> Bot) Hctx).
  - (* Bot *)
    apply ctx_id.
  - (* Conj: excluded by is_imp_bot *)
    discriminate Himp.
  - (* Disj: excluded by is_imp_bot *)
    discriminate Himp.
  - (* Impl f1 f2 *)
    apply andb_true_iff in Himp.
    destruct Himp as [Himp1 Himp2].
    assert (Hctx1 : forall p, In p (fo_vars f1) -> In (signed_atom v p) Gamma).
    {
      intros p Hp. apply Hctx. apply in_or_app. left; exact Hp.
    }
    assert (Hctx2 : forall p, In p (fo_vars f2) -> In (signed_atom v p) Gamma).
    {
      intros p Hp. apply Hctx. apply in_or_app. right; exact Hp.
    }
    specialize (IH1 v Gamma Himp1 Hctx1).
    specialize (IH2 v Gamma Himp2 Hctx2).
    destruct (foIb v f1) eqn:E1; destruct (foIb v f2) eqn:E2; simpl.
    + (* true, true => true *)
      exact (imp_true_r Gamma f1 f2 IH2).
    + (* true, false => false *)
      exact (imp_true_false Gamma f1 f2 IH1 IH2).
    + (* false, true => true *)
      exact (imp_true_r Gamma f1 f2 IH2).
    + (* false, false => true *)
      exact (imp_false_l Gamma f1 f2 IH1).
Qed.

(** Update a valuation at variable p with boolean b. *)
Definition update_val (v : Valuations) (p : AtomVars) (b : bool) : Valuations :=
  fun q => if Nat.eqb q p then b else v q.

Theorem signed_atom_update_true :
  forall (v : Valuations) (p : AtomVars),
    signed_atom (update_val v p true) p = Atom p.
Proof.
  intros v p.
  unfold signed_atom, update_val.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem signed_atom_update_false :
  forall (v : Valuations) (p : AtomVars),
    signed_atom (update_val v p false) p = (Atom p --> Bot).
Proof.
  intros v p.
  unfold signed_atom, update_val.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem signed_atom_irrel :
  forall (v : Valuations) (p q : AtomVars) (b : bool),
    q <> p ->
    signed_atom (update_val v p b) q = signed_atom v q.
Proof.
  intros v p q b Hneq.
  unfold signed_atom, update_val.
  destruct (Nat.eqb_spec q p) as [Heq | _].
  - exfalso; exact (Hneq Heq).
  - reflexivity.
Qed.

Theorem literal_ctx_irrel :
  forall (ps : list AtomVars) (v : Valuations) (p : AtomVars) (b : bool),
    ~ In p ps ->
    literal_ctx (update_val v p b) ps = literal_ctx v ps.
Proof.
  induction ps as [| q ps IH]; intros v p b Hnin; simpl.
  - reflexivity.
  - simpl in Hnin.
    assert (Hq : q <> p) by (intro Heq; apply Hnin; left; exact Heq).
    assert (Hps : ~ In p ps) by (intro Hin; apply Hnin; right; exact Hin).
    rewrite (signed_atom_irrel v p q b Hq).
    rewrite (IH v p b Hps).
    reflexivity.
Qed.

(** Variable Elimination Lemma by Induction on the Variable List ps:
    If for every valuation v, PrfInCtx (literal_ctx v ps ++ Gamma) f holds,
    then PrfInCtx Gamma f holds! *)
Theorem kalmar_eliminate_vars :
  forall (ps : list AtomVars) (Gamma : list Fo) (f : Fo),
    (forall v : Valuations, PrfInCtx (literal_ctx v ps ++ Gamma) f) ->
    PrfInCtx Gamma f.
Proof.
  induction ps as [| p ps IH]; intros Gamma f Hall.
  - (* ps = [] *)
    exact (Hall (fun _ => true)).
  - (* ps = p :: ps *)
    apply IH.
    intro v.
    destruct (in_dec Nat.eq_dec p ps) as [Hin | Hnin].
    + (* p already occurs in ps, so signed_atom v p is already in literal_ctx v ps *)
      eapply PrfInCtx_weaken.
      2: exact (Hall v).
      intros X HX.
      simpl in HX.
      destruct HX as [Heq | HX].
      * subst X.
        apply in_or_app.
        left.
        unfold literal_ctx.
        apply in_map.
        exact Hin.
      * exact HX.
    + (* p does not occur in ps: case-split on Atom p vs (Atom p --> Bot) *)
      apply (ctx_case_split (literal_ctx v ps ++ Gamma) (Atom p) f).
      * (* Positive branch: Atom p *)
        pose proof (Hall (update_val v p true)) as Hpos.
        simpl in Hpos.
        rewrite (signed_atom_update_true v p) in Hpos.
        rewrite (literal_ctx_irrel ps v p true Hnin) in Hpos.
        exact Hpos.
      * (* Negative branch: Atom p --> Bot *)
        pose proof (Hall (update_val v p false)) as Hneg.
        simpl in Hneg.
        rewrite (signed_atom_update_false v p) in Hneg.
        rewrite (literal_ctx_irrel ps v p false Hnin) in Hneg.
        exact Hneg.
Qed.

(** Kalmar's Semantic Completeness Theorem:
    Every tautology in the {Atom, Bot, Impl} fragment is provable in Prf! *)
Theorem kalmar_completeness :
  forall f : Fo,
    is_imp_bot f = true ->
    isTauto f ->
    Prf f.
Proof.
  intros f Himp Htauto.
  apply PrfInCtx_nil_iff.
  apply (kalmar_eliminate_vars (fo_vars f) [] f).
  intro v.
  rewrite app_nil_r.
  pose proof (kalmar_eval_simulation f v (literal_ctx v (fo_vars f)) Himp) as Hsim.
  rewrite (Htauto v) in Hsim.
  apply Hsim.
  intros p Hp.
  unfold literal_ctx.
  apply in_map.
  exact Hp.
Qed.

(** Full Soundness and Completeness Equivalence:
    For any formula f in the {Atom, Bot, Impl} fragment,
    Prf f holds if and only if f is a tautology (isTauto f). *)
Theorem soundness_and_completeness_iff :
  forall f : Fo,
    is_imp_bot f = true ->
    (Prf f <-> isTauto f).
Proof.
  intros f Himp.
  split.
  - apply soundness.
  - apply (kalmar_completeness f Himp).
Qed.
