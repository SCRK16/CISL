From Coq Require Export Strings.String.
From iris.proofmode Require Import tactics.
Require Import Lang.

(*
Immediate unsafe: An expression is immediately unsafe if:
  1. It is not a value
  2. None of the subexpressions within it can step
*)

Definition imm_unsafe (e : expr) (h : heap) :=
  ¬ is_val e /\ ¬ is_lock e /\ forall e' h', ¬ step e h e' h'.

Definition is_error (e : expr) (h : heap) :=
  exists k e', ctx k /\ e = k e' /\ imm_unsafe e' h.

Lemma unsafe_is_error e h : imm_unsafe e h -> is_error e h.
Proof.
  intros ?. exists (fun x => x), e. do 2 try split; eauto with context.
Qed.

Lemma unsafe_ctx_is_error k e h :
  ctx k ->
  imm_unsafe e h ->
  is_error (k e) h.
Proof.
  intros ??. by exists k, e.
Qed.

Lemma is_error_ctx k e h :
  ctx k ->
  is_error e h ->
  is_error (k e) h.
Proof.
  intros Hctx Herr.
  destruct Herr as (k' & e' & Hctx' & -> & Herr).
  induction Hctx.
  - exists k', e'. by do 2 try split.
  - destruct IHHctx as (k'' & e'' & Hctx'' & -> & Herr'').
    exists (fun x => k1 (k'' x)), e''. do 2 try split; try done. by apply Compose_ctx.
Qed.

Lemma val_not_error v h :
  ~ is_error (EVal v) h.
Proof.
  intros (k & e' & Hctx & Heq & Hunsafe).
  symmetry in Heq.
  apply (context_EVal _ _ _ Hctx) in Heq as [-> ->].
  destruct Hunsafe as [Hval _].
  by apply Hval.
Qed.



(* Notation for triples *)

Definition IL (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  forall v h', Q v h' -> exists h, P h /\ steps e h (EVal v) h'.

Definition ILERR (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall h', Q h' -> exists e' h, P h /\ steps e h e' h' /\ is_error e' h'.

Definition ISL (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  forall R, IL (P ∗ R)%S e (fun v => Q v ∗ R)%S.

Definition ISLERR (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall R, ILERR (P ∗ R)%S e (Q ∗ R)%S.

Definition is_error_or_val (e : expr) (h : heap) (mv : option val) : Prop :=
  match mv with
  | Some v => e = EVal v
  | None => is_error e h
  end.

Definition IL_Gen (P : iProp) (e : expr) (Q : option val -> iProp) : Prop :=
  forall mv h', Q mv h' -> exists e' h, P h /\ steps e h e' h' /\ is_error_or_val e' h' mv.

Definition ISL_Gen (P : iProp) (e : expr) (Q : option val -> iProp) : Prop :=
  forall R, IL_Gen (P ∗ R)%S e (fun mv => Q mv ∗ R)%S.


Definition to_option_some (Q : val -> iProp) : option val -> iProp :=
  fun mv => match mv with
  | Some v => Q v
  | None => (@[False])%S
  end.

Definition to_option_none (Q : iProp) : option val -> iProp :=
  fun mv => match mv with
  | Some v => (@[False])%S
  | None => Q
  end.

Definition from_option_some (Q : option val -> iProp) : val -> iProp :=
  fun v => Q (Some v).

Definition from_option_none (Q : option val -> iProp) : iProp :=
  Q None.

Definition ISL' (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  ISL_Gen P e (to_option_some Q).

Definition ISLERR' (P : iProp) (e : expr) (Q : iProp) : Prop :=
  ISL_Gen P e (to_option_none Q).

Lemma to_from_some_id (Q : val -> iProp) :
  from_option_some (to_option_some Q) = Q.
Proof.
  reflexivity.
Qed.

Lemma not_pure_false (h : heap) :
  ¬ @[False]%S h.
Proof.
  unfold iPure. tauto.
Qed.

Lemma pure_false_frame_equiv R h : @[False]%S h ↔ (@[False] ∗ R)%S h.
Proof.
  split.
  - intros H. by apply not_pure_false in H.
  - intros (m1 & m2 & H & _ & _ & _).
    by apply not_pure_false in H.
Qed.

Lemma to_option_some_equiv (Q : val -> iProp) (R : iProp) v h:
  to_option_some (λ v : val, (Q v ∗ R)%S) v h <-> (to_option_some Q v ∗ R)%S h.
Proof.
  destruct v as [v|]; [done|]. simpl.
  apply pure_false_frame_equiv.
Qed.

Lemma to_option_none_equiv (Q R : iProp) v h:
  to_option_none (Q ∗ R)%S v h <-> (to_option_none Q v ∗ R)%S h.
Proof.
  destruct v as [v|]; [|done]. simpl.
  apply pure_false_frame_equiv.
Qed.

Lemma IL_Gen_equiv (P : iProp) (e : expr) (Q : val -> iProp) :
  IL P e Q <-> IL_Gen P e (to_option_some Q).
Proof.
  split.
  - intros H mv h' HQ.
    destruct mv as [v|].
    + destruct (H v h' HQ) as [h [HP HSteps]].
      by exists (EVal v), h.
    + by apply not_pure_false in HQ.
  - intros H v h' HQ.
    destruct (H (Some v) h' HQ) as (e' & h & HP & Hsteps & Hval).
    exists h. by rewrite Hval in Hsteps.
Qed.

Lemma ISL_Gen_equiv (P : iProp) (e : expr) (Q : val -> iProp) :
  ISL P e Q <-> ISL_Gen P e (to_option_some Q).
Proof.
  split.
  - intros H R. specialize (H R).
    rewrite IL_Gen_equiv in H.
    intros mv h'.
    rewrite <- to_option_some_equiv.
    by revert mv h'.
  - intros H R. specialize (H R).
    rewrite IL_Gen_equiv.
    intros mv h'.
    rewrite to_option_some_equiv.
    by revert mv h'.
Qed.

Lemma ILERR_Gen_equiv (P : iProp) (e : expr) (Q : iProp) :
  ILERR P e Q <-> IL_Gen P e (to_option_none Q).
Proof.
  split.
  - intros H mv h' HQ.
    destruct mv as [v|].
    + by apply not_pure_false in HQ.
    + destruct (H h' HQ) as (e' & h & HP & Hsteps & Herr).
      by exists e', h.
  - intros H h' HQ.
    destruct (H None h' HQ) as (e' & h & HP & Hsteps & Herr).
    by exists e', h.
Qed.

Lemma ISLERR_Gen_equiv (P : iProp) (e : expr) (Q : iProp) :
  ISLERR P e Q <-> ISL_Gen P e (to_option_none Q).
Proof.
  split.
  - intros H R. specialize (H R).
    rewrite ILERR_Gen_equiv in H.
    intros mv h'.
    rewrite <- to_option_none_equiv.
    by revert mv h'.
  - intros H R. specialize (H R).
    rewrite ILERR_Gen_equiv.
    intros mv h'.
    rewrite to_option_none_equiv.
    by revert mv h'.
Qed.

Lemma IL_Gen_equiv_total (P : iProp) (e : expr) (Q : option val -> iProp) :
  IL_Gen P e Q <-> IL P e (from_option_some Q) /\ ILERR P e (from_option_none Q).
Proof.
  split.
  - intros H. split.
    + rewrite IL_Gen_equiv.
      intros [v|] h' HQ; [eauto|].
      by apply not_pure_false in HQ.
    + rewrite ILERR_Gen_equiv.
      intros [v|] h' HQ; [|eauto].
      by apply not_pure_false in HQ.
  - intros [HSome HNone] mv h' HQ.
    rewrite IL_Gen_equiv in HSome.
    rewrite ILERR_Gen_equiv in HNone.
    destruct mv as [v|]; eauto.
Qed.

Lemma ISL_Gen_equiv_total (P : iProp) (e : expr) (Q : option val -> iProp) :
  ISL_Gen P e Q <-> ISL P e (from_option_some Q) /\ ISLERR P e (from_option_none Q).
Proof.
  split.
  - intros H. unfold ISL_Gen in H. split;
    intros R; specialize (H R);
    rewrite IL_Gen_equiv_total in H; tauto.
  - intros [HSome HNone] R.
    rewrite IL_Gen_equiv_total.
    eauto.
Qed.

Lemma ISLERR_false P e :
  ISLERR P e @[False]%S.
Proof.
  intros ? ? Q.
  rewrite <- pure_false_frame_equiv in Q.
  by apply not_pure_false in Q.
Qed.

Lemma ISL_Gen_equiv' (P : iProp) (e : expr) (Q : val -> iProp) :
  ISL P e Q <-> ISL_Gen P e (to_option_some Q).
Proof.
  rewrite ISL_Gen_equiv_total.
  rewrite to_from_some_id.
  split.
  - intros H.
    split; [done|].
    apply ISLERR_false.
  - by intros [H _].
Qed.

Notation "[[[ P ]]] e [[[ v , Q ]]]" := (ISL P%S e (λ v , Q%S))
    (at level 20, e, P at level 200, Q at level 200, only parsing).
Notation "[[[ P ]]] e [[[ Q ]]]" := (ISL P%S e Q%S)
    (at level 20, e, P at level 200, Q at level 200, only parsing).
Notation "[[[ P ]]] e [[[ERR: Q ]]]" := (ISLERR P%S e Q%S)
  (at level 20, e, P at level 200, Q at level 200, only parsing).

Lemma ISL_val (v : val) : [[[ emp ]]] EVal v [[[ x, @[ x = v] ]]].
Proof.
  intros R v' h' HP.
  exists h'. inversion HP. destruct H as (h2 & [-> ->] & HR & -> & Hx).
  split.
  - by exists empty, h2.
  - apply steps_refl.
Qed.

(* Context rules *)

Lemma IL_context_all (P : iProp) (Q R : val -> iProp) e k :
  ctx k ->
  IL P e Q ->
  (forall v, IL (Q v) (k (EVal v)) R) ->
  IL P (k e) R.
Proof.
  intros Hk HPeQ HQkR v h3 HR.
  destruct (HQkR v v h3 HR) as (h2 & HQ & Hsteps).
  destruct (HPeQ v h2 HQ) as (h1 & HP & Hsteps').
  exists h1. split; [assumption|].
  by eapply steps_context.
Qed.

Lemma ISL_context_all (P : iProp) (Q R : val -> iProp) e k :
  ctx k ->
  [[[ P ]]] e [[[ Q ]]] ->
  (forall v, [[[ Q v ]]] k (EVal v) [[[ R ]]]) ->
  [[[ P ]]] k e [[[ R ]]].
Proof.
  intros Hk HPeQ HQkR W.
  eapply IL_context_all; try done.
  intros v.
  exact (HQkR v W).
Qed.

Lemma IL_context (P : iProp) (Q R : val -> iProp) e k :
  ctx k ->
  IL P e Q ->
  (exists v, IL (Q v) (k (EVal v)) R) ->
  IL P (k e) R.
Proof.
  intros Hk HPeQ HQkR v h3 HR.
  destruct HQkR as (v' & h2 & HQ & Hsteps); [done|].
  destruct (HPeQ v' h2 HQ) as (h1 & HP & Hsteps').
  exists h1. split; [done|].
  by eapply steps_context.
Qed.

Lemma ISL_context (P : iProp) (Q R : val -> iProp) e k :
  ctx k ->
  [[[ P ]]] e [[[ Q ]]] ->
  (exists v, [[[ Q v ]]] k (EVal v) [[[ R ]]]) ->
  [[[ P ]]] k e [[[ R ]]].
Proof.
  intros Hk HPeQ HQkR W.
  eapply IL_context; try done.
  destruct HQkR as [v HQkR]. exists v.
  exact (HQkR W).
Qed.

Lemma ILERR_context (P Q : iProp) e k :
  ctx k ->
  ILERR P e Q ->
  ILERR P (k e) Q.
Proof.
  intros Hctx H h' HQ.
  destruct (H h' HQ) as (e' & h & HP & Hsteps & (k' & es & Hctx' & Heq & Herr)).
  exists (k e'), h. repeat split; [done | | ].
  - by apply steps_context_steps.
  - simplify_eq. do 2 (apply is_error_ctx; [done|]). by apply unsafe_is_error.
Qed.

Lemma ISLERR_context (P Q : iProp) e k :
  ctx k ->
  [[[ P ]]] e [[[ERR: Q ]]] ->
  [[[ P ]]] (k e) [[[ERR: Q ]]].
Proof.
  intros Hctx H R.
  by apply ILERR_context.
Qed.

Lemma ISLERR_context_ISL (P Q : iProp) (R : val -> iProp) e v k :
  ctx k ->
  [[[ P ]]] e [[[ x, @[x = v] ∗ R x]]] ->
  [[[ R v ]]] k (EVal v) [[[ERR: Q ]]] ->
  [[[ P ]]] k e [[[ERR: Q ]]].
Proof.
  intros Hctx HPR HRQ W h' HQ.
  destruct (HRQ W h' HQ) as (e' & h & Hh & Hsteps & Herr).
  destruct (HPR W v h) as (h0 & Hh0 & Hsteps0).
  - destruct Hh as (h1 & h2 & H1 & H2 & -> & Hdisj).
    exists h1, h2. repeat split; try done.
    exists ∅, h1. repeat split; try done.
    + by rewrite left_id.
    + solve_map_disjoint.
  - exists e', h0. repeat split; try done.
    eapply steps_trans; [|done].
    by  eapply steps_context_steps.
Qed.

(* Cons rules *)

Lemma IL_cons (P P' : iProp) (Q Q' : val -> iProp) e :
  (P' ⊢ P)%S ->
  (forall v, (Q v  ⊢ Q' v)%S) ->
  IL P' e Q' ->
  IL P e Q.
Proof.
  intros HP HQ H' v h' HQvh.
  assert (HQ' : Q' v h') by (by apply HQ).
  destruct (H' v h' HQ') as (h & HP' & Hsteps).
  exists h. split; [|done].
  by apply HP.
Qed.

Lemma ISL_cons (P P' : iProp) (Q Q' : val -> iProp) e :
  (P' ⊢ P)%S ->
  (forall v, (Q v  ⊢ Q' v)%S) ->
  [[[ P' ]]] e [[[ Q' ]]] ->
  [[[ P ]]] e [[[ Q ]]].
Proof.
  intros HP HQ H' R. specialize (H' R).
  eapply IL_cons; [| intros v | done]; simpl; eauto with seplogic.
Qed.

Lemma ISL_IL P e Q : [[[ P ]]] e [[[ Q ]]] -> IL P e Q.
Proof.
  intros H.
  specialize (H (emp)%S).
  eapply IL_cons; [| intros v | done]; simpl; eauto with seplogic.
Qed.

Lemma ILERR_cons (P P' Q Q' : iProp) e :
  (P' ⊢ P)%S ->
  (Q ⊢ Q')%S ->
  ILERR P' e Q' ->
  ILERR P e Q.
Proof.
  intros HP' HQ' HIL h' HQ.
  destruct (HIL h' (HQ' h' HQ)) as (e' & h & HPh & Hsteps & Herr).
  exists e', h. eauto.
Qed.

Lemma ISLERR_cons (P P' Q Q' : iProp) e :
  (P' ⊢ P)%S ->
  (Q ⊢ Q')%S ->
  [[[ P' ]]] e [[[ERR: Q' ]]] ->
  [[[ P ]]] e [[[ERR: Q ]]].
Proof.
  intros ????.
  eauto using ILERR_cons, iSep_mono_l.
Qed.

Lemma ISL_sep_assoc_post (P Q2 Q3 : iProp) (Q1 : val -> iProp) e :
  [[[ P ]]] e [[[ x, (Q1 x ∗ Q2) ∗ Q3 ]]] ->
  [[[ P ]]] e [[[ x, Q1 x ∗ Q2 ∗ Q3 ]]].
Proof.
  intros HISL.
  eapply ISL_cons; [apply iEntails_refl | |done].
  intros v. simpl. apply iSep_assoc.
Qed.

Lemma ISL_sep_assoc'_post (P Q2 Q3 : iProp) (Q1 : val -> iProp) e :
  [[[ P ]]] e [[[ x, Q1 x ∗ Q2 ∗ Q3 ]]] ->
  [[[ P ]]] e [[[ x, (Q1 x ∗ Q2) ∗ Q3 ]]].
Proof.
  intros HISL.
  eapply ISL_cons; [apply iEntails_refl | |done].
  intros v. simpl. apply iSep_assoc'.
Qed.

Lemma ISL_sep_assoc_pre (P1 P2 P3 : iProp) (Q : val -> iProp) e :
  [[[ P1 ∗ P2 ∗ P3 ]]] e [[[ Q ]]] ->
  [[[ (P1 ∗ P2) ∗ P3 ]]] e [[[ Q ]]].
Proof.
  intros H. eapply ISL_cons;
  [| intros v; apply iEntails_refl | done].
  apply iSep_assoc.
Qed.

(* Alternative ISLERR_context_ISL rule *)
Lemma ISLERR_context_ISL_exists (P Q : iProp) (R : val -> iProp) e k :
  ctx k ->
  [[[ P ]]] e [[[ R ]]] ->
  (exists v, [[[ R v ]]] k (EVal v) [[[ERR: Q ]]]) ->
  [[[ P ]]] k e [[[ERR: Q ]]].
Proof.
  intros Hctx HPR [v HRQ].
  eapply ISLERR_context_ISL; [done |  | done].
  eapply ISL_cons; eauto using iPure_elim, iEntails_refl.
Qed.

(* Frame rules *)

Lemma ISL_frame (R P : iProp) (Q : val -> iProp) e :
  [[[ P ]]] e [[[ Q ]]] ->
  [[[ P ∗ R ]]] e [[[ x, Q x ∗ R ]]].
Proof.
  intros HPQ T v h' HQRT.
  apply iSep_assoc' in HQRT.
  specialize (HPQ (R ∗ T)%S v h' HQRT).
  destruct HPQ as (h & HPRT & Hsteps).
  exists h. split; by [apply iSep_assoc |].
Qed.

Lemma ISL_frame' (R : iProp) (Q : val -> iProp) e :
  [[[ emp ]]] e [[[ Q ]]] ->
  [[[ R ]]] e [[[ x, Q x ∗ R ]]].
Proof.
  intros H.
  eapply ISL_cons.
  3: { eapply ISL_frame with (R := R), H. }
  - apply iSep_emp_l_inv.
  - eauto using iEntails_refl.
Qed.

Lemma ISL_frame_left (R P : iProp) (Q : val -> iProp) e :
  [[[ P ]]] e [[[ Q ]]] ->
  [[[ R ∗ P ]]] e [[[ x, R ∗ Q x ]]].
Proof.
  intros HPQ.
  apply (ISL_cons _ (P ∗ R) _ (fun x => Q x ∗ R)%S).
  - apply iSep_comm.
  - intros v. apply iSep_comm.
  - by apply ISL_frame.
Qed.

Lemma ISLERR_frame (R P Q : iProp) e :
  [[[ P ]]] e [[[ERR: Q ]]] ->
  [[[ P ∗ R ]]] e [[[ERR: Q ∗ R ]]].
Proof.
  intros HPQ T.
  specialize (HPQ (R ∗ T)%S).
  eapply ILERR_cons; [ | | done]; eauto with seplogic.
Qed.

Lemma ISLERR_frame_left (R P Q : iProp) e :
  [[[ P ]]] e [[[ERR: Q ]]] ->
  [[[ R ∗ P ]]] e [[[ERR: R ∗ Q ]]].
Proof.
  intros HPQ.
  apply (ISLERR_cons _ (P ∗ R) _ (Q ∗ R)).
  - apply iSep_comm.
  - intros v. apply iSep_comm.
  - by apply ISLERR_frame.
Qed. 

(* Step rules *)

Lemma ISL_pure_step (P : iProp) (Q : val -> iProp) e e' :
  [[[ P ]]] e' [[[ Q ]]] ->
  pure_step e e' ->
  [[[ P ]]] e [[[ Q ]]].
Proof.
  intros HPQ Hstep W v h Hh.
  destruct (HPQ W v h Hh) as (h' & Hh' & Hsteps).
  exists h'. split; [done|].
  eapply steps_step; [|done].
  eauto with headstep.
Qed.

Lemma ISL_pure_step_context (P : iProp) (Q : val -> iProp) e e' k :
  ctx k ->
  [[[ P ]]] k e' [[[ Q ]]] ->
  pure_step e e' ->
  [[[ P ]]] k e [[[ Q ]]].
Proof.
  intros Hctx HPQ Hstep W v h Hh.
  destruct (HPQ W v h Hh) as (h' & Hh' & Hsteps).
  exists h'. split; [done|].
  eapply steps_step; [|done].
  apply do_step; by [|constructor].
Qed.

Lemma ISLERR_pure_step (P Q : iProp) e e' :
  [[[ P ]]] e' [[[ERR: Q ]]] ->
  pure_step e e' ->
  [[[ P ]]] e [[[ERR: Q ]]].
Proof.
  intros HPQ Hstep W h Hh.
  destruct (HPQ W h Hh) as (e0 & h0 & Hh0 & Hsteps & Herr).
  exists e0, h0. do 2 try split; [done | | done].
  eapply steps_step; [|done].
  eauto with headstep.
Qed.

Lemma ISLERR_pure_step_context (P Q : iProp) e e' k :
  ctx k ->
  [[[ P ]]] k e' [[[ERR: Q ]]] ->
  pure_step e e' ->
  [[[ P ]]] k e [[[ERR: Q ]]].
Proof.
  intros Hctx HPQ Hstep W h Hh.
  destruct (HPQ W h Hh) as (e0 & h0 & Hh0 & Hsteps & Herr).
  exists e0, h0. do 2 try split; [done | | done].
  eapply steps_step; [|done].
  apply do_step; by [|constructor].
Qed.

(* Quantifier rules *)
Lemma ISL_exists_post {A} (P : iProp) (Q : A -> val -> iProp) e :
  (forall s, [[[ P ]]] e [[[ Q s ]]]) ->
  [[[ P ]]] e [[[ x, ∃ s, Q s x ]]].
Proof.
  intros H R v h' (h1 & h2 & [s Hs] & H2 & -> & Hdisj).
  apply (H s R v). by exists h1, h2.
Qed.

(* Disjunction rules *)

(* Change to [P] e [Q1] -> [P] e [Q2] -> [P] e [Q1 \/ Q2] *)

Lemma IL_disj (P P' : iProp) (Q Q' : val -> iProp) e :
  IL P e Q ->
  IL P' e Q' ->
  IL (P ∨ P')%S e (fun x => Q x ∨ Q' x)%S.
Proof.
  intros H H' v h' [HQ | HQ];
  [destruct (H v h' HQ) as (h & HP & Hsteps) | destruct (H' v h' HQ) as (h & HP & Hsteps)];
  exists h; split; try done; by [left | right].
Qed.

Lemma ISL_disj (P P' : iProp) (Q Q' : val -> iProp) e :
  [[[ P ]]] e [[[ Q ]]] ->
  [[[ P' ]]] e [[[ Q' ]]] ->
  [[[ P ∨ P' ]]] e [[[ x, Q x ∨ Q' x ]]].
Proof.
  intros H H' R.
  eapply IL_cons.
  3: { apply IL_disj; [apply H | apply H']. }
  2: intros v; simpl.
  1,2: eauto using iOr_distr, iOr_distr'.
Qed.

Lemma ILERR_disj (P P' Q Q' : iProp) e :
  ILERR P e Q ->
  ILERR P' e Q' ->
  ILERR (P ∨ P')%S e (Q ∨ Q')%S.
Proof.
  intros H H' h' [HQ | HQ'];
  [ destruct (H h' HQ) as (e' & h & HP & Hsteps & Herr)
  | destruct (H' h' HQ') as (e' & h & HP & Hsteps & Herr) ];
  exists e', h; split; eauto; by [left | right].
Qed.

Lemma ISLERR_disj (P P' Q Q' : iProp) e :
  [[[ P ]]] e [[[ERR: Q ]]] ->
  [[[ P' ]]] e [[[ERR: Q' ]]] ->
  [[[ P ∨ P' ]]] e [[[ERR: Q ∨ Q' ]]].
Proof.
  intros H H' R.
  eapply ILERR_cons; eauto using iOr_distr, iOr_distr'.
  eauto using ILERR_disj.
Qed.

(* Pure rules *)

Lemma ISL_pure (P : iProp) (Q : val -> iProp) (phi : Prop) e :
  (phi -> [[[ P ]]] e [[[ Q ]]]) ->
  [[[ P ]]] e [[[ x, @[phi] ∗ Q x ]]].
Proof.
  intros H R v h (h' & hR & (h0 & hQ & [Hphi ->] & HQ & -> & Hdisj') & HR & -> & Hdisj).
  rewrite left_id. rewrite left_id in Hdisj.
  destruct (H Hphi R v (hQ ∪ hR)) as (h & HP & Hsteps); [exists hQ, hR|]; eauto.
Qed.

Lemma ISL_pure' (P : iProp) (Q : val -> iProp) (phi : val -> Prop) e :
  ((exists x, phi x) -> [[[ P ]]] e [[[ Q ]]]) ->
  [[[ P ]]] e [[[ x, @[phi x] ∗ Q x ]]].
Proof.
  intros H R v h (h' & hR & (h0 & hQ & [Hphi ->] & HQ & -> & Hdisj') & HR & -> & Hdisj).
  rewrite left_id. rewrite left_id in Hdisj.
  destruct (H (ex_intro _ _ Hphi) R v (hQ ∪ hR)) as (h & HP & Hsteps); [exists hQ, hR|]; eauto.
Qed.

Lemma ISLERR_pure (P Q : iProp) (phi : Prop) e :
  (phi -> [[[ P ]]] e [[[ERR: Q ]]]) ->
  [[[ P ]]] e [[[ERR: @[phi] ∗ Q ]]].
Proof.
  intros H R h (h' & hR & (h0 & hQ & [Hphi ->] & HQ & -> & Hdisj') & HR & -> & Hdisj).
  rewrite left_id. rewrite left_id in Hdisj.
  destruct (H Hphi R (hQ ∪ hR)) as (h & HP & Hsteps); [exists hQ, hR|]; eauto.
Qed.

(* EAmb rules *)

Lemma ISL_amb n :
  [[[ emp ]]] EAmb [[[ v, @[v = VNat n] ]]].
Proof.
  eapply ISL_pure_step; [|constructor].
  apply ISL_val.
Qed.

Lemma ctx_amb_is_amb k e :
  ctx k ->
  EAmb = k e ->
  k = (fun x => x) /\ e = EAmb.
Proof.
  intros Hctx Heq.
  inv_ctx.
Qed.

Lemma Amb_not_error h :
  ~ is_error EAmb h.
Proof.
  intros (k & e & H1 & H2 & H3).
  apply (ctx_amb_is_amb _ _ H1) in H2 as [-> ->].
  destruct H3. eapply H0.
  eapply head_step_step. constructor.
  apply (Amb_step 0).
Qed.

Lemma Amb_not_ISLERR P Q :
  (exists h, Q h) ->
  ~ [[[ P ]]] EAmb [[[ERR: Q ]]].
Proof.
  intros [h' HQ] HAmb.
  assert ((Q ∗ emp)%S (h' ∪ ∅)). {
    exists h', ∅.
    repeat split; try done.
    apply map_disjoint_empty_r.
  }
  destruct (HAmb emp%S (h' ∪ ∅) H) as (e' & h & Hh' & Hsteps & Herr).
  inv Hsteps.
  - by eapply Amb_not_error.
  - inv H0. symmetry in H2.
    apply (ctx_amb_is_amb _ _ H3) in H2 as [-> ->].
    inv H4. inv H0. inv H1.
    + by eapply val_not_error.
    + inv H0.
      apply (context_EVal _ _ _ H4) in H1 as [-> ->].
      inv H5. inv H0.
Qed.

(* EVar rules *)

Lemma ISLERR_var x :
  [[[ emp ]]] EVar x [[[ERR: emp ]]].
Proof.
  intros R h H.
  exists (EVar x), h.
  repeat split; eauto using steps.
  apply unsafe_is_error. repeat split; [tauto.. | ].
  intros e' h' Hstep.
  inv Hstep. inv_ctx.
  inv H2. inv H0.
Qed.

(* ESeq rules *)

Lemma ISL_seq_val (P : iProp) (Q : val -> iProp) v e :
  [[[ P ]]] e [[[ Q ]]] ->
  [[[ P ]]] ESeq (EVal v) e [[[ Q ]]].
Proof.
  intros HPQ.
  eapply ISL_pure_step; [done | constructor].
Qed.

Lemma ISL_seq (P : iProp) (Q R : val -> iProp) e1 e2 :
  [[[ P ]]] e1 [[[ R ]]] ->
  (exists v, [[[ R v ]]] e2 [[[ Q ]]]) ->
  [[[ P ]]] ESeq e1 e2 [[[ Q ]]].
Proof.
  intros HPR HRQ.
  eapply ISL_context with (k := fun x => ESeq x e2);
  eauto with context.
  destruct HRQ as [v HRQ].
  exists v. by apply ISL_seq_val.
Qed.

Lemma ISLERR_seq (P Q : iProp) e1 e2 :
  [[[ P ]]] e1 [[[ERR: Q ]]] ->
  [[[ P ]]] ESeq e1 e2 [[[ERR: Q ]]].
Proof.
  intros HPQ.
  apply ISLERR_context with (k := fun x => ESeq x e2);
  [eauto with context | done].
Qed.

Lemma ISLERR_seq_right (P Q : iProp) (R : val -> iProp) e1 e2 :
  [[[ P ]]] e1 [[[ R ]]] ->
  (exists v, [[[ R v ]]] e2 [[[ERR: Q]]]) ->
  [[[ P ]]] ESeq e1 e2 [[[ERR: Q ]]].
Proof.
  intros HPR [v HRQ].
  eapply ISLERR_context_ISL with (k := fun x => ESeq x e2);
  [eauto with context | |].
  - eapply ISL_cons; [apply iEntails_refl | | done].
    intros v'. apply iPure_elim. intros ->. apply iEntails_refl.
  - eapply ISLERR_pure_step; [done | constructor].
Qed.

(* EOp rules *)

Lemma ISL_op op v1 v2 v3 :
  eval_bin_op op v1 v2 = Some v3 ->
  [[[ emp ]]] EOp op (EVal v1) (EVal v2) [[[ x, @[x = v3] ]]]%S.
Proof.
  intros Hbin. eapply ISL_pure_step.
  - apply ISL_val.
  - by constructor.
Qed.

Ltac val_not_step k e := repeat
  match goal with
  | H : k e = EVal _ |- _ => apply context_EVal in H; [|assumption]
  | H : _ = _ /\ _ = _ |- _ => destruct H as [-> ->]
  | H : head_step (EVal _) _ _ _ |- _ => inv H
  | H : pure_step (EVal _) _ |- _ => inv H
  end.

Lemma op_none_not_step op v1 v2 h e' h' :
  eval_bin_op op v1 v2 = None ->
  ¬ step (EOp op (EVal v1) (EVal v2)) h e' h'.
Proof.
  intros Hbin Hstep.
  inv Hstep. inv_ctx; inv H1; inv H.
Qed.

Lemma ISLERR_op op v1 v2 :
  eval_bin_op op v1 v2 = None ->
  [[[ emp ]]] EOp op (EVal v1) (EVal v2) [[[ERR: emp]]].
Proof.
  intros Hbin R h H.
  eexists _, h. repeat split; [done | apply steps_refl |].
  apply unsafe_is_error. repeat split; [tauto..|].
  intros e' h'.
  by apply op_none_not_step.
Qed.

(* EIf rules *)

Lemma ISL_if_true (P : iProp) (Q R : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e1 [[[ x, @[x = VBool true] ∗ R x ]]] ->
  [[[ R (VBool true) ]]] e2 [[[ Q ]]] ->
  [[[ P ]]] EIf e1 e2 e3 [[[ Q ]]].
Proof.
  intros HPR HRQ.
  eapply ISL_context with (k := fun x => EIf x e2 e3);
  [eauto with context | apply HPR | exists (VBool true)].
  eapply ISL_cons.
  3: { eapply ISL_pure_step; [apply HRQ | constructor]. }
  - eapply iEntails_trans; [|by apply iSep_mono_l, iPure_intro].
    apply iSep_emp_l.
  - easy.
Qed.

Lemma ISL_if_false (P : iProp) (Q R : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e1 [[[ x, @[x = VBool false] ∗ R x ]]] ->
  [[[ R (VBool false) ]]] e3 [[[ Q ]]] ->
  [[[ P ]]] EIf e1 e2 e3 [[[ Q ]]].
Proof.
  intros HPR HRQ.
  eapply ISL_context with (k := fun x => EIf x e2 e3);
  [eauto with context | apply HPR | exists (VBool false)].
  eapply ISL_cons.
  3: { eapply ISL_pure_step; [apply HRQ | constructor]. }
  - eapply iEntails_trans; [|by apply iSep_mono_l, iPure_intro].
    apply iSep_emp_l.
  - easy.
Qed.

Lemma ISLERR_if (P Q : iProp) e1 e2 e3 :
  [[[ P ]]] e1 [[[ERR: Q ]]] ->
  [[[ P ]]] EIf e1 e2 e3 [[[ERR: Q]]].
Proof.
  intros HPQ.
  eapply ISLERR_context with (k := fun x => EIf x e2 e3);
  [eauto with context | done].
Qed.

Lemma ISLERR_if_true (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e1 [[[ x, @[x = VBool true] ∗ R x ]]] ->
  [[[ R (VBool true) ]]] e2 [[[ERR: Q ]]] ->
  [[[ P ]]] EIf e1 e2 e3 [[[ERR: Q ]]].
Proof.
  intros HPR HRQ.
  eapply ISLERR_context_ISL with (k := fun x => EIf x e2 e3);
  [eauto with context | done |].
  eapply ISLERR_pure_step; [done | constructor].
Qed.

Lemma ISLERR_if_false (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e1 [[[ x, @[x = VBool false] ∗ R x ]]] ->
  [[[ R (VBool false) ]]] e3 [[[ERR: Q ]]] ->
  [[[ P ]]] EIf e1 e2 e3 [[[ERR: Q ]]].
Proof.
  intros HPR HRQ.
  eapply ISLERR_context_ISL with (k := fun x => EIf x e2 e3);
  [eauto with context | done |].
  eapply ISLERR_pure_step; [done | constructor].
Qed.

(* EWhile rules *)

Lemma ISL_While P Q e1 e2 :
  [[[ P ]]] EIf e1 (ESeq e2 (EWhile e1 e2)) (EVal VUnit) [[[ Q ]]] ->
  [[[ P ]]] EWhile e1 e2 [[[ Q ]]].
Proof.
  eauto using ISL_pure_step, pure_step.
Qed.

Lemma ISLERR_While P Q e1 e2 :
  [[[ P ]]] EIf e1 (ESeq e2 (EWhile e1 e2)) (EVal VUnit) [[[ERR: Q ]]] ->
  [[[ P ]]] EWhile e1 e2 [[[ERR: Q ]]].
Proof.
  eauto using ISLERR_pure_step, pure_step.
Qed.

(* EAlloc rules *)

Ltac empty_left H := rewrite left_id; rewrite left_id in H.

(* The basic behavior of alloc *)
Lemma ISL_Alloc_val l v :
  [[[ emp ]]] EAlloc (EVal v) [[[ x, @[x = VRef l] ∗ l ↦ v ]]].
Proof.
  intros R v0 h' (h0 & hR & (h1 & h2 & [-> ->] & -> & -> & Hdisj') & HR & -> & Hdisj).
  empty_left Hdisj.
  exists (∅ ∪ hR). split.
  - exists ∅, hR. repeat split; try done.
    apply map_disjoint_empty_l.
  - revert Hdisj. generalize hR. rewrite <- steps_frame_equiv.
    apply step_once, head_step_step. by constructor.
Qed.

(* Alternative alloc triple, more similar to CISL paper *)
Lemma ISL_Alloc_fresh v :
  [[[ emp ]]] EAlloc (EVal v) [[[ x, ∃ l, @[x = VRef l] ∗ l ↦ v ]]].
Proof.
  eauto using ISL_exists_post, ISL_Alloc_val.
Qed.

(* This lemma shows that we can reuse previously freed locations *)
Lemma ISL_Alloc_reuse l v :
  [[[ l ↦ ⊥ ]]] EAlloc (EVal v) [[[ x, @[x = VRef l] ∗ l ↦ v ]]].
Proof.
  intros R v0 h' (h0 & hR & (h1 & h2 & [-> ->] & -> & -> & Hdisj') & HR & -> & Hdisj).
  empty_left Hdisj.
  exists ({[ l := Reserved ]} ∪ hR). split.
  - exists {[ l := Reserved ]}, hR. repeat split; try done.
    apply map_disjoint_spec. intros.
    apply lookup_singleton_Some in H as []; simplify_eq.
    assert (hR !! i = None). { solve_map_disjoint. } simplify_eq.
  - revert Hdisj. generalize hR. rewrite <- steps_frame_equiv.
    apply step_once, head_step_step.
    rewrite <- (insert_singleton l Reserved (Value v)).
    constructor. intros c Hc.
    rewrite lookup_singleton in Hc. congruence.
Qed.

(* ELoad rules *)

Lemma ISL_Load l v :
  [[[ l ↦ v ]]] ELoad (EVal (VRef l)) [[[ x, @[x = v] ∗ l ↦ v ]]].
Proof.
  intros R x h' (h'' & h2 & (h0 & h1 & [-> ->] & -> & -> & Hdisj') & H2 & -> & Hdisj).
  empty_left Hdisj. exists ({[l := Value v]} ∪ h2).
  split; [by exists {[l := Value v]}, h2 |].
  apply step_once, head_step_step, Load_headstep.
  apply lookup_union_Some_l, lookup_singleton.
Qed.

Lemma load_reserved_not_step h e' h' l :
  {[l := Reserved]} ### h ->
  ¬ step (ELoad (EVal (VRef l))) ({[l := Reserved]} ∪ h) e' h'.
Proof.
  intros Hdisj Hstep.
  inv Hstep. inv H0.
  - inv H1; [inv H|].
    apply lookup_union_Some_inv_l in H0.
    + rewrite lookup_singleton_Some in H0. easy.
    + eapply map_disjoint_Some_l; [done|].
      by rewrite lookup_singleton_Some.
  - inv H2. val_not_step k2 e.
Qed.

Lemma ISLERR_load l :
  [[[ l ↦ ⊥ ]]] ELoad (EVal (VRef l)) [[[ERR: l ↦ ⊥ ]]].
Proof.
  intros R h' (h1 & h2 & -> & H2 & -> & Hdisj).
  exists (ELoad (EVal (VRef l))), ({[l := Reserved]} ∪ h2).
  repeat split; [by exists {[l := Reserved]}, h2 | apply steps_refl | ].
  apply unsafe_is_error. split;
  auto using load_reserved_not_step.
Qed.

(* EStore rules *)

Lemma ISL_Store l v w :
  [[[ l ↦ v ]]] EStore (EVal (VRef l)) (EVal w) [[[ x, @[x = VUnit] ∗ l ↦ w ]]].
Proof.
  intros R x h' (h1 & h2 & (h0 & hl & [-> ->] & -> & -> & Hdisj') & H2 & -> & Hdisj).
  empty_left Hdisj.
  exists ({[l := Value v]} ∪ h2). split.
  - exists {[l := Value v]}, h2. repeat split; try done.
    rewrite map_disjoint_singleton_l.
    by rewrite map_disjoint_singleton_l in Hdisj.
  - revert Hdisj. generalize h2. rewrite <- steps_frame_equiv.
    rewrite <- (insert_singleton l (Value v) (Value w)).
    eapply step_once, head_step_step, Store_headstep.
    by rewrite lookup_singleton.
Qed.

Lemma store_reserved_not_step h e' h' l v :
  {[l := Reserved]} ### h ->
  ¬ step (EStore (EVal (VRef l)) (EVal v)) ({[l := Reserved]} ∪ h) e' h'.
Proof.
  intros Hdisj Hstep.
  inv Hstep. inv H0.
  - inv H1; [inv H|].
    apply lookup_union_Some_inv_l in H5.
    + rewrite lookup_singleton_Some in H5. easy.
    + eapply map_disjoint_Some_l; [done|].
      by rewrite lookup_singleton_Some.
  - inv H2; val_not_step k2 e.
Qed.

Lemma ISLERR_store l v :
  [[[ l ↦ ⊥ ]]] EStore (EVal (VRef l)) (EVal v) [[[ERR: l ↦ ⊥ ]]].
Proof.
  intros R h' (h0 & hR & -> & HR & -> & Hdisj).
  exists (EStore (EVal (VRef l)) (EVal v)), ({[l := Reserved]} ∪ hR).
  repeat split; [by exists {[l := Reserved]}, hR | apply steps_refl | ].
  apply unsafe_is_error. split;
  auto using store_reserved_not_step.
Qed.

(* EFree rules *)

Lemma ISL_free l v :
  [[[ l ↦ v ]]] EFree (EVal (VRef l)) [[[ x, @[x = VUnit] ∗ l ↦ ⊥ ]]].
Proof.
  intros R x h' (h0 & hR & (h1 & h2 & [-> ->] & -> & -> & Hdisj') & HR & -> & Hdisj).
  empty_left Hdisj.
  exists ({[l := Value v]} ∪ hR). split.
  - exists {[l := Value v]}, hR. repeat split; try done.
    rewrite map_disjoint_singleton_l.
    by rewrite map_disjoint_singleton_l in Hdisj.
  - revert Hdisj. generalize hR. rewrite <- steps_frame_equiv.
    rewrite <- (insert_singleton l (Value v) Reserved).
    eapply step_once, head_step_step, Free_headstep.
    by rewrite lookup_singleton.
Qed.

Lemma free_reserved_not_step h e' h' l :
  {[l := Reserved]} ### h ->
  ¬ step (EFree (EVal (VRef l))) ({[l := Reserved]} ∪ h) e' h'.
Proof.
  intros Hdisj Hstep.
  inv Hstep. inv H0.
  - inv H1; [inv H|].
    apply lookup_union_Some_inv_l in H0.
    + rewrite lookup_singleton_Some in H0. easy.
    + eapply map_disjoint_Some_l; [done|].
      by rewrite lookup_singleton_Some.
  - inv H2. val_not_step k2 e.
Qed.

Lemma ISLERR_free l :
  [[[ l ↦ ⊥ ]]] EFree (EVal (VRef l)) [[[ERR: l ↦ ⊥ ]]].
Proof.
  intros R h' (h0 & hR & -> & HR & -> & Hdisj).
  exists (EFree (EVal (VRef l))), ({[l := Reserved]} ∪ hR).
  repeat split; [by exists {[l := Reserved]}, hR | apply steps_refl | ].
  apply unsafe_is_error. split;
  auto using free_reserved_not_step.
Qed.

(* EPar rules *)

Lemma ISL_par_val_emp v v' :
  [[[ emp ]]] EPar (EVal v) (EVal v') [[[ x, @[x = VPair v v'] ]]].
Proof.
  eauto using ISL_pure_step, ISL_val, pure_step.
Qed.

Lemma ISL_par_val (Q1 Q2 : val -> iProp) v v' :
  [[[ Q1 v ∗ Q2 v' ]]] EPar (EVal v) (EVal v') [[[ x, @[x = VPair v v'] ∗ Q1 v ∗ Q2 v' ]]].
Proof.
  eapply ISL_frame', ISL_par_val_emp.
Qed.

(* Different possibility in Correctness logic:
  {P1} e1 {Q1} ->
  {P2} e2 {Q2} ->
  (forall v1 v2, Q1 v1 * Q2 v2 |- Q (VPair v1 v2)) ->
  {P1 * P2} e1 || e2 {Q}.
  
  or:
  {...}
  ->
  {P1 * P2} e1 || e2 {fun x => exists v1 v2, [x = VPair v1 v2] * Q1 v1 * Q2 v2}
*)

Lemma ISL_par (P1 P2 : iProp) (Q1 Q2 : val -> iProp) e1 e2 v1 v2 :
  [[[ P1 ]]] e1 [[[ v, @[ v = v1 ] ∗ Q1 v ]]] ->
  [[[ P2 ]]] e2 [[[ v, @[ v = v2 ] ∗ Q2 v ]]] ->
  [[[ P1 ∗ P2 ]]] EPar e1 e2 [[[ v, @[ v = VPair v1 v2 ] ∗ Q1 v1 ∗ Q2 v2 ]]].
Proof.
  intros H1 H2.
  eapply ISL_context with (k := fun x => EPar x e2); [eauto with context| |].
  - by apply ISL_frame.
  - exists v1. simpl. eapply ISL_context; [repeat constructor| |].
    + by apply ISL_frame_left.
    + exists v2. simpl. eapply ISL_cons; [| | apply ISL_par_val].
      * eapply iEntails_trans; [| apply iSep_assoc].
        eapply iEntails_trans; [| by apply iPure_intro'].
        by eapply iSep_mono_r, iPure_intro'.
      * easy.
Qed.

Lemma ISL_par_err (P Q : iProp) (e1 e2 : expr) :
  ([[[ P ]]] e1 [[[ERR: Q ]]] \/ [[[ P ]]] e2 [[[ERR: Q ]]]) ->
  [[[ P ]]] EPar e1 e2 [[[ERR: Q ]]].
Proof.
  intros [H | H].
  - apply ISLERR_context with (k := fun x => EPar x e2); [eauto with context | done].
  - apply ISLERR_context with (k := fun x => EPar e1 x); [eauto with context | done].
Qed.

Lemma ISL_par_l (P : iProp) (R Q : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e1 [[[ R ]]] ->
  (exists v, [[[ R v ]]] EPar e2 e3 [[[ Q ]]]) ->
  [[[ P ]]] EPar (ESeq e1 e2) e3 [[[ Q ]]].
Proof.
  intros HPR [v HRQ].
  eapply ISL_context with (k := fun x => EPar (ESeq x e2) e3); [|done|].
  - apply Compose_ctx with (k1 := fun x => EPar x e3); eauto with context.
  - exists v. eapply ISL_pure_step_context with (k := fun x => EPar x e3);
    [eauto with context | done | constructor].
Qed.

Lemma ISL_par_l_err (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e1 [[[ R ]]] ->
  (exists v, [[[ R v ]]] EPar e2 e3 [[[ERR: Q ]]]) ->
  [[[ P ]]] EPar (ESeq e1 e2) e3 [[[ERR: Q ]]].
Proof.
  intros HPR [v HRQ].
  eapply ISLERR_context_ISL with (k := fun x => EPar (ESeq x e2) e3).
  - apply Compose_ctx with (k1 := fun x => EPar x e3); eauto with context.
  - eapply ISL_cons; [apply iEntails_refl | | done].
    intros v'. apply iPure_elim. intros ->. apply iEntails_refl.
  - eapply ISLERR_pure_step_context with (k := fun x => EPar x e3);
    [eauto with context | done | constructor].
Qed.

Lemma ISL_par_r (P : iProp) (R Q : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e2 [[[ R ]]] ->
  (exists v, [[[ R v ]]] (EPar e1 e3) [[[ Q ]]]) ->
  [[[ P ]]] EPar e1 (ESeq e2 e3) [[[ Q ]]].
Proof.
  intros HPR [v HRQ].
  eapply ISL_context with (k := fun x => EPar e1 (ESeq x e3)); [|done|].
  - apply Compose_ctx with (k1 := fun x => EPar e1 x); eauto with context.
  - exists v. eapply ISL_pure_step_context;
    [eauto with context | done | constructor].
Qed.

Lemma ISL_par_r_err (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e2 [[[ R ]]] ->
  (exists v, [[[ R v ]]] EPar e1 e3 [[[ERR: Q ]]]) ->
  [[[ P ]]] EPar e1 (ESeq e2 e3) [[[ERR: Q ]]].
Proof.
  intros HPR [v HRQ].
  eapply ISLERR_context_ISL with (k := fun x => EPar e1 (ESeq x e3)).
  - eauto with context.
  - eapply ISL_cons; [apply iEntails_refl | | done].
    intros v'. apply iPure_elim. intros ->. apply iEntails_refl.
  - eapply ISLERR_pure_step_context; [|done|]; repeat constructor.
Qed.

Lemma ISL_par_r_gen (P : iProp) (R : val -> iProp) (Q : option val -> iProp) e1 e2 e3 :
  [[[ P ]]] e2 [[[ R ]]] ->
  (exists v, ISL_Gen (R v) (EPar e1 e3) Q) ->
  ISL_Gen P (EPar e1 (ESeq e2 e3)) Q.
Proof.
  intros HPR [v HRQ].
  rewrite ISL_Gen_equiv_total in HRQ.
  destruct HRQ as [HRQSome HRQNone].
  rewrite ISL_Gen_equiv_total. split.
  - eapply ISL_par_r; [done|].
    by exists v.
  - eapply ISL_par_r_err; [done|].
    by exists v.
Qed.

Lemma ISL_par_r_err' (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  [[[ P ]]] e2 [[[ R ]]] ->
  (exists v, [[[ R v ]]] EPar e1 e3 [[[ERR: Q ]]]) ->
  [[[ P ]]] EPar e1 (ESeq e2 e3) [[[ERR: Q ]]].
Proof.
  intros HPR [v HRQ].
  rewrite ISLERR_Gen_equiv.
  eapply ISL_par_r_gen; [done|].
  exists v.
  by rewrite <- ISLERR_Gen_equiv.
Qed.

Lemma pair_steps_par_steps e1 e2 v h h' :
  steps (EPair e1 e2) h (EVal v) h' ->
  steps (EPar e1 e2) h (EVal v) h'.
Proof.
  intros Hsteps.
  remember (EPair e1 e2) as e.
  revert Heqe. revert e1 e2.
  remember (EVal v) as v'.
  induction Hsteps; intros e' e'' Heq; simplify_eq.
  assert (EVal v = EVal v) by reflexivity.
  specialize (IHHsteps H0). clear H0.
  inv H. inv H1.
  - inv H2. inv H. inv Hsteps.
    + eauto with headstep.
    + inv H. val_not_step k e.
  - inv H.
    + eapply steps_step.
      * eapply do_step with (k := fun x => EPar (k2 x) e''); [|done].
        apply Compose_ctx with (k1 := fun x => EPar x e'');
        eauto with context.
      * by apply IHHsteps.
    + eapply steps_step.
      * eapply do_step with (k := fun x => EPar _ (k2 x));
        eauto with context.
      * by apply IHHsteps.
Qed.

Lemma ISL_par_pair (P : iProp) (Q : val -> iProp) e1 e2 :
  [[[ P ]]] EPair e1 e2 [[[ Q ]]] ->
  [[[ P ]]] EPar e1 e2 [[[ Q ]]].
Proof.
  intros HPair R v h' HQR.
  destruct (HPair R v h' HQR) as (h & HPR & Hsteps).
  exists h. split; [done|].
  by apply pair_steps_par_steps.
Qed.

Lemma par_steps_mirror e1 e2 v1 v2 h h' :
  steps (EPar e1 e2) h (EVal (VPair v1 v2)) h' ->
  steps (EPar e2 e1) h (EVal (VPair v2 v1)) h'.
Proof.
  intros Hsteps.
  remember (EPar e1 e2) as e.
  remember (EVal (VPair v1 v2)) as v.
  revert Heqe. revert e1 e2.
  induction Hsteps; intros e' e'' Heqe; simplify_eq.
  assert (EVal (VPair v1 v2) = EVal (VPair v1 v2)) by reflexivity.
  specialize (IHHsteps H0). clear H0.
  inv H. inv H1.
  - inv H2. inv H. inv Hsteps.
    + eauto with headstep.
    + inv H. val_not_step k e.
  - inv H.
    + eapply steps_step.
      * apply do_step with (k := fun x => EPar e'' (k2 x)); [|done].
        apply Compose_ctx with (k1 := fun x => EPar e'' x);
        eauto with context.
      * by apply IHHsteps.
    + eapply steps_step.
      * apply do_step with (k := fun x => EPar (k2 x) e'); [|done].
        apply Compose_ctx with (k1 := fun x => EPar x e');
        eauto with context.
      * by apply IHHsteps.
Qed.

Lemma ISL_par_mirror (P : iProp) (Q : val -> iProp) e1 e2 v1 v2 :
  [[[ P ]]] EPar e1 e2 [[[ x, @[x = VPair v1 v2] ∗ Q (VPair v1 v2) ]]] ->
  [[[ P ]]] EPar e2 e1 [[[ x, @[x = VPair v2 v1] ∗ Q (VPair v1 v2) ]]].
Proof.
  intros HPair R v h' (h'' & hR & (h1 & h2 & [-> ->] & HQ & -> & Hdisj') & HR & Heq & Hdisj).
  destruct (HPair R (VPair v1 v2) h') as (h & HPR & Hsteps); simplify_eq.
  2: {
    exists h. split; [done|].
    by apply par_steps_mirror.
  }
  exists (∅ ∪ h2), hR. repeat split; try done.
  by exists ∅, h2.
Qed.

(* Locks *)
Definition is_locked (e : expr) (h : heap) :=
  exists l, e = EVal (VRef l) /\ h !! l = Some (Value (VLock true)).

(*Definition is_deadlock (e : expr) (h : heap) :=
  (exists k l, ctx k /\ e = k (ELock l)) /\
  (forall k l e' h', ctx k /\ e = k (ELock l) /\ steps e h e' h' -> is_locked l h').
*)

Definition is_deadlock (e : expr) (h : heap) :=
  (exists k l, ctx k /\ e = k (ELock l) /\
     forall e' h', steps e h e' h' -> is_locked l h').

Print is_deadlock.

(* Wrong definition
  Definition is_deadlock (e : expr) (h : heap) :=
  (exists k l, ctx k /\ e = k (ELock l)) /\
  (forall k l e' h', ctx k /\ e = k (ELock l) -> is_locked l h).

  Example:
    EPar (
      ESeq (ELock (EVal (VRef 0))) (EUnlock (EVal (VRef 0)))
    ) (
      ESeq (ELock (EVal (VRef 0))) (EUnlock (EVal (VRef 0)))
    )
  Then after the first thread does the lock, the definition gives a deadlock,
  but there is no deadlock since the first thread will unlock the lock immediately
*)


Definition ILDD (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall h', Q h' -> exists e' h, P h /\ steps e h e' h' /\ is_deadlock e' h'.

Definition ISLDD (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall R, ILDD (P ∗ R)%S e (Q ∗ R)%S.

Notation "[[[ P ]]] e [[[DD: Q ]]]" := (ISLDD P%S e Q%S)
  (at level 20, e, P at level 200, Q at level 200, only parsing).

Lemma ISLDD_context_ISL (P Q : iProp) (R : val -> iProp) e v k :
  ctx k ->
  [[[ P ]]] e [[[ x, @[x = v] ∗ R x]]] ->
  [[[ R v ]]] k (EVal v) [[[DD: Q ]]] ->
  [[[ P ]]] k e [[[DD: Q ]]].
Proof.
  intros Hk HPR HRQ R' h' HQ.
  destruct (HRQ R' h' HQ) as (e' & h & HRR' & Hsteps & Hdead).
  assert (H : ((@[ v = v] ∗ R v) ∗ R')%S h).
  { by apply iSep_assoc, iPure_intro'. }
  destruct (HPR R' v h H) as (h0 & HPR' & Hsteps').
  exists e', h0. do 2 (split; try done).
  eapply steps_trans; [|done].
  by apply steps_context_steps.
Qed.

(********************************************
              Soundness
********************************************)

(*
  We need (exists h', Q h'), because if Q -> false then
  [[[ P ]]] e [[[ERR: Q ]]]
  always holds, even when e would not lead to an error
*)

Lemma soundness (e : expr) (Q : iProp) :
  [[[ emp ]]] e [[[ERR: Q ]]] ->
  (exists h', Q h') ->
  exists e' h', steps e ∅ e' h' /\ is_error e' h'.
Proof.
  intros HISLERR [h' HQ].
  specialize (HISLERR emp%S).
  apply ILERR_cons with (P := emp%S) (Q := Q) in HISLERR;
  [ | eauto with seplogic..]. unfold ILERR in HISLERR.
  destruct (HISLERR h' HQ) as (e' & h & Hh & Hsteps & Herr).
  inv Hh. by exists e', h'.
Qed.

(* Examples *)

Definition Ex_mem : expr :=
  ELet "x" (EAlloc (EVal (VNat 0))) (
    ELet "z" (EAlloc (EVal (VNat 0))) (
      EPar (
        ESeq (EFree (EVar "x")) (EStore (EVar "z") (EVal (VNat 1)))
      ) (
        ELet "a" (ELoad (EVar "z")) (
          EIf (EOp EqOp (EVar "a") (EVal (VNat 1))) (
            EStore (EVar "x") (EVal (VNat 1))
          ) (
            EVal VUnit
          )
        )
      )
    )
  ).

Ltac ISL_pure_true := eapply ISL_cons;
  [eauto using iPure_intro' | intros v; apply iEntails_refl |].

Ltac ISLERR_pure_true := eapply ISLERR_cons;
  [eauto using iPure_intro' | intros v; apply iEntails_refl |].

Example correct_execution lx lz :
  [[[ emp ]]] Ex_mem [[[ x, @[x = VPair VUnit VUnit] ∗ lz ↦ VNat 1 ∗ lx ↦ ⊥ ]]].
Proof.
  unfold Ex_mem.
  eapply ISL_context with (k := fun x => ELet _ x _);
  [eauto with context | apply ISL_Alloc_val | simpl].
  exists (VRef lx). ISL_pure_true.
  eapply ISL_pure_step; [|constructor]. simpl.
  eapply ISL_context with (k := fun x => ELet _ x _);
  [eauto with context |..]. {
    eapply ISL_cons;
    [apply iSep_emp_l_inv | intros v; apply iEntails_refl |].
    apply ISL_frame, ISL_Alloc_val.
  } simpl.
  exists (VRef lz). apply ISL_sep_assoc_pre. ISL_pure_true.
  eapply ISL_pure_step; [|constructor]. simpl.
  apply ISL_par_mirror with (Q := fun _ => (lz ↦ VNat 1 ∗ lx ↦ ⊥)%S).
  apply ISL_par_pair.
  eapply ISL_context with (k := fun x => EPair x _);
  [eauto with context | |].
  - eapply ISL_context with (k := fun x => ELet _ x _);
    [eauto with context | |].
    + eapply ISL_frame, ISL_Load.
    + simpl. exists (VNat 0). ISL_pure_true.
      { eapply iEntails_trans; [apply iPure_intro' | apply iSep_assoc]; done. }
      eapply ISL_pure_step; [|constructor]. simpl.
      eapply ISL_context with (k := fun x => EIf x _ _);
      [eauto with context | |].
      * eapply ISL_pure_step.
        -- apply ISL_frame', ISL_val.
        -- constructor. constructor.
      * simpl. exists (VBool false). ISL_pure_true.
        eapply ISL_pure_step; [|constructor].
        eapply ISL_frame', ISL_val.
  - simpl. exists VUnit. ISL_pure_true.
    eapply ISL_context with (k := fun x => EPair (EVal VUnit) x);
    [eauto with context | |].
    + eapply ISL_context with (k := fun x => ESeq x _);
      [eauto with context | |].
      * apply ISL_frame_left. apply ISL_free.
      * simpl. exists VUnit. ISL_pure_true.
        -- eapply iEntails_trans; [|apply iSep_comm].
           eapply iEntails_trans; [|apply iSep_assoc].
           by apply iPure_intro'.
        -- eapply ISL_pure_step; [|constructor].
           eapply ISL_frame_left, ISL_Store.
    + simpl. exists VUnit. ISL_pure_true.
      * eapply iEntails_trans; [|apply iSep_comm].
        eapply iEntails_trans; [|apply iSep_assoc].
        by apply iPure_intro'.
      * eapply ISL_pure_step; [|constructor].
        eapply ISL_frame', ISL_val.
Qed.

Example erroneous_execution lx lz :
  [[[ emp ]]] Ex_mem [[[ERR: lz ↦ VNat 1 ∗ lx ↦ ⊥ ]]].
Proof.
  unfold Ex_mem.
  eapply ISLERR_context_ISL_exists with (k := fun x => ELet _ x _);
  [eauto with context | apply ISL_Alloc_val | simpl].
  exists (VRef lx). ISLERR_pure_true.
  eapply ISLERR_pure_step; [|constructor]. simpl.
  eapply ISLERR_context_ISL_exists with (k := fun x => ELet _ x _);
  [eauto with context | eapply ISL_frame', ISL_Alloc_val |].
  exists (VRef lz). ISLERR_pure_true.
  { eapply iEntails_trans; [| apply iSep_assoc]. by apply iPure_intro'. }
  eapply ISLERR_pure_step; [|constructor]. simpl.
  eapply ISL_par_l_err; [apply ISL_frame_left, ISL_free|].
  exists VUnit. ISLERR_pure_true; [by apply iSep_mono_r, iPure_intro'|].
  eapply ISLERR_context_ISL with
    (k := fun x => EPar x _);
  [eauto with context | apply ISL_sep_assoc_post, ISL_frame, ISL_Store |].
  apply ISL_par_err. right.
  eapply ISLERR_context_ISL with (k := fun x => ELet _ x _);
  [eauto with context | apply ISL_sep_assoc_post, ISL_frame, ISL_Load |].
  eapply ISLERR_pure_step; [|constructor]. simpl.
  eapply ISLERR_if_true with (R := (fun x => lz ↦ VNat 1 ∗ lx ↦ ⊥)%S).
  - eapply ISL_frame', ISL_pure_step; [|by constructor].
    apply ISL_val.
  - apply ISLERR_frame_left, ISLERR_store.
Qed.

Definition Ex_thesis : expr :=
  EPar (ELoad (EVal (VRef 0))) (EAlloc (EVal (VNat 10))).

Example Ex_thesis_correct :
  [[[ 0 ↦ ⊥ ]]] Ex_thesis [[[ x, @[x = VPair (VNat 10) (VRef 0)] ∗ 0 ↦ (VNat 10) ]]].
Proof.
  eapply ISL_par_mirror with (Q := (fun x => 0 ↦ (VNat 10))%S).
  eapply ISL_par_pair, ISL_context with (k := fun x => EPair x _);
  [eauto with context | apply ISL_Alloc_reuse | simpl].
  exists (VRef 0). ISL_pure_true.
  eapply ISL_context;
  [eauto with context | apply ISL_Load | simpl].
  exists (VNat 10). ISL_pure_true.
  eapply ISL_pure_step; [|constructor].
  apply ISL_frame', ISL_val.
Qed.

Example Ex_thesis_erroneous :
  [[[ 0 ↦ ⊥ ]]] Ex_thesis [[[ERR: 0 ↦ ⊥ ]]].
Proof.
  apply ISL_par_err. left.
  apply ISLERR_load.
Qed.

Definition Ex_race (n : nat) : expr :=
  ELet "x" (EAlloc (EVal (VNat n))) (
    EPar
      (EStore (EVar "x") (EOp PlusOp (ELoad (EVar "x")) (EVal (VNat 1))))
      (EStore (EVar "x") (EOp PlusOp (ELoad (EVar "x")) (EVal (VNat 1))))
  ).
