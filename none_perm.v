From Coq Require Export Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Program.Equality.
From Coq Require Import Bool.DecBool.
Require Import perm.
From iris.proofmode Require Import tactics.
From stdpp Require Import countable.
From Coq Require Import RelationClasses.
Require Import DD.

(* We define a helper operational semantics to prove steps_trace_none_first *)
Inductive none_event :=
  | Base' : option base_event -> none_event
  | Left' : none_event -> none_event
  | Right' : none_event -> none_event.

Lemma none_event_eq_dec : EqDecision none_event.
Proof.
  intros e e'.
  dependent induction e.
  - destruct e'; [|by right..].
    destruct o; destruct o0; [| right | right | left]; [|eauto..].
    destruct (base_event_eq_dec b b0) as [<- | Hne]; [by left|].
    right. intros Heq. simplify_eq.
  - destruct e'; [by right | | by right].
    destruct (IHe e') as [<- | Hne]; [by left|].
    right. intros Heq. simplify_eq.
  - destruct e'; [by right..|].
    destruct (IHe e') as [<- | Hne]; [by left|].
    right. intros Heq. simplify_eq.
Qed.

Definition none_trace : Type := list none_event.

Inductive none_can_swap : none_event -> none_event -> Prop :=
  | none_left_right_swap e e' :
      none_can_swap (Left' e) (Right' e')
  | none_right_left_swap e e' :
      none_can_swap (Right' e) (Left' e')
  | none_left_left_swap e e' :
      none_can_swap e e' ->
      none_can_swap (Left' e) (Left' e')
  | none_right_right_swap e e' :
      none_can_swap e e' ->
      none_can_swap (Right' e) (Right' e').

Lemma none_can_swap_symm : Symmetric none_can_swap.
Proof. intros x y Hswap. induction Hswap; constructor; done. Qed.

Lemma none_can_swap_irreflexive : Irreflexive none_can_swap.
Proof. intros x. induction x; intros Hswap; by inv Hswap. Qed.

Lemma none_can_swap_dec (e e' : none_event) : Decision (none_can_swap e e').
Proof.
  dependent induction e.
  - right. intros Hswap. inv Hswap.
  - destruct e'.
    + right. intros Hswap. inv Hswap.
    + destruct (IHe e').
      * left. eauto using none_can_swap.
      * right. intros Hswap. by inv Hswap.
    + left. eauto using none_can_swap.
  - destruct e'.
    + right. intros Hswap. inv Hswap.
    + left. eauto using none_can_swap.
    + destruct (IHe e').
      * left. eauto using none_can_swap.
      * right. intros Hswap. by inv Hswap.
Qed.

Fixpoint to_none_event (e : event) : none_event :=
  match e with
  | Base b => Base' (Some b)
  | Left e' => Left' (to_none_event e')
  | Right e' => Right' (to_none_event e')
  end.

Fixpoint from_none_event (e : none_event) : option event :=
  match e with
  | Base' None => None
  | Base' (Some b) => Some (Base b)
  | Left' e' => option_map Left (from_none_event e')
  | Right' e' => option_map Right (from_none_event e')
  end.

Lemma from_to_none_event_id (e : event) :
  from_none_event (to_none_event e) = Some e.
Proof.
  induction e; simpl.
  - done.
  - by rewrite IHe.
  - by rewrite IHe.
Qed.

Inductive none_perm : list none_event -> list none_event -> Prop :=
  | none_perm_refl t :
      none_perm t t
  | none_perm_skip x t t' :
      none_perm t t' ->
      none_perm (x :: t) (x :: t')
  | none_perm_swap x y t :
      none_can_swap x y ->
      none_perm (x :: y :: t) (y :: x :: t)
  | none_perm_trans t t' t'' :
      none_perm t t' -> 
      none_perm t' t'' ->
      none_perm t t''.

Lemma none_perm_app t t' t'' :
  none_perm t t' ->
  none_perm (t ++ t'') (t' ++ t'').
Proof.
  intros Hperm. induction Hperm.
  - constructor.
  - rewrite <- !app_comm_cons. by constructor.
  - rewrite <- !app_comm_cons. by constructor.
  - by econstructor.
Qed.

Inductive none_step_trace :
  expr -> lock_heap ->
  expr -> lock_heap ->
  none_event -> Prop :=
  | do_head_step_trace_none_event e h e' h' (b : option base_event) :
      head_step_trace e h e' h' b ->
      none_step_trace e h e' h' (Base' b)
  | ctx_step_trace_none_event k e h e' h' (b : none_event) :
      ctx_trace k ->
      none_step_trace e h e' h' b ->
      none_step_trace (k e) h (k e') h' b
  | par_l_step_trace_none_event e1 e2 h e1' h' (b : none_event) :
      none_step_trace e1 h e1' h' b ->
      none_step_trace (EPar e1 e2) h (EPar e1' e2) h' (Left' b)
  | par_r_step_trace_none_event e1 e2 h e2' h' (b : none_event) :
      none_step_trace e2 h e2' h' b ->
      none_step_trace (EPar e1 e2) h (EPar e1 e2') h' (Right' b).

Lemma step_trace_none_to_step_trace {e h e' h' t} :
  none_step_trace e h e' h' t ->
  step_trace e h e' h' (from_none_event t).
Proof.
  intros Hstep. induction Hstep; by constructor.
Qed.

Lemma step_trace_to_step_trace_none_some {e h e' h' t} :
  step_trace e h e' h' (Some t) ->
  none_step_trace e h e' h' (to_none_event t).
Proof.
  intros Hstep. remember (Some t) as st. revert t Heqst.
  induction Hstep; intros t Heqst.
  - destruct b; [|done]. simpl in Heqst. simplify_eq.
    by constructor.
  - eauto using none_step_trace.
  - destruct b; [|done].
    specialize (IHHstep _ eq_refl).
    simpl in Heqst. simplify_eq.
    by constructor.
  - destruct b; [|done].
    specialize (IHHstep _ eq_refl).
    simpl in Heqst. simplify_eq.
    by constructor.
Qed.

Lemma step_trace_to_step_trace_none_none {e h e' h'} :
  step_trace e h e' h' None ->
  exists t,
    none_step_trace e h e' h' t /\
    from_none_event t = None.
Proof.
  intros Hstep. remember None as n. induction Hstep.
  - destruct b; [done|].
    exists (Base' None). split; [|done].
    by constructor.
  - destruct (IHHstep Heqn) as (t & Hstept & Ht).
    eauto using none_step_trace.
  - destruct b; [done|].
    destruct (IHHstep eq_refl) as (t & Hstept & Ht). simpl.
    exists (Left' t). split; [eauto using none_step_trace|].
    simpl. by rewrite Ht.
  - destruct b; [done|].
    destruct (IHHstep eq_refl) as (t & Hstept & Ht). simpl.
    exists (Right' t). split; [eauto using none_step_trace|].
    simpl. by rewrite Ht.
Qed.

Lemma ctxs_none_step e1 h1 e2 h2 b k :
  ctxs_trace k ->
  none_step_trace e1 h1 e2 h2 b ->
  none_step_trace (k e1) h1 (k e2) h2 b.
Proof.
  intros Hctx Hstep.
  induction Hctx; by [|constructor].
Qed.

Inductive none_steps_trace : expr -> lock_heap -> expr -> lock_heap -> none_trace -> Prop :=
  | steps_refl_trace_none e h :
      none_steps_trace e h e h []
  | steps_step_none_trace e1 h1 e2 h2 e3 h3 (b : none_event) (t : none_trace) :
      none_step_trace e1 h1 e2 h2 b ->
      none_steps_trace e2 h2 e3 h3 t ->
      none_steps_trace e1 h1 e3 h3 (b :: t).

Lemma none_steps_trace_trans {e1 h1 e2 h2 e3 h3 t t'} :
  none_steps_trace e1 h1 e2 h2 t ->
  none_steps_trace e2 h2 e3 h3 t' ->
  none_steps_trace e1 h1 e3 h3 (t ++ t').
Proof.
  intros Hsteps1 Hsteps2.
  induction Hsteps1; [done|].
  eauto using none_steps_trace.
Qed.

Fixpoint remove_none_map {A B : Type} (f : A -> option B) (t : list A) : list B :=
  match t with
  | [] => []
  | a :: t' =>
      match f a with
      | Some b => b :: (remove_none_map f t')
      | None => remove_none_map f t'
      end
  end.

Lemma steps_trace_none_to_steps_trace {e h e' h' t} :
  none_steps_trace e h e' h' t ->
  steps_trace e h e' h' (remove_none_map from_none_event t).
Proof.
  intros Hstep. induction Hstep.
  - constructor.
  - apply step_trace_none_to_step_trace in H. simpl.
    destruct (from_none_event b) eqn:Hb.
    + by eapply steps_step_some.
    + by eapply steps_step_none.
Qed.

Lemma steps_trace_to_steps_trace_none {e h e' h' t} :
  steps_trace e h e' h' t ->
  exists t',
    none_steps_trace e h e' h' t' /\
    t = remove_none_map from_none_event t'.
Proof.
  intros Hsteps. induction Hsteps.
  - eauto using none_steps_trace.
  - apply step_trace_to_step_trace_none_none in H.
    destruct H as (t0 & Hstep & Ht0).
    destruct IHHsteps as (t' & Hsteps' & Heq').
    eexists. split; [eauto using none_steps_trace|].
    simpl. by rewrite Ht0.
  - apply step_trace_to_step_trace_none_some in H.
    destruct IHHsteps as (t' & Hsteps' & Heq').
    eexists. split; [eauto using none_steps_trace|].
    simpl. rewrite from_to_none_event_id.
    by f_equal.
Qed.

Lemma ctx_none_step_not_val {e1 h1 e2 h2 b k} :
  ctx_trace k ->
  ¬ is_val e1 ->
  none_step_trace (k e1) h1 e2 h2 b ->
  exists e2', e2 = k e2' /\
    none_step_trace e1 h1 e2' h2 b.
Proof.
  intros Hctx Hnval Hstep.
  inv Hstep; [| |inv Hctx..].
  - inv H; [|by inv Hctx..].
    by inv H0; inv Hctx.
  - assert (Hstep := step_trace_none_to_step_trace H1).
    assert (Hnval' := step_trace_not_val _ _ _ _ _ Hstep).
    destruct (ctx_trace_unique _ _ _ _ H0 Hctx Hnval' Hnval H) as [-> ->].
    eauto.
Qed.

Lemma none_step_left_ctxs {e1 h1 e2 h2 t} :
  none_step_trace e1 h1 e2 h2 (Left' t) ->
  exists k e1' e2' e,
    ctxs_trace k /\
    e1 = k (EPar e1' e) /\
    e2 = k (EPar e2' e) /\
    none_step_trace e1' h1 e2' h2 t.
Proof.
  intros Hstep. remember (Left' t) as Lt.
  induction Hstep; [by destruct b | | | by destruct b].
  - destruct (IHHstep HeqLt) as (k0 & e1' & e2' & e0 & Hctx & -> & -> & Hstep').
    exists (λ x, k (k0 x)), e1', e2', e0.
    repeat split; eauto with context.
  - simplify_eq.
    exists (λ x, x), e1, e1', e2.
    repeat split; eauto with context.
Qed.

Lemma none_step_right_ctxs {e1 h1 e2 h2 t} :
  none_step_trace e1 h1 e2 h2 (Right' t) ->
  exists k e1' e2' e,
    ctxs_trace k /\
    e1 = k (EPar e e1') /\
    e2 = k (EPar e e2') /\
    none_step_trace e1' h1 e2' h2 t.
Proof.
  intros Hstep. remember (Right' t) as Rt.
  induction Hstep; [by destruct b | | by destruct b |].
  - destruct (IHHstep HeqRt) as (k0 & e1' & e2' & e0 & Hctx & -> & -> & Hstep').
    exists (λ x, k (k0 x)), e1', e2', e0.
    repeat split; eauto with context.
  - simplify_eq.
    exists (λ x, x), e2, e2', e1.
    repeat split; eauto with context.
Qed.

Lemma none_step_left_without_context {e1 e2 h1 e3 h2 t} :
  none_step_trace (EPar e1 e2) h1 e3 h2 (Left' t) ->
  exists e1', e3 = EPar e1' e2 ∧ none_step_trace e1 h1 e1' h2 t.
Proof.
  intros Hstep. inv Hstep.
  - inv H0.
  - eauto.
Qed.

Lemma none_step_left_in_context {e1 e2 h1 e3 h2 k t} :
  ctxs_trace k ->
  none_step_trace (k (EPar e1 e2)) h1 e3 h2 (Left' t) ->
  exists e1', e3 = k (EPar e1' e2) /\ none_step_trace e1 h1 e1' h2 t.
Proof.
  intros Hctx. revert e1 e2 e3 h1 h2 t.
  induction Hctx; intros e1 e2 e3 h1 h2 t Hstep.
  - by apply none_step_left_without_context.
  - assert (Hnval : ¬ is_val (k2 (EPar e1 e2))) by (apply ctxs_not_val; tauto).
    destruct (ctx_none_step_not_val H Hnval Hstep) as (e' & -> & Hstep').
    destruct (IHHctx _ _ _ _ _ _ Hstep') as (e2' & -> & IH).
    eauto.
Qed.

Lemma none_step_right_without_context {e1 e2 h1 e3 h2 t} :
  none_step_trace (EPar e1 e2) h1 e3 h2 (Right' t) ->
  exists e2', e3 = EPar e1 e2' ∧ none_step_trace e2 h1 e2' h2 t.
Proof.
  intros Hstep. inv Hstep.
  - inv H0.
  - eauto.
Qed.

Lemma none_step_right_in_context {e1 e2 h1 e3 h2 k t} :
  ctxs_trace k ->
  none_step_trace (k (EPar e1 e2)) h1 e3 h2 (Right' t) ->
  exists e2', e3 = k (EPar e1 e2') /\ none_step_trace e2 h1 e2' h2 t.
Proof.
  intros Hctx. revert e1 e2 e3 h1 h2 t.
  induction Hctx; intros e1 e2 e3 h1 h2 t Hstep.
  - by apply none_step_right_without_context.
  - assert (Hnval : ¬ is_val (k2 (EPar e1 e2))) by (apply ctxs_not_val; tauto).
    destruct (ctx_none_step_not_val H Hnval Hstep) as (e' & -> & Hstep').
    destruct (IHHctx _ _ _ _ _ _ Hstep') as (e2' & -> & IH).
    eauto.
Qed.

Lemma none_step_heap_indifferent h1' {e1 h1 e2 h2 b} :
  none_step_trace e1 h1 e2 h2 b ->
  exists h2', none_step_trace e1 h1' e2 h2' b.
Proof.
  intros Hstep. induction Hstep.
  - inv H; eexists; by do 2 constructor.
  - destruct IHHstep as [h2' H2].
    eauto using none_step_trace.
  - destruct IHHstep as [h2' H2].
    eauto using none_step_trace.
  - destruct IHHstep as [h2' H2].
    eauto using none_step_trace.
Qed.

Lemma none_step_swap {e1 h1 e2 h2 e3 h3 x y} :
  none_can_swap x y ->
  none_step_trace e1 h1 e2 h2 x ->
  none_step_trace e2 h2 e3 h3 y ->
  exists e' h' h'',
    none_step_trace e1 h1 e' h' y /\
    none_step_trace e' h' e3 h'' x.
Proof.
  intros Hswap. revert e1 h1 e2 h2 e3 h3.
  induction Hswap; intros e1 h1 e2 h2 e3 h3 Hstepx Hstepy.
  - destruct (none_step_left_ctxs Hstepx) as
      (k & e1' & e1'' & er & Hctx & -> & -> & Hx).
    destruct (none_step_right_in_context Hctx Hstepy) as
      (e2' & -> & Hy).
    destruct (none_step_heap_indifferent h1 Hy) as [h1' H1].
    destruct (none_step_heap_indifferent h1' Hx) as [h2' H2].
    exists (k (EPar e1' e2')), h1', h2'.
    split; apply ctxs_none_step; try done; by constructor.
  - destruct (none_step_right_ctxs Hstepx) as
      (k & e2' & e2'' & er & Hctx & -> & -> & Hx).
    destruct (none_step_left_in_context Hctx Hstepy) as
      (e1' & -> & Hy).
    destruct (none_step_heap_indifferent h1 Hy) as [h1' H1].
    destruct (none_step_heap_indifferent h1' Hx) as [h2' H2].
    exists (k (EPar e1' e2')), h1', h2'.
    split; apply ctxs_none_step; try done; by constructor.
  - destruct (none_step_left_ctxs Hstepx) as
      (k & e1' & e1'' & er & Hctx & -> & -> & Hx).
    destruct (none_step_left_in_context Hctx Hstepy) as
      (e1''' & -> & Hy).
    destruct (IHHswap _ _ _ _ _ _ Hx Hy) as (e3 & h1' & h2' & Hstep1 & Hstep2).
    exists (k (EPar e3 er)), h1', h2'.
    split; apply ctxs_none_step; try done; by constructor.
  - destruct (none_step_right_ctxs Hstepx) as
      (k & e2' & e2'' & er & Hctx & -> & -> & Hx).
    destruct (none_step_right_in_context Hctx Hstepy) as
      (e2''' & -> & Hy).
    destruct (IHHswap _ _ _ _ _ _ Hx Hy) as (e3 & h1' & h2' & Hstep1 & Hstep2).
    exists (k (EPar er e3)), h1', h2'.
    split; apply ctxs_none_step; try done; by constructor.
Qed.

Fixpoint is_some (e : none_event) :=
  match e with
  | Base' None => False
  | Base' (Some _) => True
  | Left' b => is_some b
  | Right' b => is_some b
  end.

Lemma decision_is_some (e : none_event) : Decision (is_some e).
Proof.
  induction e.
  - destruct o; simpl; [left | right]; tauto.
  - destruct IHe; by [left | right].
  - destruct IHe; by [left | right].
Qed.

Lemma not_none_step_trace_val {v h1 e h2 t} :
  ¬ none_step_trace (EVal v) h1 e h2 t.
Proof.
  intros Hstep. inv Hstep.
  - inv H. inv H0.
  - inv H0.
Qed.

Lemma none_step_base_ctxs {e1 h1 e2 h2 b} :
  none_step_trace e1 h1 e2 h2 (Base' b) ->
  exists k e e', ctxs_trace k /\
    e1 = k e /\
    e2 = k e' /\ 
    head_step_trace e h1 e' h2 b.
Proof.
  intros Hstep. remember (Base' b) as bb.
  induction Hstep; [ | | by destruct b0..].
  - simplify_eq.
    exists (λ x, x), e, e'.
    repeat split; auto with context.
  - destruct (IHHstep Heqbb) as (k0 & e0 & e0' & Hctx0 & -> & -> & Hhead).
    exists (λ x, k (k0 x)), e0, e0'.
    repeat split; auto with context.
Qed.

Lemma none_step_trace_not_val {e h e' h' t} :
  none_step_trace e h e' h' t ->
  ¬ is_val e.
Proof.
  intros Hstep.
  induction Hstep; [.. | tauto | tauto].
  - inv H; [inv H0|..]; tauto.
  - by apply not_is_val_ctx1, ctx_trace_ctx1.
Qed.

Lemma ctx_none_step_trace_not_val {e1 h1 e2 h2 b k} :
  ctx_trace k ->
  ¬ is_val e1 ->
  none_step_trace (k e1) h1 e2 h2 b ->
  exists e2', e2 = k e2' /\
    none_step_trace e1 h1 e2' h2 b.
Proof.
  intros Hctx Hnval Hstep.
  inv Hstep; [| |inv Hctx..].
  - inv H; [|by inv Hctx..].
    by inv H0; inv Hctx.
  - assert (Hnval' := none_step_trace_not_val H1).
    destruct (ctx_trace_unique _ _ _ _ H0 Hctx Hnval' Hnval H) as [-> ->].
    eauto.
Qed.

Lemma ctxs_none_step_not_val {e1 h1 e2 h2 b k} :
  ctxs_trace k ->
  ¬ is_val e1 ->
  none_step_trace (k e1) h1 e2 h2 b ->
  exists e2', e2 = k e2' /\
    none_step_trace e1 h1 e2' h2 b.
Proof.
  intros Hctx Hnval. revert e2.
  induction Hctx; intros e2 Hstep; [eauto|].
  apply (ctxs_not_val Hctx) in Hnval.
  destruct (ctx_none_step_not_val H Hnval Hstep) as (e2' & -> & H').
  destruct (IHHctx _ H') as (e3 & -> & H3).
  eauto.
Qed.

Ltac none_unique_tac := repeat
  match goal with
  | H : ctx_trace _ |- _ => inv H
  | H : none_step_trace (EVal _) _ _ _ _ |- _ => by apply not_none_step_trace_val in H
  | H : pure_step_trace _ _ _ |- _ => inv H
  | H : head_step_trace _ _ _ _ _ |- _ => inv H
  | H : none_step_trace _ _ _ _ _ |- _ => inv H
  | _ => intros || reflexivity
  end.

Lemma none_head_step_trace_unique {e1 h1 e2 h2 b} :
  head_step_trace e1 h1 e2 h2 b ->
  forall e2' h2' t,
    none_step_trace e1 h1 e2' h2' t ->
    t = Base' b.
Proof. none_unique_tac. Qed.

Lemma none_step_base_unique {e1 h1 e2 h2 b} :
  none_step_trace e1 h1 e2 h2 (Base' b) ->
  forall e2' h2' t,
    none_step_trace e1 h1 e2' h2' t ->
    t = Base' b.
Proof.
  intros Hstep e2' h2' t Hstep'.
  destruct (none_step_base_ctxs Hstep) as
    (k & e & e' & Hctx & -> & -> & Hhead).
  assert (Hnval := none_step_trace_not_val
    (do_head_step_trace_none_event _ _ _ _ _ Hhead)).
  destruct (ctxs_none_step_not_val Hctx Hnval Hstep') as
    (e2'' & -> & Hstep'').
  apply (none_head_step_trace_unique Hhead _ _ _ Hstep'').
Qed.

Lemma none_step_nondeterministic_can_swap {e1 h1 e2 e2' h2 h2' t t'} :
  none_step_trace e1 h1 e2 h2 t ->
  none_step_trace e1 h1 e2' h2' t' ->
  t ≠ t' ->
  none_can_swap t t'.
Proof.
  revert e1 h1 e2 h2 e2' h2' t'.
  induction t; intros e1 h1 e2 h2 e2' h2' t' Hstep Hstep' Hne.
  - by assert (Heq := none_step_base_unique Hstep _ _ _ Hstep').
  - destruct t'.
    + by assert (Heq := none_step_base_unique Hstep' _ _ _ Hstep).
    + constructor.
      destruct (none_step_left_ctxs Hstep) as
        (k & e1' & e1'' & er & Hctx & -> & -> & Hstep1).
      destruct (none_step_left_in_context Hctx Hstep') as
        (e1''' & -> & Hstep2).
      eapply IHt; [done..|]. intros Heq. simplify_eq.
    + constructor.
  - destruct t'.
    + by assert (Heq := none_step_base_unique Hstep' _ _ _ Hstep).
    + constructor.
    + constructor.
      destruct (none_step_right_ctxs Hstep) as
        (k & e1' & e1'' & er & Hctx & -> & -> & Hstep1).
      destruct (none_step_right_in_context Hctx Hstep') as
        (e1''' & -> & Hstep2).
      eapply IHt; try done. intros Heq. simplify_eq.
Qed.

Lemma not_some_remove_none_is_empty t :
  Forall (λ x, ¬ is_some x) t ->
  remove_none_map from_none_event t = [].
Proof.
  induction t; [done|].
  intros Hnone.
  apply Forall_cons_1 in Hnone. destruct Hnone as [Ha Hnone].
  simpl. destruct (from_none_event a) eqn:Hfne.
  - exfalso. revert e Hfne. induction a; intros e Hfne.
    + by destruct o.
    + simpl in Ha, Hfne.
      destruct (from_none_event a); eauto.
    + simpl in Ha, Hfne.
      destruct (from_none_event a); eauto.
  - by apply IHt.
Qed.

Lemma remove_none_map_cons {A B : Type} (f : A -> option B) (b : A) (t t' : list A) :
  remove_none_map f t = remove_none_map f t' ->
  remove_none_map f (b :: t) = remove_none_map f (b :: t').
Proof.
  intros Heq. simpl.
  destruct (f b) eqn:Hfb;
  by [f_equal|].
Qed.

Lemma remove_none_map_app {A B : Type} (f : A -> option B) (t t' : list A) :
  remove_none_map f (t ++ t') =
    remove_none_map f t ++ remove_none_map f t'.
Proof.
  induction t; [done|].
  simpl. destruct (f a) eqn:Hfa;
  by [rewrite IHt|].
Qed.

Lemma none_step_trace_heap_eq {e1 h1 e2 h2 b} :
  none_step_trace e1 h1 e2 h2 b ->
  ¬ is_some b ->
  h1 = h2.
Proof.
  intros Hstep Hnone.
  apply step_trace_none_to_step_trace in Hstep.
  assert (Heq : from_none_event b = None).
  - clear Hstep. induction b; simpl in *.
    + by destruct o.
    + by rewrite IHb.
    + by rewrite IHb.
  - rewrite Heq in Hstep.
    by eapply step_trace_none_eq.
Qed.

(* Currently unused *)
Lemma none_steps_split e e'' h h'' (t t' : none_trace) :
  none_steps_trace e h e'' h'' (t ++ t') ->
  exists e' h',
    none_steps_trace e h e' h' t /\
    none_steps_trace e' h' e'' h'' t'.
Proof.
  intros Hsteps. remember (t ++ t') as tt'. revert t t' Heqtt'.
  induction Hsteps; intros t' t'' Heqtt'.
  - symmetry in Heqtt'. apply app_eq_nil in Heqtt' as [-> ->].
    eauto using none_steps_trace.
  - destruct t'; simpl in *; simplify_eq.
    + eauto using none_steps_trace.
    + destruct (IHHsteps _ _ eq_refl) as (e' & h' & Hfst & Hsnd).
      eauto using none_steps_trace.
Qed.

Lemma none_step_trace_event_postponed {e1 h1 e2 h2 b e2' h2' b'} :
  none_step_trace e1 h1 e2 h2 b ->
  none_step_trace e1 h1 e2' h2' b' -> 
  b ≠ b' ->
  exists e3 h3, none_step_trace e2' h2' e3 h3 b.
Proof.
  intros Hstep Hstep'. revert e2 h2 b Hstep.
  induction Hstep'; intros e'' h'' b' Hstep Hne.
  - by eapply none_head_step_trace_unique in H.
  - apply none_step_trace_not_val in Hstep'.
    destruct (ctx_none_step_not_val H Hstep' Hstep) as (e2 & -> & H2).
    destruct (IHHstep' _ _ _ H2 Hne) as (e3 & h3 & H3).
    eauto using none_step_trace.
  - inv Hstep.
    + inv H. inv H0. by apply none_step_trace_not_val in Hstep'.
    + inv H0.
    + destruct (IHHstep' _ _ _ H5) as (? & ? & ?); [intros ?; simplify_eq|].
      eauto using none_step_trace.
    + eapply none_step_heap_indifferent in H5.
      destruct H5 as [h2' H5]. eauto using none_step_trace.
  - inv Hstep.
    + inv H. inv H0. by apply none_step_trace_not_val in Hstep'.
    + inv H0.
    + eapply none_step_heap_indifferent in H5.
      destruct H5 as [h2' H5]. eauto using none_step_trace.
    + destruct (IHHstep' _ _ _ H5) as (? & ? & ?); [intros ?; simplify_eq|].
      eauto using none_step_trace.
Qed.

Lemma none_steps_trace_event_postponed {e1 h1 e2 h2 b e2' h2' t} :
  none_step_trace e1 h1 e2 h2 b ->
  none_steps_trace e1 h1 e2' h2' t ->
  ¬ In b t ->
  exists e3 h3, none_step_trace e2' h2' e3 h3 b.
Proof.
  intros Hstep Hsteps. revert e2 h2 Hstep.
  induction Hsteps; intros e2' h2' Hstep Hnin; [eauto|..]; simpl in Hnin.
  destruct (none_step_trace_event_postponed Hstep H) as (e3' & h3' & H3); eauto.
Qed.

Lemma none_steps_trace_in_trace {e1 h1 v h2 t} :
  none_steps_trace e1 h1 (EVal v) h2 t ->
  forall e' h' b, none_step_trace e1 h1 e' h' b ->
  In b t.
Proof.
  revert e1 h1 v h2. induction t; intros e1 h1 v h2 Hsteps e' h' b Hstep.
  - exfalso. revert e' h' b Hstep. remember (EVal v) as ev. remember [] as t.
    induction Hsteps; simplify_eq; intros e' h' b Hstep.
    by eapply not_none_step_trace_val.
  - destruct b.
    + inv Hsteps.
      assert (Heq := none_step_base_unique Hstep _ _ _ H5).
      simplify_eq. apply in_eq.
    + destruct (none_event_eq_dec (Left' b) a) as [<- | Hne]; [apply in_eq|].
      inv Hsteps.
      destruct (none_step_trace_event_postponed Hstep H5) as
        (e0' & h0' & H0'); [done|].
      by eapply in_cons, IHt.
    + destruct (none_event_eq_dec (Right' b) a) as [<- | Hne]; [apply in_eq|].
      inv Hsteps.
      destruct (none_step_trace_event_postponed Hstep H5) as
        (e0' & h0' & H0'); [done|].
      by eapply in_cons, IHt.
Qed.

Lemma all_can_swap_none_perm {a t} :
  Forall (λ x, none_can_swap a x) t ->
  none_perm (a :: t) (t ++ [a]).
Proof.
  intros H. induction t; [constructor|].
  apply Forall_cons_1 in H. destruct H as [Hswap H].
  eapply none_perm_trans; [by apply none_perm_swap|].
  by apply none_perm_skip, IHt.
Qed.

Lemma Forall_none_perm P t t' :
  none_perm t t' ->
  Forall P t ->
  Forall P t'.
Proof.
  intros Hperm H.
  induction Hperm; eauto;
  rewrite !Forall_cons_iff in H;
  rewrite !Forall_cons_iff;
  tauto.
Qed.
