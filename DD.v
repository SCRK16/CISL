From Coq Require Export Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Program.Equality.
From Coq Require Import Bool.DecBool.
Require Import perm.
From iris.proofmode Require Import tactics.
From stdpp Require Import countable.
From Coq Require Import RelationClasses.

Definition imm_stuck (e : expr) (h : lock_heap) :=
  ¬ is_val e /\ forall e' h', ¬ step e h e' h'.

Definition stuck (e : expr) (h : lock_heap) := 
  exists e' h', steps e h e' h' /\ imm_stuck e' h'.

Lemma imm_stuck_par e e' h :
  imm_stuck e h ->
  imm_stuck e' h ->
  imm_stuck (EPar e e') h.
Proof.
  intros [Hnvale Hnstepe] [Hnvale' Hnstepe'].
  split; [auto |].
  intros ep hp Hstep.
  inv Hstep.
  inv H0.
  - inv H1. by inv H.
  - inv H2.
    + eapply Hnstepe.
      by apply do_step.
    + eapply Hnstepe'.
      by apply do_step.
Qed.

(***
Goal: Proof that certain programs get stuck because of a deadlock
Difficult with just the definition of stuck, since we need all threads
to step in the exact correct order for the deadlock to show up, and then
also proof that the program can not step to any other expression anymore.
We will take a different approach: Proof that programs contain a deadlock,
which will then imply that the program can get stuck
***)


(************************
        HISTORIES
************************)

(***
Define new step relation steps_trace
This is a step relation that also keeps track of a trace (history),
the events that have happened during the execution of the program
****)

Notation Join := perm.Join.

Inductive pure_step_trace : expr -> expr -> option base_event -> Prop :=
  | Amb_step_trace n :
      pure_step_trace EAmb (EVal (VNat n)) None
  | Pair_step_trace v1 v2 :
      pure_step_trace (EPair (EVal v1) (EVal v2)) (EVal (VPair v1 v2)) None
  | Fst_step_trace v1 v2 :
      pure_step_trace (EFst (EVal (VPair v1 v2))) (EVal v1) None
  | Snd_step_trace v1 v2 :
      pure_step_trace (ESnd (EVal (VPair v1 v2))) (EVal v2) None
  | Let_step_trace y e v :
      pure_step_trace (ELet y (EVal v) e) (subst y v e) None
  | Op_step_trace op v1 v2 v3 :
      eval_bin_op op v1 v2 = Some v3 ->
      pure_step_trace (EOp op (EVal v1) (EVal v2)) (EVal v3) None
  | If_true_step_trace e1 e2 :
      pure_step_trace (EIf (EVal (VBool true)) e1 e2) e1 None
  | If_false_step_trace e1 e2 :
      pure_step_trace (EIf (EVal (VBool false)) e1 e2) e2 None
  | While_step_trace e1 e2 :
      pure_step_trace (EWhile e1 e2) (EIf e1 (ESeq e2 (EWhile e1 e2)) (EVal VUnit)) None
  | Seq_step_trace v e :
      pure_step_trace (ESeq (EVal v) e) e None
  | Par_step_trace v1 v2 :
      pure_step_trace (EPar (EVal v1) (EVal v2)) (EVal (VPair v1 v2)) (Some Join).

Inductive head_step_trace :
  expr -> lock_heap ->
  expr -> lock_heap ->
  option base_event -> Prop :=
  | do_pure_step_trace e e' h b :
      pure_step_trace e e' b ->
      head_step_trace e h e' h b
  | Lock_head_step_trace h l :
      head_step_trace
        (ELock (EVal (VRef l))) h
        (EVal VUnit) (<[ l := true ]> h)
        (Some (Lock l))
  | Unlock_head_step_trace h l :
      head_step_trace
        (EUnlock (EVal (VRef l))) h
        (EVal VUnit) (<[ l := false ]> h)
        (Some (Unlock l)).

Global Hint Constructors pure_step_trace : headstep.
Global Hint Constructors head_step_trace : headstep.

Inductive ctx_trace : (expr -> expr) -> Prop :=
  | pair_l_ctx_trace e : ctx_trace (fun x => EPair x e)
  | pair_r_ctx_trace v : ctx_trace (EPair (EVal v))
  | fst_ctx_trace : ctx_trace EFst
  | snd_ctx_trace : ctx_trace ESnd
  | let_ctx_trace y e : ctx_trace (fun x => ELet y x e)
  | op_l_ctx_trace op e : ctx_trace (fun x => EOp op x e)
  | op_r_ctx_trace op v : ctx_trace (fun x => EOp op (EVal v) x)
  | if_ctx_trace e1 e2 : ctx_trace (fun x => EIf x e1 e2)
  | seq_ctx_trace e : ctx_trace (fun x => ESeq x e)
  | lock_ctx_trace : ctx_trace ELock
  | unlock_ctx_trace : ctx_trace EUnlock.

Lemma ctx_trace_ctx1 k :
  ctx_trace k ->
  ctx1 k.
Proof.
  intros Hctx.
  inv Hctx; constructor.
Qed.

Lemma ctx_trace_injective k e e' :
  ctx_trace k ->
  k e = k e' ->
  e = e'.
Proof.
  intros Hctx Hk.
  induction Hctx;
  injection Hk; tauto.
Qed.

Lemma ctx_trace_unique e e' k k' :
  ctx_trace k ->
  ctx_trace k' ->
  ¬ is_val e ->
  ¬ is_val e' ->
  k e = k' e' ->
  k = k' /\ e = e'.
Proof.
  intros Hctx Hctx' Hnval Hnval' Heq.
  induction Hctx; by inv Hctx'.
Qed.

Global Hint Constructors ctx_trace : context.
Global Hint Resolve ctx_trace_ctx1 : context.

Inductive step_trace :
  expr -> lock_heap ->
  expr -> lock_heap ->
  option event -> Prop :=
  | do_head_step_trace e h e' h' (b : option base_event) :
      head_step_trace e h e' h' b ->
      step_trace e h e' h' (option_map Base b)
  | ctx_step_trace k e h e' h' (b : option event) :
      ctx_trace k ->
      step_trace e h e' h' b ->
      step_trace (k e) h (k e') h' b
  | par_l_step_trace e1 e2 h e1' h' (b : option event) :
      step_trace e1 h e1' h' b ->
      step_trace (EPar e1 e2) h (EPar e1' e2) h' (option_map Left b)
  | par_r_step_trace e1 e2 h e2' h' (b : option event) :
      step_trace e2 h e2' h' b ->
      step_trace (EPar e1 e2) h (EPar e1 e2') h' (option_map Right b).

Global Hint Resolve do_head_step_trace : headstep.

Lemma head_step_trace_some e h e' h' (b : base_event) :
  head_step_trace e h e' h' (Some b) ->
  step_trace e h e' h' (Some (Base b)).
Proof. intros. by eapply do_head_step_trace in H. Qed.

Lemma head_step_trace_none e h e' h' :
  head_step_trace e h e' h' None ->
  step_trace e h e' h' None.
Proof. intros. by eapply do_head_step_trace in H. Qed.

Lemma par_l_step_trace_some e1 e2 h e1' h' (b : event) :
  step_trace e1 h e1' h' (Some b) ->
  step_trace (EPar e1 e2) h (EPar e1' e2) h' (Some (Left b)).
Proof. intros. by eapply par_l_step_trace in H. Qed.

Lemma par_r_step_trace_some e1 e2 h e2' h' (b : event) :
  step_trace e2 h e2' h' (Some b) ->
  step_trace (EPar e1 e2) h (EPar e1 e2') h' (Some (Right b)).
Proof. intros. by eapply par_r_step_trace in H. Qed.

Lemma par_l_step_trace_none e1 e2 h e1' h' :
  step_trace e1 h e1' h' None ->
  step_trace (EPar e1 e2) h (EPar e1' e2) h' None.
Proof. intros. by eapply par_l_step_trace in H. Qed.

Lemma par_r_step_trace_none e1 e2 h e2' h' :
  step_trace e2 h e2' h' None ->
  step_trace (EPar e1 e2) h (EPar e1 e2') h' None.
Proof. intros. by eapply par_r_step_trace in H. Qed.

Lemma let_not_recursive s e1 e2 :
  ¬ e2 = ELet s e1 e2.
Proof.
  intros H. induction e2; done || simplify_eq.
Qed.

Lemma step_trace_not_eq' e1 h1 e2 h2 t :
  e1 = e2 ->
  ¬ step_trace e1 h1 e2 h2 t.
Proof.
  intros Heq Hstep.
  induction Hstep; simplify_eq.
  - inv H. inv H0.
    + induction e; done || simpl in H2.
      * by destruct (string_dec s y).
      * destruct (string_dec y s); simplify_eq.
        by eapply let_not_recursive.
    + induction e1; simplify_eq.
    + induction e2; simplify_eq.
    + induction e; simplify_eq.
  - eauto using ctx_trace_injective.
Qed.

Lemma step_trace_not_val e h e' h' t :
  step_trace e h e' h' t ->
  ¬ is_val e.
Proof.
  intros Hstep.
  induction Hstep; [.. | tauto | tauto].
  - inv H; [inv H0|..]; tauto.
  - by apply not_is_val_ctx1, ctx_trace_ctx1.
Qed.

Lemma step_trace_not_eq e h1 h2 t :
  ¬ step_trace e h1 e h2 t.
Proof. by apply step_trace_not_eq'. Qed.

Inductive steps_trace : expr -> lock_heap -> expr -> lock_heap -> trace -> Prop :=
  | steps_refl_trace e h :
      steps_trace e h e h []
  | steps_step_none e1 h1 e2 h2 e3 h3 (t : trace) :
      step_trace e1 h1 e2 h2 None ->
      steps_trace e2 h2 e3 h3 t ->
      steps_trace e1 h1 e3 h3 t
  | steps_step_some e1 h1 e2 h2 e3 h3 (b : event) (t : trace) :
      step_trace e1 h1 e2 h2 (Some b) ->
      steps_trace e2 h2 e3 h3 t ->
      steps_trace e1 h1 e3 h3 (b :: t).

Lemma step_trace_none_eq {e1 h1 e2 h2} :
  step_trace e1 h1 e2 h2 None ->
  h1 = h2.
Proof.
  intros Hstep. remember None as n.
  induction Hstep; [by inv H | eauto |..];
  destruct b; done || tauto.
Qed.

Lemma steps_trace_none_eq {e1 h1 e2 h2} :
  steps_trace e1 h1 e2 h2 [] ->
  h1 = h2.
Proof.
  intros Hstep. remember [] as t.
  induction Hstep; [done | | done].
  rewrite <- (IHHstep Heqt).
  by eapply step_trace_none_eq.
Qed.

Create HintDb step_trace.
Global Hint Constructors
  steps_trace head_step_trace pure_step_trace : step_trace.
Global Hint Resolve
  head_step_trace_some  head_step_trace_none
  par_l_step_trace_some par_r_step_trace_some
  par_l_step_trace_none par_r_step_trace_none : step_trace.

Lemma step_once_none e e' h h' : 
  step_trace e h e' h' None ->
  steps_trace e h e' h' [].
Proof.
  intros Hstep.
  eauto using steps_trace.
Qed.

Lemma step_once_some e e' h h' (b : event) :
  step_trace e h e' h' (Some b) ->
  steps_trace e h e' h' [b].
Proof.
  intros Hstep.
  eauto using steps_trace.
Qed.

Lemma steps_left {e1 e2 e' h h' t t'} :
  steps_trace e1 h e2 h' t ->
  map Left t = t' ->
  steps_trace (EPar e1 e') h (EPar e2 e') h' t'.
Proof.
  intros Hsteps H. revert t' H.
  induction Hsteps; intros t' H'.
  - simplify_eq. simpl. constructor.
  - eapply steps_step_none; [|eauto].
    by apply par_l_step_trace_none.
  - simpl in H'. simplify_eq.
    eapply steps_step_some; [|eauto].
    by apply par_l_step_trace_some.
Qed.

Lemma steps_right {e1 e2 e' h h' t t'} :
  steps_trace e1 h e2 h' t ->
  map Right t = t' ->
  steps_trace (EPar e' e1) h (EPar e' e2) h' t'.
Proof.
  intros Hsteps H. revert t' H.
  induction Hsteps; intros t' H'.
  - simplify_eq. simpl. constructor.
  - eapply steps_step_none; [|eauto].
    by apply par_r_step_trace_none.
  - simpl in H'. simplify_eq.
    eapply steps_step_some; [|eauto].
    by apply par_r_step_trace_some.
Qed.

Lemma steps_context_steps e e' h h' k (t : trace) :
  ctx_trace k ->
  steps_trace e h e' h' t ->
  steps_trace (k e) h (k e') h' t.
Proof.
  intros Hctx Hsteps.
  induction Hsteps;
  eauto using steps_trace, step_trace.
Qed.

Lemma steps_trans e e' e'' h h' h'' (t t' : trace) :
  steps_trace e h e' h' t ->
  steps_trace e' h' e'' h'' t' ->
  steps_trace e h e'' h'' (t ++ t').
Proof.
  intros H. revert t'.
  induction H; [done | |]; intros t' H';
  eauto using steps_trace.
Qed.

Lemma steps_trans' e e' e'' h h' h'' (t t' t'' : trace) :
  steps_trace e h e' h' t ->
  steps_trace e' h' e'' h'' t' ->
  t ++ t' = t'' ->
  steps_trace e h e'' h'' t''.
Proof.
  intros Hsteps Hsteps' <-.
  by eapply steps_trans.
Qed.

Lemma steps_split e e'' h h'' (t t' : trace) :
  steps_trace e h e'' h'' (t ++ t') ->
  exists e' h',
    steps_trace e h e' h' t /\
    steps_trace e' h' e'' h'' t'.
Proof.
  intros Hsteps. remember (t ++ t') as tt'. revert t t' Heqtt'.
  induction Hsteps; intros t' t'' Heqtt'.
  - symmetry in Heqtt'. apply app_eq_nil in Heqtt' as [-> ->].
    exists e, h. eauto with step_trace.
  - destruct (IHHsteps _ _ Heqtt') as (e' & h' & Hfst & Hsnd).
    exists e', h'. split; [|done].
    by eapply steps_step_none.
  - destruct t'; simpl in *; simplify_eq.
    + exists e1, h1. split; [constructor|].
      by eapply steps_step_some.
    + destruct (IHHsteps _ _ eq_refl) as (e' & h' & Hfst & Hsnd).
      exists e', h'. split; [|done].
      by eapply steps_step_some.
Qed.

Inductive ctxs_trace : (expr -> expr) -> Prop :=
  | Id_ctxs_trace : ctxs_trace (λ x, x)
  | Compose_ctxs_trace k1 k2 :
      ctx_trace k1 ->
      ctxs_trace k2 ->
      ctxs_trace (λ x, k1 (k2 x)).

Global Hint Constructors ctxs_trace : context.

Lemma ctxs_single_ctx (k : expr -> expr) :
  ctx_trace k ->
  ctxs_trace k.
Proof. eauto with context. Qed.

Lemma ctxs_step e1 h1 e2 h2 b k :
  ctxs_trace k ->
  step_trace e1 h1 e2 h2 b ->
  step_trace (k e1) h1 (k e2) h2 b.
Proof.
  intros Hctx Hstep.
  induction Hctx; by [|constructor].
Qed.

Lemma ctxs_steps {e1 h1 e2 h2 b k} :
  ctxs_trace k ->
  steps_trace e1 h1 e2 h2 b ->
  steps_trace (k e1) h1 (k e2) h2 b.
Proof.
  intros Hctx Hsteps.
  induction Hctx; [done|].
  by apply steps_context_steps.
Qed.

Lemma ctx_not_val {e k} :
  ctx_trace k ->
  ¬ is_val (k e).
Proof.
  intros Hctx.
  inv Hctx; tauto.
Qed.

Lemma ctxs_not_val {e k} :
  ctxs_trace k ->
  ¬ is_val e ->
  ¬ is_val (k e).
Proof.
  intros Hctx Hnval.
  inv Hctx; by [|apply ctx_not_val].
Qed.

Lemma ctx_step_not_val {e1 h1 e2 h2 b k} :
  ctx_trace k ->
  ¬ is_val e1 ->
  step_trace (k e1) h1 e2 h2 b ->
  exists e2', e2 = k e2' /\
    step_trace e1 h1 e2' h2 b.
Proof.
  intros Hctx Hnval Hstep.
  inv Hstep; [| |inv Hctx..].
  - inv H; [|by inv Hctx..].
    by inv H0; inv Hctx.
  - assert (Hnval' := step_trace_not_val _ _ _ _ _ H1).
    destruct (ctx_trace_unique _ _ _ _ H0 Hctx Hnval' Hnval H) as [-> ->].
    eauto.
Qed.

Lemma step_left_ctxs {e1 h1 e2 h2 t} :
  step_trace e1 h1 e2 h2 (Some (Left t)) ->
  exists k e1' e2' e,
    ctxs_trace k /\
    e1 = k (EPar e1' e) /\
    e2 = k (EPar e2' e) /\
    step_trace e1' h1 e2' h2 (Some t).
Proof.
  intros Hstep. remember (Some (Left t)) as Lt.
  induction Hstep; [by destruct b | | | by destruct b].
  - destruct (IHHstep HeqLt) as (k0 & e1' & e2' & e0 & Hctx & -> & -> & Hstep').
    exists (λ x, k (k0 x)), e1', e2', e0.
    repeat split; eauto with context.
  - destruct b; [|done]. simpl in HeqLt. simplify_eq.
    exists (λ x, x), e1, e1', e2.
    repeat split; eauto with context.
Qed.

Lemma step_right_ctxs {e1 h1 e2 h2 t} :
  step_trace e1 h1 e2 h2 (Some (Right t)) ->
  exists k e1' e2' e,
    ctxs_trace k /\
    e1 = k (EPar e e1') /\
    e2 = k (EPar e e2') /\
    step_trace e1' h1 e2' h2 (Some t).
Proof.
  intros Hstep. remember (Some (Right t)) as Rt.
  induction Hstep; [by destruct b | | by destruct b |].
  - destruct (IHHstep HeqRt) as (k0 & e1' & e2' & e0 & Hctx & -> & -> & Hstep').
    exists (λ x, k (k0 x)), e1', e2', e0.
    repeat split; eauto with context.
  - destruct b; [|done]. simpl in HeqRt. simplify_eq.
    exists (λ x, x), e2, e2', e1.
    repeat split; eauto with context.
Qed.

Lemma step_trace_none_heap_indifferent {e h e' h'} :
  step_trace e h e' h' None ->
  forall h'', step_trace e h'' e' h'' None.
Proof.
  intros Hstep h''. remember None as t.
  induction Hstep.
  - constructor. destruct b; [done|simpl].
    inv H. by constructor.
  - constructor; tauto.
  - constructor. destruct b; [done|tauto].
  - apply par_r_step_trace. destruct b; [done|tauto].
Qed.

Lemma steps_trace_none_heap_indifferent {e h e' h'} :
  steps_trace e h e' h' [] ->
  forall h'', steps_trace e h'' e' h'' [].
Proof.
  intros Hsteps h''. remember [] as t.
  induction Hsteps; [constructor | | done].
  specialize (IHHsteps Heqt).
  eapply steps_step_none; [|done].
  by eapply step_trace_none_heap_indifferent.
Qed.

Lemma step_none_without_context {e1 e2 h e3} :
  step_trace (EPar e1 e2) h e3 h None ->
  (exists e1', e3 = (EPar e1' e2) /\ step_trace e1 h e1' h None) \/
  (exists e2', e3 = (EPar e1 e2') /\ step_trace e2 h e2' h None).
Proof.
  intros Hstep.
  inv Hstep.
  - inv H4. inv H0.
  - inv H0.
  - left. exists e1'. split; [done|].
    rewrite H5. by destruct b.
  - right. exists e2'. split; [done|].
    rewrite H5. by destruct b.
Qed.

Lemma step_none_in_context {e1 e2 h e3 k} :
  ctxs_trace k ->
  step_trace (k (EPar e1 e2)) h e3 h None ->
  (exists e1', e3 = k (EPar e1' e2) /\ step_trace e1 h e1' h None) \/
  (exists e2', e3 = k (EPar e1 e2') /\ step_trace e2 h e2' h None).
Proof.
  intros Hctx. revert e1 e2 e3 h.
  induction Hctx; intros e1 e2 e3 h Hstep.
  - by apply step_none_without_context.
  - assert (Hnval : ¬ is_val (k2 (EPar e1 e2))) by (apply ctxs_not_val; tauto).
    destruct (ctx_step_not_val H Hnval Hstep) as (e' & -> & Hstep').
    destruct (IHHctx _ _ _ _ Hstep') as [(e1' & -> & IH) | (e2' & -> & IH)];
    eauto.
Qed.

Lemma step_left_some_without_context {e1 e2 h1 e3 h2 t} :
  step_trace (EPar e1 e2) h1 e3 h2 (Some (Left t)) ->
  exists e1', e3 = EPar e1' e2 ∧ step_trace e1 h1 e1' h2 (Some t).
Proof.
  intros Hstep. inv Hstep.
  - destruct b; [|done]. inv H4.
  - inv H0.
  - destruct b; [|done]. simpl in H5. simplify_eq. eauto.
  - by destruct b.
Qed.

Lemma step_left_some_in_context {e1 e2 h1 e3 h2 k t} :
  ctxs_trace k ->
  step_trace (k (EPar e1 e2)) h1 e3 h2 (Some (Left t)) ->
  exists e1', e3 = k (EPar e1' e2) /\ step_trace e1 h1 e1' h2 (Some t).
Proof.
  intros Hctx. revert e1 e2 e3 h1 h2 t.
  induction Hctx; intros e1 e2 e3 h1 h2 t Hstep;
  (* Case: k = λ x, x *)
  [by apply step_left_some_without_context|].
  (* Case: k = λ x, k1 (k2 x) *)
  assert (Hnval : ¬ is_val (k2 (EPar e1 e2))) by (apply ctxs_not_val; tauto).
  destruct (ctx_step_not_val H Hnval Hstep) as (e' & -> & Hstep').
  destruct (IHHctx _ _ _ _ _ _ Hstep') as (e1' & -> & IH).
  eauto.
Qed.

Lemma step_right_some_without_context {e1 e2 h1 e3 h2 t} :
  step_trace (EPar e1 e2) h1 e3 h2 (Some (Right t)) ->
  exists e2', e3 = EPar e1 e2' ∧ step_trace e2 h1 e2' h2 (Some t).
Proof.
  intros Hstep. inv Hstep.
  - destruct b; [|done]. inv H4.
  - inv H0.
  - by destruct b.
  - destruct b; [|done]. simpl in H5. simplify_eq. eauto.
Qed.

Lemma step_right_some_in_context {e1 e2 h1 e3 h2 k t} :
  ctxs_trace k ->
  step_trace (k (EPar e1 e2)) h1 e3 h2 (Some (Right t)) ->
  exists e2', e3 = k (EPar e1 e2') /\ step_trace e2 h1 e2' h2 (Some t).
Proof.
  intros Hctx. revert e1 e2 e3 h1 h2 t.
  induction Hctx; intros e1 e2 e3 h1 h2 t Hstep;
  [by apply step_right_some_without_context|].
  assert (Hnval : ¬ is_val (k2 (EPar e1 e2))) by (apply ctxs_not_val; tauto).
  destruct (ctx_step_not_val H Hnval Hstep) as (e' & -> & Hstep').
  destruct (IHHctx _ _ _ _ _ _ Hstep') as (e2' & -> & IH).
  eauto.
Qed.

Lemma steps_left_in_context {e1 e2 h1 e3 h2 t k} :
  ctxs_trace k ->
  steps_trace (k (EPar e1 e2)) h1 e3 h2 [Left t] ->
  exists e3' e2',
    steps_trace (k (EPar e1 e2)) h1 (k (EPar e3' e2')) h2 [Left t] /\
    steps_trace e2 h1 e2' h1 [] /\
    steps_trace e1 h1 e3' h2 [t] /\
    steps_trace (k (EPar e3' e2')) h2 e3 h2 [].
Proof.
  intros Hctx Hsteps. dependent induction Hsteps.
  - assert (Heq := step_trace_none_eq H). subst.
    destruct (step_none_in_context Hctx H) as [(e1' & -> & H') | (e2' & -> & H')].
    + specialize (IHHsteps k Hctx t e2 e1' eq_refl JMeq_refl).
      destruct IHHsteps as (e1'' & e2' & HL & HR & Ht & Hafter).
      exists e1'', e2'. repeat split; eauto with step_trace.
    + specialize (IHHsteps k Hctx t e2' e1 eq_refl JMeq_refl).
      destruct IHHsteps as (e1'' & e2'' & HL & HR & Ht & Hafter).
      exists e1'', e2''. repeat split; eauto with step_trace.
  - assert (Heq := steps_trace_none_eq Hsteps). subst.
    destruct (step_left_some_in_context Hctx H) as (e1' & -> & H').
    exists e1', e2. repeat split; eauto with step_trace.
Qed.

Lemma steps_right_in_context {e1 e2 h1 e3 h2 t k} :
  ctxs_trace k ->
  steps_trace (k (EPar e1 e2)) h1 e3 h2 [Right t] ->
  exists e3' e1',
    steps_trace (k (EPar e1 e2)) h1 (k (EPar e1' e3')) h2 [Right t] /\
    steps_trace e1 h1 e1' h1 [] /\
    steps_trace e2 h1 e3' h2 [t] /\
    steps_trace (k (EPar e1' e3')) h2 e3 h2 [].
Proof.
  intros Hctx Hsteps. dependent induction Hsteps.
  - assert (Heq := step_trace_none_eq H). subst.
    destruct (step_none_in_context Hctx H) as [(e1' & -> & H') | (e2' & -> & H')].
    + specialize (IHHsteps k Hctx t e2 e1' eq_refl JMeq_refl).
      destruct IHHsteps as (e1'' & e2' & HL & HR & Ht & Hafter).
      exists e1'', e2'. repeat split; eauto with step_trace.
    + specialize (IHHsteps k Hctx t e2' e1 eq_refl JMeq_refl).
      destruct IHHsteps as (e1'' & e2'' & HL & HR & Ht & Hafter).
      exists e1'', e2''. repeat split; eauto with step_trace.
  - assert (Heq := steps_trace_none_eq Hsteps). subst.
    destruct (step_right_some_in_context Hctx H) as (e2' & -> & H').
    exists e2', e1. repeat split; eauto with step_trace.
Qed.

Lemma steps_one_split {e1 h1 e2 h2 t} :
  steps_trace e1 h1 e2 h2 [t] ->
  exists e1' e2',
    steps_trace e1 h1 e1' h1 [] /\
    step_trace e1' h1 e2' h2 (Some t) /\
    steps_trace e2' h2 e2 h2 [].
Proof.
  intros Hsteps. remember [t] as tt.
  induction Hsteps; [done|simplify_eq..].
  - destruct (IHHsteps eq_refl) as (e1' & e2' & Hsteps1 & Hstep & Hsteps2).
    assert (Heq := step_trace_none_eq H). subst.
    exists e1', e2'. repeat split; try done.
    by eapply steps_step_none.
  - assert (Heq := steps_trace_none_eq Hsteps). subst.
    exists e1, e2. repeat split; eauto using steps_trace.
Qed.

Lemma steps_two_split_left_right {e1 h1 e2 h2 t e3 h3 t'} :
  step_trace e1 h1 e2 h2 (Some (Left t)) ->
  steps_trace e2 h2 e3 h3 [Right t'] ->
  exists e1' e2' e3',
    steps_trace e1 h1 e1' h1 [] /\
    step_trace e1' h1 e2' h2 (Some (Left t)) /\
    step_trace e2' h2 e3' h3 (Some (Right t')) /\
    steps_trace e3' h3 e3 h3 [].
Proof.
  intros Hstep Hsteps.
  destruct (step_left_ctxs Hstep) as
    (k & e1' & e1'' & e2' & Hctx & -> & -> & Hstep').
  destruct (steps_right_in_context Hctx Hsteps) as
    (e2'' & e1''' & Hsteps' & H1 & H2 & H3).
  destruct (steps_one_split H2) as
    (e2'1 & e2'2 & H2'1 & H2'2 & H2'3).
  exists (k (EPar e1' e2'1)), (k (EPar e1'' e2'1)), (k (EPar e1'' e2'2)).
  repeat split.
  - apply ctxs_steps; [done|].
    eapply steps_right; by [eapply steps_trace_none_heap_indifferent|].
  - apply ctxs_step; [done|].
    by apply par_l_step_trace_some.
  - apply ctxs_step; [done|].
    by apply par_r_step_trace_some.
  - eapply steps_trans'.
    + eapply ctxs_steps; [done|].
      by eapply steps_right.
    + eapply steps_trans'; [|done..].
      apply ctxs_steps; [done|].
      eapply steps_left; by [eapply steps_trace_none_heap_indifferent|].
    + done.
Qed.

Lemma steps_two_split_right_left {e1 h1 e2 h2 t e3 h3 t'} :
  step_trace e1 h1 e2 h2 (Some (Right t)) ->
  steps_trace e2 h2 e3 h3 [Left t'] ->
  exists e1' e2' e3',
    steps_trace e1 h1 e1' h1 [] /\
    step_trace e1' h1 e2' h2 (Some (Right t)) /\
    step_trace e2' h2 e3' h3 (Some (Left t')) /\
    steps_trace e3' h3 e3 h3 [].
Proof.
  intros Hstep Hsteps.
  destruct (step_right_ctxs Hstep) as
    (k & e2' & e2'' & e1' & Hctx & -> & -> & Hstep').
  destruct (steps_left_in_context Hctx Hsteps) as
    (e1'' & e2''' & Hsteps' & H1 & H2 & H3).
  destruct (steps_one_split H2) as
    (e1'1 & e1'2 & H1'1 & H1'2 & H1'3).
  exists (k (EPar e1'1 e2')), (k (EPar e1'1 e2'')), (k (EPar e1'2 e2'')).
  repeat split.
  - apply ctxs_steps; [done|].
    eapply steps_left; by [eapply steps_trace_none_heap_indifferent|].
  - apply ctxs_step; [done|].
    by apply par_r_step_trace_some.
  - apply ctxs_step; [done|].
    by apply par_l_step_trace_some.
  - eapply steps_trans'.
    + eapply ctxs_steps; [done|].
      by eapply steps_left.
    + eapply steps_trans'; [|done..].
      apply ctxs_steps; [done|].
      eapply steps_right; by [eapply steps_trace_none_heap_indifferent|].
    + done.
Qed.

Lemma steps_two_split_start_some {e1 h1 e2 h2 e3 h3 x y} :
  can_swap x y ->
  step_trace e1 h1 e2 h2 (Some x) ->
  steps_trace e2 h2 e3 h3 [y] ->
  exists e1' e2' e3',
    steps_trace e1 h1 e1' h1 [] /\
    step_trace e1' h1 e2' h2 (Some x) /\
    step_trace e2' h2 e3' h3 (Some y) /\
    steps_trace e3' h3 e3 h3 [].
Proof.
  intros Hswap. revert e1 h1 e2 h2 e3 h3.
  induction Hswap; intros e1 h1 e2 h2 e3 h3.
  - (* Base case: Left Right *) apply steps_two_split_left_right.
  - (* Base case: Right Left *) apply steps_two_split_right_left.
  - (* Inductive case: Left Left *)
    intros Hstep Hsteps.
    destruct (step_left_ctxs Hstep) as
      (k & e1' & e1'' & e2' & Hctx & -> & -> & Hstep').
    destruct (steps_left_in_context Hctx Hsteps) as
      (e3' & e2'' & Hctx3' & H2 & H3' & He3).
    specialize (IHHswap e1' h1 e1'' h2 e3' h3 Hstep' H3').
    destruct IHHswap as (ec1 & ec2 & ec3 & Hstep1 & Hstep2 & Hstep3 & Hstep4).
    exists (k (EPar ec1 e2'')), (k (EPar ec2 e2'')), (k (EPar ec3 e2'')).
    repeat split; eauto using ctxs_step, par_l_step_trace_some.
    + apply ctxs_steps; [done|].
      eapply steps_trans' with (t := []) (t' := []); [ | | done].
      * by eapply steps_left.
      * eapply steps_trace_none_heap_indifferent in H2.
        by eapply steps_right.
    + eapply steps_trans' with (t := []); [ | done | done].
      * eapply ctxs_steps; [done|].
        by eapply steps_left.
  - (* Inductive case: Right Right *)
    intros Hstep Hsteps.
    destruct (step_right_ctxs Hstep) as
      (k & e2' & e2'' & e1' & Hctx & -> & -> & Hstep').
    destruct (steps_right_in_context Hctx Hsteps) as
      (e3' & e1'' & Hctx3' & H1 & H3' & He3).
    specialize (IHHswap e2' h1 e2'' h2 e3' h3 Hstep' H3').
    destruct IHHswap as (ec1 & ec2 & ec3 & Hstep1 & Hstep2 & Hstep3 & Hstep4).
    exists (k (EPar e1'' ec1)), (k (EPar e1'' ec2)), (k (EPar e1'' ec3)).
    repeat split; eauto using ctxs_step, par_r_step_trace_some.
    + apply ctxs_steps; [done|].
      eapply steps_trans' with (t := []) (t' := []); [ | | done].
      * by eapply steps_right.
      * eapply steps_trace_none_heap_indifferent in H1.
        by eapply steps_left.
    + eapply steps_trans' with (t := []); [ | done | done].
      * eapply ctxs_steps; [done|].
        by eapply steps_right.
Qed.

Lemma steps_two_split {e h e' h' x y} :
  can_swap x y ->
  steps_trace e h e' h' [x; y] ->
  exists e1 e2 h2 e3,
    steps_trace e h e1 h [] /\
    step_trace e1 h e2 h2 (Some x) /\
    step_trace e2 h2 e3 h' (Some y) /\
    steps_trace e3 h' e' h' [].
Proof.
  intros Hswap Hsteps.
  remember [x;y] as xy. induction Hsteps; [done|..].
  - simplify_eq. specialize (IHHsteps eq_refl).
    destruct IHHsteps as (e3' & e4 & h4 & e5 & Hsteps2 & Hsteps3 & Hsteps4 & Hsteps5).
    exists e3', e4, h4, e5.
    assert (h1 = h2) by (by eapply step_trace_none_eq).
    simplify_eq. repeat split; [|done..].
    by eapply steps_step_none.
  - simplify_eq.
    destruct (steps_two_split_start_some Hswap H Hsteps)
      as (e1' & e2' & e3' & Hsteps' & Hxstep & Hystep & Hsteps'').
    by repeat eexists.
Qed.

(* Currently unused *)
Lemma ctx_trace_step_left e h e' h' t k :
  ctx_trace k ->
  ¬ is_val e ->
  step_trace (k e) h e' h' (Some (Left t)) ->
  exists e0, e' = k e0.
Proof.
  intros Hctx Hnval Hstep.
  inv Hstep; [by destruct b | .. | by destruct b].
  - apply ctx_trace_unique in H; try done.
    + destruct H; simplify_eq. by eexists.
    + by eapply step_trace_not_val.
  - inv Hctx.
Qed.

(* Currently unused *)
Lemma ctx_trace_step_right e h e' h' t k :
  ctx_trace k ->
  ¬ is_val e ->
  step_trace (k e) h e' h' (Some (Right t)) ->
  exists e0, e' = k e0.
Proof.
  intros Hctx Hnval Hstep.
  inv Hstep; try by destruct b.
  - apply ctx_trace_unique in H; try done.
    + destruct H; simplify_eq. by eexists.
    + by eapply step_trace_not_val.
  - inv Hctx.
Qed.

(* Currently unused *)
Lemma step_left_not_val e h e' h' t :
  step_trace e h e' h' (Some (Left t)) ->
  ¬ is_val e'.
Proof.
  intros Hstep.
  induction e'; try tauto.
  inv Hstep.
  - by destruct b.
  - by apply not_is_val_ctx1, ctx_trace_ctx1.
Qed.

(* Currently unused *)
Lemma step_right_not_val e h e' h' t :
  step_trace e h e' h' (Some (Right t)) ->
  ¬ is_val e'.
Proof.
  intros Hstep.
  induction e'; try tauto.
  inv Hstep.
  - by destruct b.
  - by apply not_is_val_ctx1, ctx_trace_ctx1.
Qed.

Lemma steps_left_map e h e' h' t t' {ek} :
  steps_trace e h e' h' t ->
  t' = map Left t ->
  steps_trace (EPar e ek) h (EPar e' ek) h' t'.
Proof.
  intros Hsteps ->. induction Hsteps; [constructor|..].
  - eapply steps_step_none; [|done].
    by apply par_l_step_trace_none.
  - eapply steps_step_some; [|done].
    by apply par_l_step_trace_some.
Qed.

Lemma steps_right_map e h e' h' t t' {ek}:
  steps_trace e h e' h' t ->
  t' = map Right t ->
  steps_trace (EPar ek e) h (EPar ek e') h' t'.
Proof.
  intros Hsteps ->. induction Hsteps; [constructor|..].
  - eapply steps_step_none; [|done].
    by apply par_r_step_trace_none.
  - eapply steps_step_some; [|done].
    by apply par_r_step_trace_some.
Qed.

Lemma step_trace_some_heap_indifferent h1' {e1 h1 e2 h2 b} :
  step_trace e1 h1 e2 h2 (Some b) ->
  exists h2', step_trace e1 h1' e2 h2' (Some b).
Proof.
  intros Hstep. dependent induction Hstep.
  - destruct b0; [|done]. simpl in x.  simplify_eq.
    inv H.
    + inv H0. exists h1'.
      apply head_step_trace_some. repeat constructor.
    + eexists. apply head_step_trace_some, Lock_head_step_trace.
    + eexists. apply head_step_trace_some, Unlock_head_step_trace.
  - destruct (IHHstep b eq_refl) as [h2' Hstep'].
    eexists. by constructor.
  - destruct b0; [|done]. simpl in x. simplify_eq.
    destruct (IHHstep e eq_refl) as [h2' Hstep'].
    eexists. by apply par_l_step_trace_some.
  - destruct b0; [|done]. simpl in x. simplify_eq.
    destruct (IHHstep e eq_refl) as [h2' Hstep'].
    eexists. by apply par_r_step_trace_some.
Qed.

Lemma step_swap {e1 h1 e2 h2 e3 h3 x y} :
  can_swap x y ->
  step_trace e1 h1 e2 h2 (Some x) ->
  step_trace e2 h2 e3 h3 (Some y) ->
  exists h', steps_trace e1 h1 e3 h' [y; x].
Proof.
  intros Hswap. revert e1 h1 e2 h2 e3 h3.
  induction Hswap; intros e1 h1 e2 h2 e3 h3 Hstepx Hstepy.
  - destruct (step_left_ctxs Hstepx) as
      (k & e1' & e1'' & e2' & Hctx & -> & -> & Hstep1).
    destruct (step_right_some_in_context Hctx Hstepy) as
      (e2'' & -> & Hstep2).
    destruct (step_trace_some_heap_indifferent h1 Hstep2) as (h2' & Hstep2').
    destruct (step_trace_some_heap_indifferent h2' Hstep1) as (h2'' & Hstep1').
    exists h2''. eapply steps_trans'; try apply step_once_some.
    + apply ctxs_step; [done|].
      by apply par_r_step_trace_some.
    + apply ctxs_step; [done|].
      by apply par_l_step_trace_some.
    + done.
  - destruct (step_right_ctxs Hstepx) as
      (k & e2' & e2'' & e1' & Hctx & -> & -> & Hstep1).
    destruct (step_left_some_in_context Hctx Hstepy) as
      (e1'' & -> & Hstep2).
    destruct (step_trace_some_heap_indifferent h1 Hstep2) as (h2' & Hstep2').
    destruct (step_trace_some_heap_indifferent h2' Hstep1) as (h2'' & Hstep1').
    exists h2''. eapply steps_trans'; try apply step_once_some.
    + apply ctxs_step; [done|].
      by apply par_l_step_trace_some.
    + apply ctxs_step; [done|].
      by apply par_r_step_trace_some.
    + done.
  - destruct (step_left_ctxs Hstepx) as
      (k & e1' & e1'' & e2' & Hctx & -> & -> & Hstep1).
    destruct (step_left_some_in_context Hctx Hstepy) as
      (e1''' & -> & Hstep2).
    destruct (IHHswap _ _ _ _ _ _ Hstep1 Hstep2) as [h' Hsteps].
    exists h'. apply ctxs_steps; [done|].
    by eapply steps_left_map.
  - destruct (step_right_ctxs Hstepx) as
      (k & e2' & e2'' & e1' & Hctx & -> & -> & Hstep1).
    destruct (step_right_some_in_context Hctx Hstepy) as
      (e2''' & -> & Hstep2).
    destruct (IHHswap _ _ _ _ _ _ Hstep1 Hstep2) as [h' Hsteps].
    exists h'. apply ctxs_steps; [done|].
    by eapply steps_right_map.
Qed.

Lemma steps_swap {e h e' h' x y} :
  can_swap x y ->
  steps_trace e h e' h' [y; x] ->
  exists h'', steps_trace e h e' h'' [x; y].
Proof.
  intros Hswap Hsteps.
  apply can_swap_symm in Hswap.
  destruct (steps_two_split Hswap Hsteps) as
    (e1 & e2 & h2 & e3 & Hsteps1 & Hstepy & Hstepx & Hsteps2).
  destruct (step_swap Hswap Hstepy Hstepx) as [hi Hstepsxy].
  eapply steps_trace_none_heap_indifferent in Hsteps2.
  exists hi. eauto using steps_trans'.
Qed.

Lemma steps_trace_heap_indifferent h1' {e1 h1 e2 h2 t} :
  steps_trace e1 h1 e2 h2 t ->
  exists h2', steps_trace e1 h1' e2 h2' t.
Proof.
  intros Hsteps. revert h1'.
  induction Hsteps; intros h1'.
  - exists h1'. constructor.
  - destruct (IHHsteps h1') as [h3' Hsteps'].
    exists h3'. eapply steps_step_none; [|done].
    by eapply step_trace_none_heap_indifferent.
  - apply (step_trace_some_heap_indifferent h1') in H.
    destruct H as [h2' Hstep2].
    destruct (IHHsteps h2') as [h3' Hsteps3].
    eexists. by eapply steps_step_some.
Qed.

Lemma step_base_ctxs {e1 h1 e2 h2 b} :
  step_trace e1 h1 e2 h2 (Some (Base b)) ->
  exists k e e', ctxs_trace k /\
    e1 = k e /\
    e2 = k e' /\ 
    head_step_trace e h1 e' h2 (Some b).
Proof.
  intros Hstep. remember (Some (Base b)) as bb.
  induction Hstep; [ | | by destruct b0..].
  - destruct b0; [|done]. simpl in Heqbb. simplify_eq.
    exists (λ x, x), e, e'.
    repeat split; auto with context.
  - destruct (IHHstep Heqbb) as (k0 & e0 & e0' & Hctx0 & -> & -> & Hhead).
    exists (λ x, k (k0 x)), e0, e0'.
    repeat split; auto with context.
Qed.

Lemma ctxs_step_not_val {e1 h1 e2 h2 b k} :
  ctxs_trace k ->
  ¬ is_val e1 ->
  step_trace (k e1) h1 e2 h2 b ->
  exists e2', e2 = k e2' /\
    step_trace e1 h1 e2' h2 b.
Proof.
  intros Hctx Hnval. revert e2.
  induction Hctx; intros e2 Hstep; [eauto|].
  apply (ctxs_not_val Hctx) in Hnval.
  destruct (ctx_step_not_val H Hnval Hstep) as (e2' & -> & H').
  destruct (IHHctx _ H') as (e3 & -> & H3).
  eauto.
Qed.

Lemma not_step_trace_val {v h1 e h2 t} :
  ¬ step_trace (EVal v) h1 e h2 t.
Proof.
  intros Hstep. inv Hstep.
  - inv H. inv H0.
  - inv H0.
Qed.

Ltac unique_tac := repeat
  match goal with
  | H : ctx_trace _ |- _ => inv H
  | H : step_trace (EVal _) _ _ _ _ |- _ => by apply not_step_trace_val in H
  | H : pure_step_trace _ _ _ |- _ => inv H
  | H : head_step_trace _ _ _ _ _ |- _ => inv H
  | H : step_trace _ _ _ _ _ |- _ => inv H
  | _ => intros || reflexivity
  end.

Lemma head_step_trace_unique {e1 h1 e2 h2 b} :
  head_step_trace e1 h1 e2 h2 b ->
  forall e' h' t, step_trace e1 h1 e' h' t -> t = option_map Base b.
Proof. unique_tac. Qed.

Lemma step_base_unique {e1 h1 e2 h2 b} :
  step_trace e1 h1 e2 h2 (Some (Base b)) ->
  forall e2' h2' t,
    step_trace e1 h1 e2' h2' t ->
    t = Some (Base b).
Proof.
  intros Hstep e2' h2' t Hstep'.
  destruct (step_base_ctxs Hstep) as
    (k & e & e' & Hctx & -> & -> & Hhead).
  assert (Hnval := step_trace_not_val _ _ _ _ _
    (do_head_step_trace _ _ _ _ _ Hhead)).
  destruct (ctxs_step_not_val Hctx Hnval Hstep') as
    (e2'' & -> & Hstep'').
  apply (head_step_trace_unique Hhead _ _ _ Hstep'').
Qed.

Lemma steps_perm e h e' h' (t t' : trace) :
  perm t t' ->
  steps_trace e h e' h' t ->
  exists h'', steps_trace e h e' h'' t'.
Proof.
  intros Hperm. revert t t' Hperm e h e' h'.
  refine (perm.perm_ind_bis _ _ _ _ _).
  - intros t e h e' h' Hsteps.
    by exists h'.
  - intros x t t' Hperm IH e h e' h' Hsteps.
    replace (x :: t) with ([x] ++ t) in Hsteps by reflexivity.
    replace (x :: t') with ([x] ++ t') by reflexivity.
    destruct (steps_split _ _ _ _ _ _ Hsteps) as (e1 & h1 & Hstep1 & Hstep2).
    destruct (IH _ _ _ _ Hstep2) as [h'' Hsteps''].
    exists h''. by eapply steps_trans.
  - intros x y t t' Hswap Hperm1 IH e h e' h' Hsteps.
    replace (y :: x :: t) with ([y; x] ++ t) in Hsteps by reflexivity.
    replace (x :: y :: t') with ([x; y] ++ t') by reflexivity.
    destruct (steps_split _ _ _ _ _ _ Hsteps) as (e1 & h1 & Hsteps1 & Hsteps2).
    destruct (steps_swap Hswap Hsteps1) as [h1' Hsteps1'].
    assert (Hperm : perm [y; x] [x; y]).
    { do 2 constructor. by apply can_swap_symm. }
    destruct (steps_trace_heap_indifferent h1' Hsteps2) as (h3 & Hsteps3).
    destruct (IH _ _ _ _ Hsteps3) as (h4 & Hsteps4).
    exists h4. by eapply steps_trans.
  - intros t t' t'' Hperm IH Hperm' IH' e h e' h' Hsteps.
    edestruct IH; [done|].
    edestruct IH'; [done|].
    by eexists.
Qed.

(* The proof of this theorem uses that gen_tree, from stdpp, is Countable *)
Global Instance val_countable : Countable val.
Proof.
  set (enc :=
    fix encv v :=
      match v with
      | VUnit => GenLeaf (inl (inl tt))
      | VBool b => GenLeaf (inl (inr (inl b)))
      | VNat n => GenLeaf (inr (inl n))
      | VRef n => GenLeaf (inr (inr n))
      | VPair v1 v2 => GenNode 0 [encv v1; encv v2]
      | VLock b => GenLeaf (inl (inr (inr b)))
      end).
  set (dec :=
    fix decv v :=
      match v with
      | GenLeaf (inl (inl tt)) => VUnit
      | GenLeaf (inl (inr (inl b))) => VBool b
      | GenLeaf (inl (inr (inr b))) => VLock b
      | GenLeaf (inr (inl n)) => VNat n
      | GenLeaf (inr (inr n)) => VRef n
      | GenNode _ [v1; v2] => VPair (decv v1) (decv v2)
      | GenNode _ _ => VUnit (* dummy *)
      end).
  refine (inj_countable' enc dec _). intros.
  induction x; eauto. simpl. by f_equal.
Qed.

Fixpoint to_base (e : event) : base_event :=
  match e with
  | Base b => b
  | Left b => to_base b
  | Right b => to_base b
  end.

Lemma left_to_base_eq (e : event) :
  to_base (Left e) = to_base e.
Proof. done. Qed.

Lemma right_to_base_eq (e : event) :
  to_base (Right e) = to_base e.
Proof. done. Qed.

(* alocks are the active locks, the locks that are currently locked *)
Fixpoint alocks_stateful (p : trace) (a : gset nat) : gset nat :=
  match p with
  | [] => a
  | e :: p' =>
      match to_base e with
      | Lock l => alocks_stateful p' ({[l]} ∪ a)
      | Unlock l => alocks_stateful p' (a ∖ {[l]})
      | Join => alocks_stateful p' a
      end
  end.

Definition alocks (p : trace) : gset nat := alocks_stateful p ∅.

Lemma alocks_empty :
  alocks [] = ∅.
Proof. done. Qed.

Lemma step_can_swap {e h e' h' e'' h'' a b} :
  step_trace e h e' h' (Some a) ->
  step_trace e h e'' h'' (Some b) ->
  a ≠ b ->
  can_swap a b.
Proof.
  revert e h e' h' a e'' h''.
  induction b; intros e h e' h' a e'' h'' Hstepa Hstepb Hne.
  - eapply step_base_unique in Hstepa; [|done]. simplify_eq.
  - destruct a.
    + eapply step_base_unique in Hstepb; [|done]. simplify_eq.
    + constructor.
      destruct (event_eq_dec a b); [simplify_eq|].
      apply step_left_ctxs in Hstepa.
      destruct Hstepa as (k & e1' & e2' & e0 & Hk & -> & -> & Hstepa).
      apply (step_left_some_in_context Hk) in Hstepb.
      destruct Hstepb as (e1'' & -> & Hstepb).
      eapply IHb; [apply Hstepa | apply Hstepb | apply n].
    + constructor.
  - destruct a.
    + eapply step_base_unique in Hstepb; [|done]. simplify_eq.
    + constructor.
    + constructor.
      destruct (event_eq_dec a b); [simplify_eq|].
      apply step_right_ctxs in Hstepa.
      destruct Hstepa as (k & e1' & e2' & e0 & Hk & -> & -> & Hstepa).
      apply (step_right_some_in_context Hk) in Hstepb.
      destruct Hstepb as (e1'' & -> & Hstepb).
      eapply IHb; [apply Hstepa | apply Hstepb | apply n].
Qed.

Global Instance base_event_countable : Countable base_event.
Proof.
  set (enc := λ e, match e with
    | Lock n => inl (inl n)
    | Unlock n => inl (inr n)
    | Join => inr tt
    end).
  set (dec := λ e, match e with
    | inl (inl n) => Lock n
    | inl (inr n) => Unlock n
    | inr tt => Join
    end).
  refine (inj_countable' enc dec _).
  intros x. by destruct x.
Qed.

Global Instance event_countable : Countable event.
Proof.
  set (enc :=
    fix encv e :=
      match e with
      | Base b => GenLeaf (b)
      | Left e' => GenNode 0 [encv e']
      | Right e' => GenNode 1 [encv e']
      end).
  set (dec :=
    fix decv v :=
      match v with
      | GenLeaf b => Base b
      | GenNode 0 [e] => Left (decv e)
      | GenNode 1 [e] => Right (decv e)
      | GenNode _ _ => Base Join (* dummy *)
      end).
  refine (inj_countable' enc dec _). intros.
  induction x; eauto; simpl; by f_equal.
Qed.

Global Instance forall_can_swap_dec (e : event) (u : gset event) :
  Decision (set_Forall (can_swap e) u).
Proof.
  apply set_Forall_dec.
  induction e; intros e'.
  - right. intros Hswap. inv Hswap.
  - destruct e'.
    + right. intros Hswap. inv Hswap.
    + destruct (IHe e').
      * left. by constructor.
      * right. intros Hswap. by inv Hswap.
    + left. constructor.
  - destruct e'.
    + right. intros Hswap. inv Hswap.
    + left. constructor.
    + destruct (IHe e').
      * left. by constructor.
      * right. intros Hswap. by inv Hswap.
Qed.

(* next events are events that could be scheduled next *)
(* they are the first instruction of a thread that is running concurrently *)
Fixpoint next_events_stateful
  (p : trace) (u : gset event) : gset event :=
  match p with
  | [] => ∅
  | e :: p' =>
      if decide (set_Forall (can_swap e) u)
        then {[e]} ∪ (next_events_stateful p' ({[e]} ∪ u))
        else (next_events_stateful p' ({[e]} ∪ u))
  end.

Definition next_events (p : trace) : gset event :=
  next_events_stateful p ∅.

Lemma next_events_head b t :
  b ∈ next_events (b :: t).
Proof.
  unfold next_events. simpl.
  destruct (decide (set_Forall (can_swap b) ∅)); [set_solver|].
  exfalso. apply n, set_Forall_empty.
Qed.

(* Checks wether, given a list of active locks, a base event is locking,
   meaning that a Lock instruction is trying to get a lock that is locked,
   or that an Unlock instruction is trying to release a lock that is unlocked *)
Definition is_locking (al : gset nat) (b : event) : Prop :=
  match to_base b with
  | Lock l => l ∈ al
  | Unlock l => l ∉ al
  | Join => False
  end.

Fixpoint valid_stateful (t : trace) (a : gset nat) : Prop :=
  match t with
  | [] => True
  | e :: p' =>
      match to_base e with
      | Lock l => l ∉ a /\ valid_stateful p' ({[l]} ∪ a)
      | Unlock l => l ∈ a /\ valid_stateful p' (a ∖ {[l]})
      | Join => valid_stateful p' a
      end
  end.

Definition valid (t : trace) : Prop :=
  valid_stateful t ∅.

Lemma valid_empty :
  valid [].
Proof. done. Qed.

Lemma valid_cons_inv t b a :
  valid_stateful (b :: t) a ->
  valid_stateful [b] a.
Proof.
  simpl. intros Hvalid.
  induction b; [|tauto..].
  destruct b; simpl in *; tauto.
Qed.

Lemma valid_left_inv t a :
  valid_stateful (map Left t) a ->
  valid_stateful t a.
Proof.
  revert a. induction t as [|e t]; [done|]. simpl.
  intros a Hvalid. destruct (to_base e); [..|eauto];
  split; try apply IHt; tauto.
Qed.

Lemma valid_right_inv t a :
  valid_stateful (map Right t) a ->
  valid_stateful t a.
Proof.
  revert a. induction t as [|e t]; [done|]. simpl.
  intros a Hvalid. destruct (to_base e); [..|eauto];
  split; try apply IHt; tauto.
Qed.

Lemma valid_to_base_iff b a :
  valid_stateful [b] a <-> valid_stateful [Base (to_base b)] a.
Proof. split; intros; done. Qed.

Lemma valid_to_base_cons_iff b t a :
  valid_stateful (b :: t) a <-> valid_stateful (Base (to_base b) :: t) a.
Proof. split; intros; done. Qed.

(* Currently only used in unused lemmas *)
Lemma valid_stateful_is_locking t b a :
  valid_stateful t a ->
  valid_stateful (t ++ [b]) a \/ is_locking (alocks_stateful t a) b.
Proof.
  revert a. induction t as [|e t]; intros a Ht.
  - simpl. induction b; [|done..].
    destruct b as [v|v|];
    [destruct (decide (v ∈ a))..|]; simpl; tauto.
  - simpl in Ht. induction e; [|tauto..].
    destruct b0; simpl in Ht;
    [destruct (IHt _ (proj2 Ht)).. | destruct (IHt _ Ht)];
    simpl; tauto.
Qed.

(* Currently unused *)
Lemma valid_is_locking t b :
  valid t ->
  valid (t ++ [b]) \/ is_locking (alocks t) b.
Proof. apply valid_stateful_is_locking. Qed.

Global Instance cell_eq_dec : EqDecision cell.
Proof. solve_decision. Defined.

Definition heap_locks (h : lock_heap) : gset nat :=
  dom _ (filter (λ lc, lc.2 = true) h).

Lemma heap_locks_empty :
  heap_locks ∅ = ∅.
Proof. set_solver. Qed.

Definition deadlock (t : trace) : Prop :=
  ∃ (ph pt : trace),
      perm t (ph ++ pt) ∧
      valid ph ∧
      pt ≠ [] ∧
      set_Forall (is_locking (alocks ph)) (next_events pt).

Lemma empty_not_deadlock :
  ¬ deadlock [].
Proof.
  intros (ph & pt & Hperm & Hpt & Hvalid & Hlock).
  apply perm_nil_is_nil, app_eq_nil in Hperm.
  tauto.
Qed.

Lemma step_trace_none_step (e e' : expr) h h' :
  step_trace e h e' h' None ->
  step e h e' h'.
Proof.
  intros Hstep. remember None as n.
  induction Hstep; destruct b; try done.
  - apply head_step_step. inv H.
    apply do_pure_step.
    inv H0; by constructor.
  - apply step_context_step;
    eauto with context.
  - apply step_context_step with (k := fun x => EPar x _);
    eauto with context.
  - apply step_context_step; eauto with context.
Qed.

(* 
  We define a helper-operational semantics which only records base events
  We can use this operational semantics to prove theorems about valid_stateful,
  which doesn't care about the tree-like structure of events
  We use this specifically for the lemmas:
  step_trace_some_step & step_trace_heap_locks_some
*)
Inductive step_trace_base :
  expr -> lock_heap ->
  expr -> lock_heap ->
  option base_event -> Prop :=
  | do_head_step_trace_base e h e' h' (b : option base_event) :
      head_step_trace e h e' h' b ->
      step_trace_base e h e' h' b
  | ctx_step_trace_base k e h e' h' (b : option base_event) :
      ctx_trace k ->
      step_trace_base e h e' h' b ->
      step_trace_base (k e) h (k e') h' b
  | par_l_step_trace_base e1 e2 h e1' h' (b : option base_event) :
      step_trace_base e1 h e1' h' b ->
      step_trace_base (EPar e1 e2) h (EPar e1' e2) h' b
  | par_r_step_trace_base e1 e2 h e2' h' (b : option base_event) :
      step_trace_base e2 h e2' h' b ->
      step_trace_base (EPar e1 e2) h (EPar e1 e2') h' b.

Lemma to_base_Base_id (b : option base_event) :
  option_map to_base (option_map Base b) = b.
Proof. by destruct b. Qed.

Lemma to_base_Left_id (b : option event) :
  option_map to_base (option_map Left b) = option_map to_base b.
Proof. by destruct b. Qed.

Lemma to_base_Right_id (b : option event) :
  option_map to_base (option_map Right b) = option_map to_base b.
Proof. by destruct b. Qed.

Lemma step_trace_to_base e1 h1 e2 h2 (b : option event) :
  step_trace e1 h1 e2 h2 b ->
  step_trace_base e1 h1 e2 h2 (option_map to_base b).
Proof.
  intros Hstep.
  induction Hstep;
  [rewrite to_base_Base_id | | rewrite to_base_Left_id | rewrite to_base_Right_id];
  by constructor.
Qed.

Lemma step_trace_some_step (e e' : expr) h h' b :
  step_trace e h e' h' (Some b) ->
  valid_stateful [b] (heap_locks h) ->
  step e h e' h'.
Proof.
  intros Hstep Hvalid.
  apply step_trace_to_base in Hstep. simpl in Hstep.
  remember (Some (to_base b)) as b0. induction Hstep.
  - destruct b0; [|done]. simplify_eq. inv H.
    + inv H0. eauto with headstep.
    + apply do_step with (k := fun x => x); eauto with context.
      constructor. rewrite valid_to_base_iff in Hvalid.
      rewrite <- H5 in Hvalid. destruct Hvalid as [Hvalid _].
      rewrite not_elem_of_dom in Hvalid.
      rewrite map_filter_lookup_None in Hvalid.
      destruct Hvalid as [Hnone | Hfalse].
      * left. by rewrite not_elem_of_dom.
      * simpl in Hfalse. destruct (h !! l) eqn:H.
        -- right. destruct b0; [|done].
           by specialize (Hfalse true eq_refl).
        -- left. by rewrite not_elem_of_dom.
    + apply do_step with (k := fun x => x); eauto with context.
      constructor. rewrite valid_to_base_iff in Hvalid.
      rewrite <- H5 in Hvalid. destruct Hvalid as [Hvalid _].
      rewrite elem_of_dom in Hvalid.
      destruct Hvalid as [x Hvalid].
      apply map_filter_lookup_Some_1_2 in Hvalid as Hv.
      simpl in Hv. simplify_eq.
      by eapply map_filter_lookup_Some_1_1.
  - apply step_context_step; eauto with context.
  - apply step_context_step with (k := fun x => EPar x e2); eauto with context.
  - apply step_context_step; eauto with context.
Qed.

Lemma heap_locks_lock l h :
  heap_locks (<[l:=true]> h) = {[l]} ∪ heap_locks h.
Proof.
  unfold heap_locks.
  rewrite map_filter_insert_True; [|done].
  by rewrite dom_insert_L.
Qed.

Lemma heap_locks_unlock l h :
  heap_locks (<[l:=false]> h) = heap_locks h ∖ {[l]}.
Proof.
  unfold heap_locks.
  rewrite map_filter_insert_False; [|done].
  by rewrite map_filter_delete dom_delete_L.
Qed.

Lemma step_trace_heap_locks_some e1 h1 e2 h2 t b :
  step_trace e1 h1 e2 h2 (Some b) ->
  valid_stateful (b :: t) (heap_locks h1) ->
  valid_stateful t (heap_locks h2).
Proof.
  intros Hstep Hvalid.
  apply step_trace_to_base in Hstep. simpl in Hstep.
  remember (Some (to_base b)) as b0.
  induction Hstep; [|eauto..].
  simplify_eq. inv H; [|simpl in Hvalid..].
  - inv H0. rewrite valid_to_base_cons_iff in Hvalid.
    by rewrite <- H3 in Hvalid.
  - rewrite <- H5 in Hvalid. rewrite heap_locks_lock; tauto.
  - rewrite <- H5 in Hvalid. rewrite heap_locks_unlock; tauto.
Qed.

Lemma steps_trace_valid_steps (e e' : expr) h h' t :
  steps_trace e h e' h' t ->
  valid_stateful t (heap_locks h) ->
  steps e h e' h'.
Proof.
  intros Hsteps Hvalid.
  induction Hsteps; [constructor | |].
  - eapply steps_step.
    + by apply step_trace_none_step.
    + erewrite step_trace_none_eq in Hvalid; eauto.
  - eapply steps_step.
    + eapply step_trace_some_step; [done|].
      by eapply valid_cons_inv.
    + eauto using step_trace_heap_locks_some.
Qed.

Lemma steps_trace_stuck e h e' h' ph :
  steps_trace e h e' h' ph ->
  valid_stateful ph (heap_locks h) ->
  stuck e' h' ->
  stuck e h.
Proof.
  intros Hsteps Hvalid (e'' & h'' & Hsteps' & Hstuck).
  exists e'', h''. split; [|done].
  eapply perm.steps_trans; [|done].
  by eapply steps_trace_valid_steps.
Qed.

(* Helper lemmas for steps_trace_locks_stateful *)
Lemma step_trace_alocks e1 h1 e2 h2 b t :
  step_trace e1 h1 e2 h2 (Some b) ->
  alocks_stateful (b :: t) (heap_locks h1) = alocks_stateful t (heap_locks h2).
Proof.
  intros Hstep.
  apply step_trace_to_base in Hstep. simpl in Hstep.
  remember (Some (to_base b)) as b0.
  induction Hstep; [|tauto..].
  simplify_eq. inv H.
  - inv H0. simpl. by rewrite <- H3.
  - simpl. rewrite <- H5.
    by rewrite heap_locks_lock.
  - simpl. rewrite <- H5.
    by rewrite heap_locks_unlock.
Qed.

Lemma step_trace_valid_stateful e1 h1 e2 h2 b t :
  step_trace e1 h1 e2 h2 (Some b) ->
  valid_stateful (b :: t) (heap_locks h1) ->
  valid_stateful t (heap_locks h2).
Proof.
  intros Hstep Hvalid.
  apply step_trace_to_base in Hstep. simpl in Hstep.
  remember (Some (to_base b)) as b0.
  induction Hstep; [|tauto..].
  simplify_eq. inv H.
  - inv H0. simpl in Hvalid. by rewrite <- H3 in Hvalid.
  - simpl in Hvalid. rewrite <- H5 in Hvalid.
    rewrite heap_locks_lock. tauto.
  - simpl in Hvalid. rewrite <- H5 in Hvalid.
    rewrite heap_locks_unlock. tauto.
Qed.

Lemma steps_trace_locks_stateful e h e' h' ph :
  steps_trace e h e' h' ph ->
  valid_stateful ph (heap_locks h) ->
  alocks_stateful ph (heap_locks h) = heap_locks h'.
Proof.
  intros Hsteps Hvalid. induction Hsteps; [done|..].
  - erewrite (step_trace_none_eq H).
    erewrite step_trace_none_eq in Hvalid; eauto.
  - rewrite <- IHHsteps.
    + by eapply step_trace_alocks.
    + by eapply step_trace_valid_stateful.
Qed.



Lemma steps_trace_locks e e' h' ph :
  steps_trace e ∅ e' h' ph ->
  valid ph ->
  alocks ph = heap_locks h'.
Proof.
  intros. unfold alocks.
  rewrite <- heap_locks_empty.
  eapply steps_trace_locks_stateful; [done|].
  by rewrite heap_locks_empty.
Qed.

Lemma par_base_is_join {e1 e2 h1 e h2 b} :
  step_trace (EPar e1 e2) h1 e h2 (Some (Base b)) ->
  b = Join.
Proof.
  intros Hstep. inv Hstep.
  - destruct b0; [|done]. simpl in H. simplify_eq.
    inv H4. by inv H.
  - inv H0.
  - by destruct b0.
  - by destruct b0.
Qed.

Lemma join_in_trace_par {e1 e2 h1 v h2 t} :
  steps_trace (EPar e1 e2) h1 (EVal v) h2 t ->
  (Base Join) ∈ t.
Proof.
  intros Hsteps. remember (EVal v) as ev.
  remember (EPar e1 e2) as ep. revert e1 e2 Heqep.
  induction Hsteps; intros e1' e2' Heq; simplify_eq.
  - assert (Heq := step_trace_none_eq H). subst.
    destruct (step_none_without_context H) as
      [(? & -> & _) | (? & -> & _)]; eauto.
  - destruct b; [|apply elem_of_list_further..].
    + apply par_base_is_join in H. subst. apply elem_of_list_here.
    + destruct (step_left_some_without_context H) as (e & -> & _). eauto.
    + destruct (step_right_some_without_context H) as (e & -> & _). eauto.
Qed.

Lemma is_val_decision e : Decision (is_val e).
Proof. destruct e; (right; progress eauto) || by left. Qed.

Lemma steps_none_in_context {e h v k} :
  ctx_trace k ->
  steps_trace (k e) h (EVal v) h [] ->
  exists v', steps_trace e h (EVal v') h [].
Proof.
  intros Hctx Hsteps.
  remember (k e) as ke. revert e Heqke.
  remember (EVal v) as ev. remember [] as t.
  induction Hsteps; intros e' Heqke; [inv Hctx | subst | done].
  destruct (is_val_decision e') as [Hval | Hnval].
  - destruct e'; simpl in Hval; [|done..].
    eauto using steps_trace.
  - destruct (ctx_step_not_val Hctx Hnval H) as (e'' & -> & He'').
    destruct (IHHsteps eq_refl eq_refl e'' eq_refl) as [v' Hv'].
    assert (Heq := steps_trace_none_eq Hsteps). subst.
    assert (Heq := step_trace_none_eq He''). subst.
    eauto using steps_trace.
Qed.

Lemma steps_trace_singleton_unique {e1 h1 e2 h2 b v h3} :
  step_trace e1 h1 e2 h2 (Some b) ->
  steps_trace e2 h2 (EVal v) h3 [] ->
  forall e' h' t, step_trace e1 h1 e' h' t -> t = Some b.
Proof.
  intros Hstep. revert v.
  remember (Some b) as t.
  induction Hstep; intros v Hsteps.
  - by eapply head_step_trace_unique.
  - assert (Heq := steps_trace_none_eq Hsteps). subst.
    destruct (steps_none_in_context H Hsteps) as [v' Hv'].
    intros e1 h1 b1 H1. apply step_trace_not_val in Hstep.
    destruct (ctx_step_not_val H Hstep H1) as (e1' & -> & He1').
    eauto.
  - by apply join_in_trace_par, not_elem_of_nil in Hsteps.
  - by apply join_in_trace_par, not_elem_of_nil in Hsteps.
Qed.

Lemma step_trace_heap_indifferent {e1 h1 e2 h2 b h1'} :
  step_trace e1 h1 e2 h2 b ->
  exists h2', step_trace e1 h1' e2 h2' b.
Proof.
  intros Hstep. destruct b.
  - by eapply step_trace_some_heap_indifferent.
  - eapply step_trace_none_heap_indifferent in Hstep.
    eauto.
Qed.

Lemma step_trace_event_postponed {e1 h1 e2 h2 b e2' h2' b'} :
  step_trace e1 h1 e2 h2 b ->
  step_trace e1 h1 e2' h2' b' -> 
  b ≠ b' ->
  exists e3 h3, step_trace e2' h2' e3 h3 b.
Proof.
  intros Hstep Hstep'. revert e2 h2 b Hstep.
  induction Hstep'; intros e'' h'' b' Hstep Hne.
  - by eapply head_step_trace_unique in H.
  - apply step_trace_not_val in Hstep'.
    destruct (ctx_step_not_val H Hstep' Hstep) as (e2 & -> & H2).
    destruct (IHHstep' _ _ _ H2 Hne) as (e3 & h3 & H3).
    eauto using step_trace.
  - inv Hstep.
    + inv H. inv H0. by apply step_trace_not_val in Hstep'.
    + inv H0.
    + destruct b0; destruct b; simpl in Hne; [..|done];
      destruct (IHHstep' _ _ _ H5) as (? & ? & ?);
      eauto using step_trace. intros Heq. simplify_eq.
    + eapply step_trace_heap_indifferent in H5.
      destruct H5 as [h2' H5]. eauto using step_trace.
  - inv Hstep.
    + inv H. inv H0. by apply step_trace_not_val in Hstep'.
    + inv H0.
    + eapply step_trace_heap_indifferent in H5.
      destruct H5 as [h2' H5]. eauto using step_trace.
    + destruct b0; destruct b; simpl in Hne; [..|done];
      destruct (IHHstep' _ _ _ H5) as (? & ? & ?);
      eauto using step_trace. intros Heq. simplify_eq.
Qed.

Lemma steps_trace_event_postponed {e1 h1 e2 h2 b e2' h2' t} :
  step_trace e1 h1 e2 h2 (Some b) ->
  steps_trace e1 h1 e2' h2' t ->
  ¬ In b t ->
  exists e3 h3, step_trace e2' h2' e3 h3 (Some b).
Proof.
  intros Hstep Hsteps. revert e2 h2 Hstep.
  induction Hsteps; intros e2' h2' Hstep Hnin; [eauto|..].
  - destruct (step_trace_event_postponed Hstep H) as (e3' & h3' & H3); eauto.
  - rewrite not_in_cons in Hnin. destruct Hnin as [Hneq Hnin].
    destruct (step_trace_event_postponed Hstep H) as (e3' & h3' & H3); [|eauto].
    intros Heq. simplify_eq.
Qed.

(* Practise for step_trace_in_next_events with an easier conclusion *)
Lemma steps_trace_in_trace {e1 h1 v h2 t} :
  steps_trace e1 h1 (EVal v) h2 t ->
  forall e' h' b, step_trace e1 h1 e' h' (Some b) ->
  In b t.
Proof.
  revert e1 h1 v h2. induction t; intros e1 h1 v h2 Hsteps e' h' b Hstep.
  - exfalso. revert e' h' b Hstep. remember (EVal v) as ev. remember [] as t.
    induction Hsteps; simplify_eq; intros e' h' b Hstep.
    + by eapply not_step_trace_val.
    + destruct (step_trace_event_postponed Hstep H) as (e'' & h'' & H''); eauto.
  - destruct b.
    + destruct (step_base_ctxs Hstep) as (k & eb & eb' & Hctx & -> & -> & Hhead).
      assert (Heq: Base b = a); [clear IHt | subst; apply in_eq].
      inv Hsteps.
      * assert (Hnval := step_trace_not_val _ _ _ _ _
                (head_step_trace_some _ _ _ _ _ Hhead)).
        destruct (ctxs_step_not_val Hctx Hnval H) as (e2' & -> & H').
        by apply (head_step_trace_unique Hhead) in H'.
      * assert (Hnval := step_trace_not_val _ _ _ _ _
                (head_step_trace_some _ _ _ _ _ Hhead)).
        destruct (ctxs_step_not_val Hctx Hnval H5) as (e2' & -> & H').
        apply (head_step_trace_unique Hhead) in H'. simpl in H'. by simplify_eq.
    + destruct (event_eq_dec (Left b) a); [subst; apply in_eq|].
      replace (a :: t) with ([a] ++ t) in Hsteps; [|done].
      destruct (steps_split _ _ _ _ _ _ Hsteps) as (e1' & h1' & Ha & Ht).
      destruct (steps_trace_event_postponed Hstep Ha) as (e0' & h0' & H0').
      * intros Hin. destruct Hin; simplify_eq.
      * by eapply in_cons, IHt.
    + destruct (event_eq_dec (Right b) a); [subst; apply in_eq|].
      replace (a :: t) with ([a] ++ t) in Hsteps; [|done].
      destruct (steps_split _ _ _ _ _ _ Hsteps) as (e1' & h1' & Ha & Ht).
      destruct (steps_trace_event_postponed Hstep Ha) as (e0' & h0' & H0').
      * intros Hin. destruct Hin; simplify_eq.
      * by eapply in_cons, IHt.
Qed.

Lemma next_events_cons {a b u t} :
  can_swap b a ->
  b ∈ next_events_stateful t u ->
  b ∈ next_events_stateful t ({[a]} ∪ u).
Proof.
  revert a b u. induction t; intros b c u Hswap Hin; [set_solver|].
  simpl in *. destruct (decide (set_Forall (can_swap a) u)).
  - rewrite elem_of_union in Hin. destruct Hin as [Hin | Hin].
    + apply elem_of_singleton in Hin. simplify_eq.
      destruct (decide (set_Forall (can_swap a) ({[b]} ∪ u))); [set_solver|].
      exfalso. apply n. apply set_Forall_union; [|done].
      by rewrite set_Forall_singleton.
    + specialize (IHt _ _ _ Hswap Hin).
      replace ({[b]} ∪ ({[a]} ∪ u)) with ({[a]} ∪ ({[b]} ∪ u)) in IHt;
      [destruct (decide (set_Forall (can_swap a) ({[b]} ∪ u)))|];
      set_solver.
  - specialize (IHt _ _ _ Hswap Hin).
    replace ({[b]} ∪ ({[a]} ∪ u)) with ({[a]} ∪ ({[b]} ∪ u)) in IHt;
    [destruct (decide (set_Forall (can_swap a) ({[b]} ∪ u)))|];
    set_solver.
Qed.

(* Lemma used directly in steps_trace_heap_locks_stuck *)
Lemma step_trace_in_next_events {e h1 v h2 t} :
  steps_trace e h1 (EVal v) h2 t ->
  forall e' h' b, step_trace e h1 e' h' (Some b) ->
  b ∈ next_events t.
Proof.
  revert e h1 v h2. induction t; intros e h1 v h2 Hsteps e' h' b Hstep.
  - exfalso. revert e' h' b Hstep. remember (EVal v) as ev. remember [] as t.
    induction Hsteps; simplify_eq; intros e' h' b Hstep.
    + by eapply not_step_trace_val.
    + destruct (step_trace_event_postponed Hstep H) as (e'' & h'' & H''); eauto.
  - destruct (event_eq_dec b a) as [-> | Hne]; [apply next_events_head|].
    unfold next_events. simpl.
    destruct (decide (set_Forall (can_swap a) ∅)).
    2:{ exfalso. apply n, set_Forall_empty. }
    replace (a :: t) with ([a] ++ t) in Hsteps; [|done].
    apply steps_split in Hsteps. destruct Hsteps as (ea & ha & Ha & Hsteps).
    destruct (steps_trace_event_postponed Hstep Ha) as (e3 & h3 & H3);
    [set_solver|]. remember [a] as la. revert e' h' Hstep;
    induction Ha; intros e' h' Hstep; simplify_eq.
    { destruct (step_trace_event_postponed Hstep H) as
      (ef & hf & Hf); by [|eapply IHHa]. }
    eapply elem_of_union_r, next_events_cons.
    + by eapply step_can_swap.
    + by eapply IHt.
Qed.

(* TODO: Move everything about NoneEvent and none_steps_trace to different file *)

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

Lemma strong_induction (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
  forall n, P n.
Proof.
  intros IH n; enough (H: forall m, m <= n -> P m).
  - apply H, le_n.
  - induction n.
    + intros m Hm. apply le_n_0_eq in Hm. subst.
      apply IH. lia.
    + intros m Hm. apply Nat.le_succ_r in Hm. destruct Hm as [Hm | ->].
      * by apply IHn.
      * apply IH. intros k HK. apply IHn. lia.
Qed.

Lemma none_perm_length t t' :
  none_perm t t' ->
  length t = length t'.
Proof.
  intros Hperm. induction Hperm.
  - done.
  - rewrite !cons_length. by f_equal.
  - by rewrite !cons_length.
  - by rewrite IHHperm1.
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

Definition step_no_event : relation (expr * lock_heap) := λ H H',
  let (e, h) := H in
  let (e', h') := H' in
  step_trace e h e' h' None.

Lemma step_sn e h v h' t :
  steps_trace e h (EVal v) h' t ->
  sn (step_no_event) (e, h).
Proof.
  intros Hsteps.
  Check @sn_wn. Print red. Print sn. Print Acc. Print flip.
  Print wn. Print nf. Print relation.
  About rtc_nsteps. About lt_wf. Print diamond.
  (* TODO: steps_trace e h (EVal v) h' t ->
           exists n, e steps to v in n steps *)
Admitted.

Lemma steps_trace_none_first {e h v h' pt} :
  steps_trace e h (EVal v) h' pt ->
  pt ≠ [] ->
  exists e',
    steps_trace e h e' h [] /\
    steps_trace e' h (EVal v) h' pt /\
    (forall e'' h'' t,
      step_trace e' h e'' h'' t -> exists b, t = Some b).
Proof.
  (* TODO *)
Admitted.

Lemma steps_trace_not_val {e h e' h' t} :
  steps_trace e h e' h' t ->
  t ≠ [] ->
  ¬ is_val e.
Proof.
  intros Hsteps Ht.
  inv Hsteps; by eapply step_trace_not_val.
Qed.

Lemma head_step_to_step_trace {e h e' h'} :
  head_step e h e' h' ->
  exists t,
    step_trace e h e' h' t /\
    forall b, t = Some b -> ¬ is_locking (heap_locks h) b.
Proof.
  intros Hstep. inv Hstep.
  - inv H; [exists (option_map Base None); split;
      try done; eauto with headstep..|].
    exists (option_map Base (Some Join)). split; [eauto with headstep|].
    simpl. intros b Heq Hlock. by simplify_eq.
  - eexists. split; [eauto with headstep|].
    simpl. intros b Heq Hlock. simplify_eq.
    unfold is_locking in Hlock. simpl in Hlock.
    destruct H as [Hnelem | Hfalse].
    + eapply Hnelem, elem_of_weaken; [done|].
      apply dom_filter_subseteq.
    + rewrite elem_of_dom in Hlock.
      destruct Hlock as [x Hlock].
      apply map_filter_lookup_Some_1_2 in Hlock as Hl. simpl in Hl.
      apply map_filter_lookup_Some_1_1 in Hlock. simplify_eq.
  - eexists. split; [eauto with headstep|].
    simpl. intros b Heq Hlock. simplify_eq.
    unfold is_locking in Hlock. simpl in Hlock.
    rewrite not_elem_of_dom map_filter_lookup_None in Hlock.
    destruct Hlock as [? | Hlock]; [simplify_eq | by eapply Hlock].
Qed.

Lemma step_to_step_trace {e h e' h'} :
  step e h e' h' ->
  exists t,
    step_trace e h e' h' t /\
    forall b, t = Some b ->
      ¬ is_locking (heap_locks h) b.
Proof.
  intros Hstep. inv Hstep.
  induction H; [by apply head_step_to_step_trace|].
  destruct IHctx as (t & Hstep & Hlock).
  inv H; try by (exists t; split; try apply Hlock;
    apply ctx_step_trace; eauto with context).
  - exists t. split; [|apply Hlock].
    apply ctx_step_trace with (k := fun x => EPair x e); eauto with context.
  - exists t. split; [|apply Hlock].
    apply ctx_step_trace with (k := fun x => ELet y x e); eauto with context.
  - exists t. split; [|apply Hlock].
    apply ctx_step_trace with (k := fun x => EOp op x e); eauto with context.
  - exists t. split; [|apply Hlock].
    apply ctx_step_trace with (k := fun x => EIf x e1 e2); eauto with context.
  - exists t. split; [|apply Hlock].
    apply ctx_step_trace with (k := fun x => ESeq x e); eauto with context.
  - exists (option_map Left t). split; [by constructor|].
    intros b Heq Hb. destruct t; [|done]. simpl in Heq.
    simplify_eq. by eapply Hlock.
  - exists (option_map Right t). split; [by constructor|].
    intros b Heq Hb. destruct t; [|done]. simpl in Heq.
    simplify_eq. by eapply Hlock.
Qed.

Lemma steps_trace_heap_locks_stuck e h v h' pt :
  steps_trace e h (EVal v) h' pt ->
  pt ≠ [] ->
  set_Forall (is_locking (heap_locks h)) (next_events pt) ->
  stuck e h.
Proof.
  intros Hsteps Hpt Hlock.
  destruct (steps_trace_none_first Hsteps Hpt) as
    (e' & Hnone & Hrest & Hin).
  exists e', h. repeat split.
  - by eapply steps_trace_valid_steps.
  - by eapply steps_trace_not_val.
  - intros e'' h'' Hstep.
    destruct (step_to_step_trace Hstep) as (t & Hstept & Ht).
    destruct (Hin _ _ _ Hstept) as [b ->].
    apply (step_trace_in_next_events Hrest) in Hstept.
    by apply (Ht b eq_refl), Hlock.
Qed.

Theorem trace_soundness (e : expr) (v : val) h' (t : trace) :
  steps_trace e ∅ (EVal v) h' t ->
  deadlock t ->
  stuck e ∅.
Proof.
  intros Hsteps (ph & pt & Hperm & Hvalid & Hpt & Hdeadlock).
  apply (steps_perm _ _ _ _ _ _ Hperm) in Hsteps.
  destruct Hsteps as [h1 Hsteps].
  apply (steps_split _ _ _ _ _ _) in Hsteps as (e' & h'' & Hsteps & Hsteps').
  eapply steps_trace_stuck; [|rewrite heap_locks_empty|]; [done..|].
  erewrite steps_trace_locks in Hdeadlock; [|done..].
  by eapply steps_trace_heap_locks_stuck.
Qed.

(*
  1) Verslag
    1a) Introduction
        -- Contributions incl Differences with CISL paper (globally)
    1b) Preliminaries (no Coq)
        -- Separation logic
        -- ISL
        -- CISL (High-level overview)
    1c) CISL_DC (no Coq)
    1d) CISL_DD (no Coq)
        -- Trace based notion of deadlock
    1e) Coq
        -- CISL_DC
        -- CISL_DD
    1f) Related Work
        -- CISL paper incl differences (detailed)
        -- Other formal definition of deadlock
    1g) Conclusion & Future work
        -- Locks + state using Iris locks specs
        -- Deadlock definition without permutations
  2) Prove lemmas
*)

(* let l = alloc(lock(false)) in
    acquire l; || //while(true);
    acquire l; || release l;
    true + 0   ||

  What does CISL say about the above program (with/without while(true))?

Possible acquire states:
 1) acquire v, where v does not point to a lock
 2) acquire v, deadlock in thread, no other threads
 3) acquire v, other threads exist
 4) acquire v, all threads are doing an acquire on a locked lock
*)

(*
Possible definitions of deadlock:
  For all possible steps, a lock remains locked
    - Starvation (Not necessarily deadlock if infinite loops)
  Cannot step, but not is_error
    - Not is_error is difficult to prove
    - Use correctness logic to prove typed -> correct,
      then typed /\ not step -> deadlock
  Histories
    - Locks don't lock, but add event to history
    - CISL paper only uses non-deterministic choice and loops
    - Generalizing to deterministic may introduce bugs
*)
