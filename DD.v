From Coq Require Export Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Program.Equality.
From Coq Require Import Bool.DecBool.
Require Import perm.
From iris.proofmode Require Import tactics.
From stdpp Require Import countable.

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
  | Newlock_head_step_trace h l :
      l ∉ dom (gset nat) h →
      head_step_trace
        ENewlock h
        (EVal (VRef l)) (<[ l := false ]> h)
        None
  | Lock_head_step_trace h l :
      l ∈ dom (gset nat) h ->
      head_step_trace
        (ELock (EVal (VRef l))) h
        (EVal VUnit) (<[ l := true ]> h)
        (Some (Lock l))
  | Unlock_head_step_trace h l :
      l ∈ dom (gset nat) h ->
      head_step_trace
        (EUnlock (EVal (VRef l))) h
        (EVal VUnit) (<[ l := false ]> h)
        (Some (Unlock l)).

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
  intros H. induction e2; try done.
  simplify_eq.
Qed.

Lemma step_trace_not_eq' e1 h1 e2 h2 t :
  e1 = e2 ->
  ¬ step_trace e1 h1 e2 h2 t.
Proof.
  intros Heq Hstep.
  induction Hstep; simplify_eq.
  - inv H. inv H0.
    + induction e; try done; simpl in H2.
      * by destruct (string_dec s y).
      * destruct (string_dec y s); simplify_eq.
        by eapply let_not_recursive.
    + induction e1; try done; simplify_eq.
    + induction e2; try done; simplify_eq.
    + induction e; try done; simplify_eq.
  - eauto using ctx_trace_injective.
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

Lemma steps_swap {e h e' h' x y} :
  can_swap x y ->
  steps_trace e h e' h' [y; x] ->
  exists h'', steps_trace e h e' h'' [x; y].
Proof. Admitted.
(* steps_swap is false, since the following program doesn't allow swaps *)

Definition steps_swap_false l l' :=
  (EPar (ELock (EVal (VRef l'))) (ESeq (ELock (EVal (VRef l))) (ENewlock))).

Check ({[ 0 := false; 1 := false]}) : lock_heap.

Lemma contradiction : False.
Proof.
  assert (
    steps_trace
      (steps_swap_false 0 1) {[0 := false]}
      (EPar (EVal VUnit) (EVal (VRef 1))) {[1 := true; 0 := true]}
      [Right (Base (Lock 0)); Left (Base (Lock 1))]).
  { unfold steps_swap_false. eapply steps_step_some. {
    apply par_r_step_trace_some.
    apply ctx_step_trace with (k := fun x => ESeq x _); eauto with context.
    apply head_step_trace_some.
    by constructor. } rewrite insert_singleton.
    eapply steps_step_none. {
    apply par_r_step_trace_none, head_step_trace_none. repeat constructor. }
    eapply steps_step_none. {
    apply par_r_step_trace_none, head_step_trace_none.
    by apply Newlock_head_step_trace with (l := 1). }
    eapply steps_step_some. {
    apply par_l_step_trace_some, head_step_trace_some.
    by constructor. } rewrite insert_insert. apply steps_refl_trace.
  } unfold steps_swap_false in H.
  apply steps_swap in H; [|constructor].
  destruct H as [h'' H]. inv H.
  - inv H0.
    + inv H6. inv H0.
    + inv H2.
    + inv H6.
      * inv H. inv H0.
      * inv H0. inv H2.
        -- inv H. inv H0.
        -- inv H0.
    + inv H6.
      * inv H. inv H0.
      * inv H0. inv H2.
        -- inv H. inv H0.
        -- inv H0. inv H3.
           ++ inv H. inv H0.
           ++ inv H0.
  - inv H6.
    + inv H4. inv H0.
    + inv H0.
    + inv H4.
      * inv H.
        -- inv H0.
        -- discriminate. (* The crucial step *)
      * inv H0. inv H1.
        -- inv H. inv H0.
        -- inv H0.
    + destruct b; done.
Qed.

Lemma step_trace_heap_indifferent {e1 h1 h1' e2 h2 t} :
  dom (gset nat) h1 = dom (gset nat) h1' ->
  step_trace e1 h1 e2 h2 t ->
  exists h2', step_trace e1 h1' e2 h2' t.
Proof.
  intros Hdom Hstep.
  induction Hstep.
  - inversion H; [|rewrite Hdom in H0..]; simplify_eq.
    + exists h1'. by do 2 constructor.
    + eexists. constructor. by apply Newlock_head_step_trace.
    + eexists. constructor. by apply Lock_head_step_trace.
    + eexists. constructor. by apply Unlock_head_step_trace.
  - destruct (IHHstep Hdom) as [h2' IH].
    eexists; by constructor.
  - destruct (IHHstep Hdom) as [h2' IH].
    eexists; by constructor.
  - destruct (IHHstep Hdom) as [h2' IH].
    eexists; by constructor.
Qed.

Lemma step_trace_dom_eq {e0 h0 e1 h1 h1' t t'} :
  steps_trace e0 h0 e1 h1 t ->
  steps_trace e0 h0 e1 h1' t' ->
  dom (gset nat) h1 = dom (gset nat) h1'.
Proof. Admitted.

Lemma steps_trace_heap_indifferent {e0 h0 e1 h1 h1' e2 h2 t0 t0' t1} :
  steps_trace e0 h0 e1 h1 t0 ->
  steps_trace e0 h0 e1 h1' t0' ->
  steps_trace e1 h1 e2 h2 t1 ->
  exists h2', steps_trace e1 h1' e2 h2' t1.
Proof.
  intros Hsteps1 Hsteps1' Hsteps2.
  revert e0 h0 h1' t0 t0' Hsteps1 Hsteps1'.
  induction Hsteps2;
  intros e0 h0 h1' t0 t0' Hsteps1 Hsteps1'.
  - exists h1'. constructor.
  - assert (dom (gset nat) h1 = dom (gset nat) h1');
    [by eapply step_trace_dom_eq|].
    destruct (step_trace_heap_indifferent H0 H) as [h2' H'].
    destruct (IHHsteps2 e0 h0 h2' (t0 ++ []) (t0' ++ [])) as [h3' Hsteps3].
    + eapply steps_trans; [done|]. by apply step_once_none.
    + eapply steps_trans; [done|]. by apply step_once_none.
    + exists h3'. replace t with ([] ++ t) by reflexivity.
      eapply steps_trans; [|done]. by apply step_once_none.
  - assert (dom (gset nat) h1 = dom (gset nat) h1');
    [by eapply step_trace_dom_eq|].
    destruct (step_trace_heap_indifferent H0 H) as [h2' H'].
    edestruct (IHHsteps2 e0 h0 h2') as [h3' Hsteps3].
    + eapply steps_trans; [apply Hsteps1|]. by apply step_once_some.
    + eapply steps_trans; [done|]. by apply step_once_some.
    + exists h3'. replace (b :: t) with ([b] ++ t) by reflexivity.
      eapply steps_trans; [|done]. by apply step_once_some.
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
    destruct (steps_trace_heap_indifferent Hsteps1 Hsteps1' Hsteps2) as (h3 & Hsteps3).
    destruct (IH _ _ _ _ Hsteps3) as (h4 & Hsteps4).
    exists h4. by eapply steps_trans.
  - intros t t' t'' Hperm IH Hperm' IH' e h e' h' Hsteps.
    edestruct IH; [done|].
    edestruct IH'; [done|].
    by eexists.
Qed.

Check perm_ind_bis.

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

(* the thread is the combination of left/right of an event,
   represented as a list of bools *)
Fixpoint thread_stateful (e : event) (a : list bool) : list bool :=
  match e with
  | Base _ => a
  | Left b => thread_stateful b (a ++ [false])
  | Right b => thread_stateful b (a ++ [true])
  end.

Definition thread (e : event) : list bool := thread_stateful e [].

Definition is_parent_or_child (tid tid' : list bool) : Prop :=
  (tid `prefix_of` tid') \/ (tid' `prefix_of` tid).

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

(* next events are events that could be scheduled next *)
(* they are the first instruction of a thread that is running concurrently *)
Fixpoint next_events_stateful
  (p : trace) (n : gset base_event) (u : gset (list bool)) : gset base_event :=
  match p with
  | [] => n
  | e :: p' =>
      if decide (set_Exists (is_parent_or_child (thread e)) u)
        then (next_events_stateful p' n ({[thread e]} ∪ u))
        else (next_events_stateful p' ({[to_base e]} ∪ n) ({[thread e]} ∪ u))
  end.

Definition next_events (p : trace) : gset base_event :=
  next_events_stateful p ∅ ∅.

(* Checks wether, given a list of active locks, a base event is locking,
   meaning that a Lock instruction is trying to get a lock that is locked,
   or that an Unlock instruction is trying to release a lock that is unlocked *)
Definition is_locking (al : gset nat) (e : base_event) : Prop :=
  match e with
  | Lock l => l ∈ al
  | Unlock l => l ∉ al
  | Join => False
  end.

Lemma forall_is_locking_empty (t : list base_event) :
  Forall (is_locking ∅) t ->
  Forall (fun e => exists l, e = Unlock l) t.
Proof.
  do 2 rewrite List.Forall_forall.
  intros Hlock e Hin.
  specialize (Hlock e Hin).
  destruct e; [done | | done].
  by exists n.
Qed.

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

Lemma valid_stateful_is_locking t b a :
  valid_stateful t a ->
  valid_stateful (t ++ [b]) a \/ is_locking (alocks_stateful t a) (to_base b).
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

Lemma valid_is_locking t b :
  valid t ->
  valid (t ++ [b]) \/ is_locking (alocks t) (to_base b).
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
  - apply head_step_step. inv H; [|by constructor].
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
      rewrite <- H0 in Hvalid. destruct Hvalid as [Hvalid _].
      rewrite elem_of_dom in H5. destruct H5. destruct x; [|done].
      rewrite not_elem_of_dom in Hvalid.
      rewrite map_filter_lookup_None in Hvalid.
      destruct Hvalid as [Hnone | Hfalse]; [simplify_eq|].
      specialize (Hfalse true H). done.
    + apply do_step with (k := fun x => x); eauto with context.
      constructor. rewrite valid_to_base_iff in Hvalid.
      rewrite <- H0 in Hvalid. destruct Hvalid as [Hvalid _].
      rewrite elem_of_dom in H5. destruct H5. destruct x; [done|].
      rewrite elem_of_dom in Hvalid.
      destruct Hvalid as [x Hvalid].
      apply map_filter_lookup_Some_1_2 in Hvalid as Hv.
      simpl in Hv. simplify_eq.
      by eapply map_filter_lookup_Some_1_1.
  - apply step_context_step; eauto with context.
  - apply step_context_step with (k := fun x => EPar x e2); eauto with context.
  - apply step_context_step; eauto with context.
Qed.

Lemma step_trace_heap_locks_none e1 h1 e2 h2:
  step_trace e1 h1 e2 h2 None ->
  heap_locks h1 = heap_locks h2.
Proof.
  intros Hsteps. remember None as n.
  induction Hsteps; [ | | destruct b; [done|]..]; eauto.
  destruct b; [done|]. inv H; [done|].
  unfold heap_locks.
  rewrite map_filter_insert_False; [|done].
  rewrite delete_notin; [done|].
  by rewrite not_elem_of_dom in H0.
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
  - rewrite <- H0 in Hvalid. rewrite heap_locks_lock; tauto.
  - rewrite <- H0 in Hvalid. rewrite heap_locks_unlock; tauto.
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
    + erewrite step_trace_heap_locks_none in Hvalid; eauto.
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
  - simpl. rewrite <- H0.
    by rewrite heap_locks_lock.
  - simpl. rewrite <- H0.
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
  - simpl in Hvalid. rewrite <- H0 in Hvalid.
    rewrite heap_locks_lock. tauto.
  - simpl in Hvalid. rewrite <- H0 in Hvalid.
    rewrite heap_locks_unlock. tauto.
Qed.

Lemma steps_trace_locks_stateful e h e' h' ph :
  steps_trace e h e' h' ph ->
  valid_stateful ph (heap_locks h) ->
  alocks_stateful ph (heap_locks h) = heap_locks h'.
Proof.
  intros Hsteps Hvalid. induction Hsteps; [done|..].
  - erewrite (step_trace_heap_locks_none _ _ _ _ H).
    erewrite step_trace_heap_locks_none in Hvalid; eauto.
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

Definition next_threads (t : trace) : gset (list bool).
Admitted. (* Idea: Redefine next_events in terms of next_threads *)

Lemma next_events_app t t' n n' u :
  next_events t = n ->
  next_threads t = u ->
  next_events_stateful t' n u = n' ->
  next_events (t ++ t') = n'.
Proof.
Admitted.

Lemma steps_trace_heap_locks_stuck e h v h' pt :
  steps_trace e h (EVal v) h' pt ->
  pt ≠ [] ->
  set_Forall (is_locking (heap_locks h)) (next_events pt) ->
  stuck e h.
Proof.
  (* Need to generalize to next_events_stateful *)
  (* Idea: Need some lemma about imm_stuck *)
Admitted.

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
  erewrite steps_trace_locks in Hdeadlock; try done.
  by eapply steps_trace_heap_locks_stuck.
Qed.

(*
  1) Verslag
    1a) Introduction
        -- Contributions incl Differences with CISL paper (globally)
    1b) Preliminaries
        -- Separation logic
        -- ISL
        -- CISL (High-level overview)
    1c) CISL_DC
    1d) CISL_DD
        -- Trace based notion of deadlock
    1e) Related Work
        -- CISL paper incl differences (detailed)
        -- Other formal definition of deadlock
    1f) Conclusion & Future work
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
