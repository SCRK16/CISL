From Coq Require Export Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Program.Equality.
From Coq Require Import Bool.DecBool.
From iris.proofmode Require Import tactics.
Require Import Lang.
Require Import perm.

Definition imm_stuck (e : expr) (h : heap) :=
  ¬ is_val e /\ forall e' h', ¬ step e h e' h'.

Definition stuck (e : expr) (h : heap) := 
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

(* Incorrecness Logic: Stuck *)
Definition ILS (P : iProp) (e : expr) (Q : iProp) :=
  forall h', Q h' -> exists e' h, P h /\ steps e h e' h' /\ imm_stuck e' h'.

Definition ISLS (P : iProp) (e : expr) (Q : iProp) :=
  forall R, ILS (P ∗ R)%S e (Q ∗ R)%S.

Notation "[[[ P ]]] e [[[S: Q ]]]" := (ISLS P%S e Q%S)
  (at level 20, e, P at level 200, Q at level 200, only parsing).

Lemma ILS_cons (P P' Q Q' : iProp) e :
  (P' ⊢ P)%S ->
  (Q ⊢ Q')%S ->
  ILS P' e Q' ->
  ILS P e Q.
Proof.
  intros HP' HQ' HIL h' HQ.
  destruct (HIL h' (HQ' h' HQ)) as (e' & h & HPh & Hsteps & Hs).
  exists e', h. eauto.
Qed.

Lemma soundness (e : expr) (Q : iProp) :
  [[[ emp ]]] e [[[S: Q ]]] ->
  (exists h', Q h') ->
  stuck e ∅.
Proof.
  intros HISLS [h' HQ].
  specialize (HISLS emp%S).
  apply ILS_cons with (P := emp%S) (Q := Q) in HISLS;
  [ | eauto with seplogic..].
  destruct (HISLS h' HQ) as (e' & h & Hh & Hsteps & Hs).
  exists e', h'.
  by inv Hh.
Qed.

Inductive seq_ctx1 : (expr -> expr) -> Prop :=
  | Pair_l_ctx e : seq_ctx1 (fun x => EPair x e)
  | Pair_r_ctx v : seq_ctx1 (EPair (EVal v))
  | Fst_ctx : seq_ctx1 EFst
  | Snd_ctx : seq_ctx1 ESnd
  | Let_ctx y e : seq_ctx1 (fun x => ELet y x e)
  | Op_l_ctx op e : seq_ctx1 (fun x => EOp op x e)
  | Op_r_ctx op v : seq_ctx1 (fun x => EOp op (EVal v) x)
  | If_ctx e1 e2 : seq_ctx1 (fun x => EIf x e1 e2)
  | Seq_ctx e : seq_ctx1 (fun x => ESeq x e)
  | Alloc_ctx : seq_ctx1 EAlloc
  | Load_ctx : seq_ctx1 ELoad
  | Store_l_ctx e : seq_ctx1 (fun x => EStore x e)
  | Store_r_ctx v : seq_ctx1 (EStore (EVal v))
  | Free_ctx : seq_ctx1 EFree
  | Lock_ctx : seq_ctx1 ELock
  | Unlock_ctx : seq_ctx1 EUnlock.

Inductive seq_ctx : (expr -> expr) -> Prop :=
  | Id_ctx : seq_ctx (fun x => x)
  | Compose_ctx k1 k2 : seq_ctx1 k1 -> seq_ctx k2 -> seq_ctx (fun x => k1 (k2 x)).

Lemma seq_ctx1_ctx1 k :
  seq_ctx1 k -> ctx1 k.
Proof.
  intros Hctx.
  inv Hctx; constructor.
Qed.

Lemma seq_ctx_ctx k :
  seq_ctx k -> ctx k.
Proof.
  intros Hctx.
  induction Hctx; constructor; [|done].
  by apply seq_ctx1_ctx1.
Qed.

Lemma seq_ctx_eq k k' e e' :
  ctx1 k ->
  seq_ctx1 k' ->
  ¬ is_val e ->
  ¬ is_val e' ->
  k e = k' e' ->
  k = k' /\ e = e'.
Proof.
  intros Hctx Hctx' Hnval Hnval' Heq.
  inv Hctx; inv Hctx'; try done.
Qed.

Ltac seq_ctx_not_step_tac k e := repeat
  match goal with
  | H : seq_ctx1 _ |- _ => inv H
  | H : EVal _ = k e |- is_val (k e) => by rewrite <- H
  | H : EVal _ = k e |- False => apply (not_is_val_context e k)
  | H : seq_ctx k |- ctx k => by apply seq_ctx_ctx
  | H : pure_step _ _ |- _ => inv H
  | H : head_step _ _ _ _ |- _ => inv H
  | H : _ |- _ => try done
  end.

Lemma seq_ctx_not_step k e h :
  seq_ctx k ->
  ¬ is_val e ->
  (forall e' h', ¬ step e h e' h') ->
  (forall e' h', ¬ step (k e) h e' h').
Proof.
  intros Hctx Hnval Hnstep e' h' Hstep.
  inv Hstep. inv Hctx; [by eapply Hnstep |].
  induction H0; [seq_ctx_not_step_tac k2 e|].
  admit.

(*intros Hctx. revert e. inv Hctx;
  intros e Hnval Hnstep e' h' Hstep;
  [by eapply Hnstep |].
  inv Hstep. revert H1 H0 H. induction H2;
  intros H' H0 H1.
  - seq_ctx_not_step_tac k2 e.
  - *)

Admitted.



Lemma ILS_seq_ctx (P Q : iProp) e k :
  seq_ctx k ->
  ILS P e Q ->
  ILS P (k e) Q.
Proof.
  intros Hctx H h' HQ.
  destruct (H h' HQ) as (e' & h & HP & Hsteps & Hnval & Hnstep).
  exists (k e'), h. repeat split; [done | ..].
  - apply steps_context_steps; eauto using seq_ctx_ctx.
  - apply seq_ctx_ctx in Hctx.
    by apply not_is_val_context.
  - by apply seq_ctx_not_step.
Qed.

Lemma ISLS_seq_ctx (P Q : iProp) e k :
  seq_ctx k ->
  [[[ P ]]] e [[[S: Q ]]] ->
  [[[ P ]]] k e [[[S: Q ]]].
Proof.
  intros Hctx H R.
  by apply ILS_seq_ctx.
Qed.

Ltac iSep_mono_l_comm R :=
  eapply (iSep_mono_l _ _ R);
  [apply iSep_comm | by apply iSep_assoc].

Lemma ILS_par (P P' Q Q' : iProp) (e e' : expr) :
  ISLS P e Q ->
  ISLS P' e' Q' ->
  ISLS (P ∗ P') (EPar e e') (Q ∗ Q').
Proof.
  intros H H' R h HQQR.
  assert (H0 : (Q ∗ Q' ∗ R)%S h) by (by apply iSep_assoc').
  destruct (H (Q' ∗ R)%S h H0) as (e0 & h0 & HPQR & Hsteps & Hstuck).
  assert (H1 : (Q' ∗ P ∗ R)%S h0).
  { apply iSep_assoc'. iSep_mono_l_comm R. }
  destruct (H' (P ∗ R)%S h0 H1) as (e1 & h1 & HPPR & Hsteps' & Hstuck').
  exists (EPar e0 e1), h1. split; [|split].
  - iSep_mono_l_comm R.
  - eapply steps_trans.
    + apply steps_context_steps;
      eauto with context.
    + apply steps_context_steps with (k := fun x => EPar x e1);
      eauto with context.
  - apply imm_stuck_par; [done|].
    admit.
Admitted.


(************************
        HISTORIES
************************)

(* 
   Define new step relation steps_trace
   This is a step relation that also keeps track of a trace (history),
   the events that have happened during the execution of the program
*)



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

Inductive head_step_trace : expr -> heap -> expr -> heap -> option base_event -> Prop :=
  | do_pure_step_trace e e' h b :
      pure_step_trace e e' b ->
      head_step_trace e h e' h b
  | alloc_head_step_trace h v l :
      valid_alloc h l →
      head_step_trace
        (EAlloc (EVal v)) h
        (EVal (VRef l)) (<[ l := (Value v) ]> h) None
  | load_head_step_trace h v l :
      h !! l = Some (Value v) →
      head_step_trace
        (ELoad (EVal (VRef l))) h
        (EVal v) h None
  | store_head_step_trace h v w l :
      h !! l = Some (Value w) →
      head_step_trace
        (EStore (EVal (VRef l)) (EVal v)) h
        (EVal VUnit) (<[ l := (Value v) ]> h) None
  | free_head_step_trace h v l :
      h !! l = Some (Value v) →
      head_step_trace
        (EFree (EVal (VRef l))) h
        (EVal VUnit) (<[l := Reserved ]> h) None
  | lock_head_step_trace h l :
      head_step_trace
        (ELock (EVal (VRef l))) h
        (EVal VUnit) h (Some (Lock (VRef l)))
  | unlock_head_step_trace h l :
      head_step_trace
        (EUnlock (EVal (VRef l))) h
        (EVal VUnit) h (Some (Unlock (VRef l))).

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
  | alloc_ctx_trace : ctx_trace EAlloc
  | load_ctx_trace : ctx_trace ELoad
  | store_l_ctx_trace e : ctx_trace (fun x => EStore x e)
  | store_r_ctx_trace v : ctx_trace (EStore (EVal v))
  | free_ctx_trace : ctx_trace EFree
  | lock_ctx_trace : ctx_trace ELock
  | unlock_ctx_trace : ctx_trace EUnlock.

Global Hint Constructors ctx_trace : context.

Inductive step_trace : expr -> heap -> expr -> heap -> option event -> Prop :=
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

Definition unleft (e : event) : option event :=
  match e with
  | Left b => Some b
  | _ => None
  end.

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

Inductive steps_trace : expr -> heap -> expr -> heap -> trace -> Prop :=
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
Global Hint Constructors steps_trace : step_trace.
Global Hint Constructors head_step_trace : step_trace.
Global Hint Constructors pure_step_trace : step_trace.
Global Hint Resolve head_step_trace_some : step_trace.
Global Hint Resolve head_step_trace_none : step_trace.
Global Hint Resolve par_l_step_trace_some : step_trace.
Global Hint Resolve par_r_step_trace_some : step_trace.
Global Hint Resolve par_l_step_trace_none : step_trace.
Global Hint Resolve par_r_step_trace_none : step_trace.


Lemma step_once_none e e' h h' : 
  step_trace e h e' h' None ->
  steps_trace e h e' h' [].
Proof.
  intros Hstep.
  eauto using steps_trace.
Qed.

Lemma steps_once_some e e' h h' (b : event) :
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

Definition event_in_trace (s : event) (p : trace) : Prop :=
  Exists (eq s) p.

Lemma steps_perm e h e' h' (t t' : trace) :
  perm t t' ->
  steps_trace e h e' h' t ->
  steps_trace e h e' h' t'.
Proof.
  intros Hperm Hsteps. revert t' Hperm.
  induction Hsteps; intros t' Hperm.
  - rewrite (perm_nil_is_nil _ Hperm).
    apply steps_refl_trace.
  - eapply steps_step_none; by [|apply IHHsteps].
  - revert H Hsteps IHHsteps. revert e1 h1 e2 h2 e3 h3. induction t'.
    { by apply perm_symm, perm_nil_is_nil in Hperm. }
    intros e1 h1 e2 h2 e3 h3 Hstep Hsteps IH.
    destruct (event_eq_dec a b).
    + simplify_eq. admit.
    + admit.
Admitted.

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

Lemma val_eq_dec (x y : val) : {x = y} + {x ≠ y}.
Proof.
  decide equality.
Restart.
  revert y. induction x; intros y; destruct y; try auto.
  1,5: destruct b; destruct b0; auto.
  1,2: destruct (Nat.eq_dec n n0); [auto|];
    right; by injection.
  destruct (IHx1 y1); destruct (IHx2 y2);
  simplify_eq; [auto|right..]; by injection.
Qed.

(* alocks are the active locks, the locks that are currently locked *)
Fixpoint alocks_stateful (p : trace) (a : list val) : list val :=
  match p with
  | [] => a
  | e :: p' =>
      match to_base e with
      | Lock l => alocks_stateful p' (l :: a)
      | Unlock l => alocks_stateful p' (remove val_eq_dec l a)
      | Join => alocks_stateful p' a
      end
  end.

Definition alocks (p : trace) : list val := alocks_stateful p [].

(* the thread is the combination of left/right of an event,
   represented as a list of bools *)
Fixpoint thread_stateful (e : event) (a : list bool) : list bool :=
  match e with
  | Base _ => a
  | Left b => thread_stateful b (a ++ [false])
  | Right b => thread_stateful b (a ++ [true])
  end.

Definition thread (e : event) : list bool := thread_stateful e [].

Print ifdec.

Fixpoint is_prefix (l l' : list bool) : bool :=
  match l, l' with
  | [], _ => true
  | _, [] => false
  | (b :: r), (b' :: r') => andb (Bool.eqb b b') (is_prefix r r')
  end.

Definition is_parent_or_child (tid tid' : list bool) : bool :=
  orb (is_prefix tid tid') (is_prefix tid' tid).

(* next events are events that could be scheduled next *)
(* they are the first instruction of a thread that is running concurrently *)

Print existsb.

Fixpoint next_events_stateful
  (p : trace) (n : list base_event) (u : list (list bool)) : list base_event :=
  match p with
  | [] => n
  | e :: p' =>
      if existsb (is_parent_or_child (thread e)) u
        then (next_events_stateful p' n (thread e :: u))
        else (next_events_stateful p' (to_base e :: n) (thread e :: u))
  end.

Definition next_events (p : trace) : list base_event :=
  next_events_stateful p [] [].

Fixpoint active (tid : list bool) (t : trace) : Prop :=
  match t with
  | [] => False
  | e :: t' => thread e = tid ∨
      (¬ is_prefix (thread e) tid ∧ ¬ is_prefix tid (thread e) ∧ active tid t')
  end.

Definition example_program : expr :=
  EPar (EPar (ELock (EVal (VRef 0))) (ELock (EVal (VRef 1))))
       (EPar (ELock (EVal (VRef 2))) (ELock (EVal (VRef 3)))).

Example threading_example :
  steps_trace
    example_program ∅
    (EVal (VPair (VPair VUnit VUnit) (VPair VUnit VUnit))) ∅
    [Left (Left (Base (Lock (VRef 0))));
     Left (Right (Base (Lock (VRef 1))));
     Left (Base Join);
     Right (Left (Base (Lock (VRef 2))));
     Right (Right (Base (Lock (VRef 3))));
     Right (Base Join);
     Base Join].
Proof. eauto 28 with step_trace. Qed.

Example active_example (b1 b2 : base_event) :
  active [true; false] [Left (Base b1); Right (Left (Base b2))].
Proof.
  compute. right. split; [|split]; tauto.
Qed.

(* Checks wether, given a list of active locks, a base event is locking,
   meaning that a Lock instruction is trying to get a lock that is locked,
   or that an Unlock instruction is trying to release a lock that is unlocked *)
Definition is_locking (al : list val) (e : base_event) : Prop :=
  match e with
  | Lock l => In l al
  | Unlock l => ~In l al
  | Join => False
  end.

Definition deadlock (t : trace) : Prop :=
  ∃ (ph pt : trace), perm t (ph ++ pt) ∧
      Forall (is_locking (alocks ph)) (next_events pt).

(* Probably needed: The expressions do not contain a heap
    instruction that changes the locks *)
Theorem trace_soundness (e e' : expr) h h' (t : trace) :
  steps_trace e h e' h' t ->
  deadlock t ->
  stuck e h.
Proof.
  intros Hsteps Hdeadlock.
Admitted.
