From Coq Require Export Strings.String.
From Coq Require Import Lists.List.
From iris.proofmode Require Import tactics.
Require Import Lang.

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

(* Define new step relation h_step (Step with Histories) *)

Inductive event :=
  | Lock : val -> event
  | Unlock : val -> event
  | Left : event -> event
  | Right : event -> event.
  (*| End : event.*)

Fixpoint val_eqb (v1 v2 : val) : bool :=
  match v1, v2 with
  | VUnit, VUnit => true
  | VBool b1, VBool b2 => Bool.eqb b1 b2
  | VNat n1, VNat n2 => Nat.eqb n1 n2
  | VRef l1, VRef l2 => Nat.eqb l1 l2
  | VPair v1' v1'', VPair v2' v2'' => andb (val_eqb v1' v2') (val_eqb v1'' v2'')
  | VLock l1, VLock l2 => Bool.eqb l1 l2
  | _, _ => false
  end.

Fixpoint event_eqb (s1 s2 : event) : bool :=
  match s1, s2 with
  | Lock v1, Lock v2 => val_eqb v1 v2
  | Unlock v1, Unlock v2 => val_eqb v1 v2
  | Left s1', Left s2' => event_eqb s1' s2'
  | Right s1', Left s2' => event_eqb s1' s2'
  (*| End, End => true*)
  | _, _ => false
  end.

Definition trace : Type := list event.

Inductive h_head_step : expr -> heap -> expr -> heap -> trace -> Prop :=
  | h_pure_step e e' h :
      pure_step e e' ->
      h_head_step e h e' h []
  | h_alloc_headstep h v l :
      valid_alloc h l →
      h_head_step (EAlloc (EVal v)) h (EVal (VRef l)) (<[ l := (Value v) ]> h) []
  | h_load_headstep h v l :
      h !! l = Some (Value v) →
      h_head_step (ELoad (EVal (VRef l))) h (EVal v) h []
  | h_store_headstep h v w l :
      h !! l = Some (Value w) →
      h_head_step (EStore (EVal (VRef l)) (EVal v)) h (EVal VUnit) (<[ l := (Value v) ]> h) []
  | h_free_headstep h v l :
      h !! l = Some (Value v) →
      h_head_step (EFree (EVal (VRef l))) h (EVal VUnit) (<[l := Reserved ]> h) []
  | h_lock_headstep h l :
      h_head_step (ELock (EVal (VRef l))) h (EVal VUnit) h [Lock (VRef l)]
  | h_unlock_headstep h l :
      h !! l = Some (Value (VLock true)) →
      h_head_step (EUnlock (EVal (VRef l))) h (EVal VUnit) h [Unlock (VRef l)].

Inductive h_ctx1 : (expr -> expr) -> Prop :=
  | h_pair_l_ctx e : h_ctx1 (fun x => EPair x e)
  | h_pair_r_ctx v : h_ctx1 (EPair (EVal v))
  | h_fst_ctx : h_ctx1 EFst
  | h_snd_ctx : h_ctx1 ESnd
  | h_let_ctx y e : h_ctx1 (fun x => ELet y x e)
  | h_op_l_ctx op e : h_ctx1 (fun x => EOp op x e)
  | h_op_r_ctx op v : h_ctx1 (fun x => EOp op (EVal v) x)
  | h_if_ctx e1 e2 : h_ctx1 (fun x => EIf x e1 e2)
  | h_seq_ctx e : h_ctx1 (fun x => ESeq x e)
  | h_alloc_ctx : h_ctx1 EAlloc
  | h_load_ctx : h_ctx1 ELoad
  | h_store_l_ctx e : h_ctx1 (fun x => EStore x e)
  | h_store_r_ctx v : h_ctx1 (EStore (EVal v))
  | h_free_ctx : h_ctx1 EFree
  | h_lock_ctx : h_ctx1 ELock
  | h_unlock_ctx : h_ctx1 EUnlock.

Inductive h_ctx : (expr -> expr) -> Prop :=
  | h_id_ctx : h_ctx (fun x => x)
  | h_compose_ctx k1 k2 : h_ctx1 k1 -> h_ctx k2 -> h_ctx (fun x => k1 (k2 x)).

Lemma single_h_ctx k : h_ctx1 k -> h_ctx k.
Proof.
  intro Hk. apply h_compose_ctx; [done | constructor].
Qed.

Global Hint Resolve single_h_ctx : context.
Global Hint Constructors h_ctx1 : context.
Global Hint Constructors h_ctx : context.

Ltac inv_ctx := repeat
  match goal with
  | H : ctx1 _ |- _ => inv H; try done
  | H : ctx _ |- _ => inv H; try done
  end.

Lemma h_context_Eval k e v :
  ctx k ->
  k e = EVal v ->
  k = (fun x => x) /\ e = EVal v.
Proof.
  intros Hk. induction Hk; [done|].
  intros Hk12. inv H.
Qed.

Inductive h_step : expr -> heap -> expr -> heap -> trace -> Prop :=
  | do_h_head_step e h e' h' p :
      h_head_step e h e' h' p ->
      h_step e h e' h' p
  | h_ctx_step k e h e' h' p :
      h_ctx k ->
      h_step e h e' h' p ->
      h_step (k e) h (k e') h' p
  | h_par_l_step e1 e2 h e1' h' p :
      h_step e1 h e1' h' p ->
      h_step (EPar e1 e2) h (EPar e1' e2) h' (map Left p)
  | h_par_r_step e1 e2 h e2' h' p :
      h_step e2 h e2' h' p ->
      h_step (EPar e1 e2) h (EPar e1 e2') h' (map Right p).

Inductive h_steps : expr -> heap -> expr -> heap -> trace -> Prop :=
  | h_steps_refl e h :
      h_steps e h e h []
  | h_steps_step e1 h1 e2 h2 e3 h3 p1 p2 :
      h_step e1 h1 e2 h2 p1 ->
      h_steps e2 h2 e3 h3 p2 ->
      h_steps e1 h1 e3 h3 (p1 ++ p2).

Lemma h_step_once e e' h h' p : 
  h_step e h e' h' p ->
  h_steps e h e' h' p.
Proof.
  intros Hstep.
  rewrite <- app_nil_r.
  eapply h_steps_step;
  [done | apply h_steps_refl].
Qed.

Lemma h_steps_context_steps e e' h h' k p :
  h_ctx k ->
  h_steps e h e' h' p ->
  h_steps (k e) h (k e') h' p.
Proof.
  intros Hctx Hsteps.
  induction Hsteps; [apply h_steps_refl|].
  eapply h_steps_step; [|done].
  apply h_ctx_step; eauto with context.
Qed.

Lemma h_steps_trans e e' e'' h h' h'' p p' :
  h_steps e h e' h' p ->
  h_steps e' h' e'' h'' p' ->
  h_steps e h e'' h'' (p ++ p').
Proof.
  intros H. revert p'.
  induction H; [done|].
  intros p' H'.
  rewrite <- app_assoc.
  eauto using h_steps_step, app_assoc.
Qed.

Definition event_in_trace (s : event) (p : trace) : Prop :=
  Exists (eq s) p.

Print Permutation.

Inductive can_swap : event -> event -> Prop :=
  | left_right_swap e1 e2 :
      can_swap (Left e1) (Right e2)
  | left_left_swap e1 e2 :
      can_swap e1 e2 ->
      can_swap (Left e1) (Left e2)
  | right_right_swap e1 e2 :
      can_swap e1 e2 ->
      can_swap (Right e1) (Right e2).

Print Permutation.

Inductive perm : trace -> trace -> Prop :=
  | perm_nil :
      perm [] []
  | perm_skip x l l' :
      perm l l' ->
      perm (x :: l) (x :: l')
  | perm_swap x y l :
      can_swap x y ->
      perm (x :: y :: l) (y :: x :: l)
  | perm_trans l l' l'' :
      perm l l' ->
      perm l' l'' ->
      perm l l''.

(* Active locks, the locks that are currently locked *)
(*Fixpoint alocks (p : trace) : list val :=
  match p with
  | [] => []
  | (Lock l) :: p' =>
      match event_in_trace (Unlock l) p' with
      | true => alocks p'
      | false => l :: alocks p'
      end
  | _ :: p' => alocks p'
  end.*)
(* Definition incorrect, see notes *)



