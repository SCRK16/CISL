From Coq Require Export Strings.String.
From iris.proofmode Require Import tactics.

Tactic Notation "inv" ident(H) "as" simple_intropattern(ipat) :=
  inversion H as ipat; clear H; simplify_eq.

Tactic Notation "inv" ident(H) :=
  inversion H; clear H; simplify_eq.

Inductive val :=
  | VUnit : val
  | VBool : bool -> val
  | VNat : nat -> val
  | VRef : nat -> val
  | VPair : val -> val -> val.

Inductive expr :=
  | EVal : val -> expr
  | EVar : string -> expr
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | ELet : string -> expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | ESeq : expr -> expr -> expr
  | EAlloc : expr -> expr
  | ELoad : expr -> expr
  | EStore : expr -> expr -> expr
  | EFree : expr -> expr
  | EPar : expr -> expr -> expr.

Fixpoint subst (x : string) (w : val) (e : expr) : expr :=
  match e with
  | EVal _ => e
  | EVar y => if string_dec y x then EVal w else EVar y
  | EPair e1 e2 => EPair (subst x w e1) (subst x w e2)
  | EFst e' => EFst (subst x w e')
  | ESnd e' => ESnd (subst x w e')
  | ELet y e1 e2 => if string_dec x y
     then ELet y (subst x w e1) e2
     else ELet y (subst x w e1) (subst x w e2)
  | EIf e1 e2 e3 => EIf (subst x w e1) (subst x w e2) (subst x w e3)
  | ESeq e1 e2 => ESeq (subst x w e1) (subst x w e2)
  | EAlloc e' => EAlloc (subst x w e')
  | ELoad e' => ELoad (subst x w e')
  | EStore e1 e2 => EStore (subst x w e1) (subst x w e2)
  | EFree e' => EFree (subst x w e')
  | EPar e1 e2 => EPar (subst x w e1) (subst x w e2)
  end.

(* Small steps that don't alter the heap *)
Inductive pure_step : expr -> expr -> Prop :=
  | Pair_step v1 v2 :
      pure_step (EPair (EVal v1) (EVal v2)) (EVal (VPair v1 v2))
  | Fst_step e1 e2 :
      pure_step (EFst (EPair e1 e2)) e1
  | Snd_step e1 e2 :
      pure_step (ESnd (EPair e1 e2)) e2
  | Let_step y e v :
      pure_step (ELet y (EVal v) e) (subst y v e)
  | If_true_step e1 e2 :
      pure_step (EIf (EVal (VBool true)) e1 e2) e1
  | If_false_step e1 e2 :
      pure_step (EIf (EVal (VBool false)) e1 e2) e2
  | Seq_step v e :
      pure_step (ESeq (EVal v) e) e
  | Par_step v1 v2 :
      pure_step (EPar (EVal v1) (EVal v2)) (EVal (VPair v1 v2)).

(* Either a value or reserved (previously freed)
   Corresponds to memory locations *)
Inductive loc :=
  | Value : val -> loc
  | Reserved : loc.

(* A heap maps a natural number to a memery location *)
Notation heap := (gmap nat loc).

Definition valid_alloc (h : heap) (n : nat) := ∀ e, h !! n = Some e → e = Reserved.

Inductive head_step : expr -> heap -> expr -> heap -> Prop :=
  | do_pure_step e e' h :
      pure_step e e' ->
      head_step e h e' h
  | Alloc_headstep h v l:
      valid_alloc h l →
      head_step (EAlloc (EVal v)) h (EVal (VRef l)) (<[ l := (Value v) ]> h)
  | Load_headstep h v l:
      h !! l = Some (Value v) →
      head_step (ELoad (EVal (VRef l))) h (EVal v) h
  | Store_headstep h v w l:
      h !! l = Some (Value w) →
      head_step (EStore (EVal (VRef l)) (EVal v)) h (EVal VUnit) (<[ l := (Value v) ]> h)
  | Free_headstep h v l:
      h !! l = Some (Value v) →
      head_step (EFree (EVal (VRef l))) h (EVal VUnit) (<[l := Reserved ]> h).

Inductive ctx : (expr -> expr) -> Prop :=
  | Pair_l_ctx e : ctx (fun x => EPair x e)
  | Pair_r_ctx v : ctx (EPair (EVal v))
  | Fst_ctx : ctx EFst
  | Snd_ctx : ctx ESnd
  | Let_ctx y e : ctx (fun x => ELet y x e)
  | If_ctx e1 e2 : ctx (fun x => EIf x e1 e2)
  | Seq_ctx e : ctx (fun x => ESeq x e)
  | Alloc_ctx : ctx EAlloc
  | Load_ctx : ctx ELoad
  | Store_l_ctx e : ctx (fun x => EStore x e)
  | Store_r_ctx v : ctx (EStore (EVal v))
  | Free_ctx : ctx EFree
  | Par_l_ctx e : ctx (fun x => EPar x e)
  | Par_r_ctx e : ctx (EPar e)
  | Id_ctx : ctx (fun x => x)
  | Compose_ctx k1 k2 : ctx k1 -> ctx k2 -> ctx (fun x => k1 (k2 x)).

Definition cfg : Type := expr * heap.

Inductive step : expr -> heap -> expr -> heap -> Prop :=
  | do_step k e e' h h' :
      ctx k ->
      head_step e h e' h' ->
      step (k e) h (k e') h'.

Inductive steps : expr -> heap -> expr -> heap -> Prop :=
  | steps_refl e h :
      steps e h e h
  | steps_step e1 h1 e2 h2 e3 h3 :
      step e1 h1 e2 h2 ->
      steps e2 h2 e3 h3 ->
      steps e1 h1 e3 h3.

Strategy 100 [Acc_intro_generator].

Lemma head_step_step e e' h h' :
  head_step e h e' h' -> step e h e' h'.
Proof.
  intros Hhead.
  apply (do_step (fun x => x)).
  - constructor.
  - assumption.
Qed.

Lemma step_context_step e e' h h' k :
  ctx k ->
  step e h e' h' ->
  step (k e) h (k e') h'.
Proof.
  intros Hctx Hstep.
  inversion Hstep.
  apply (do_step (fun x => (k (k0 x)))); [|done].
  by constructor.
Qed.

Lemma steps_context_steps e e' h h' k :
  ctx k ->
  steps e h e' h' ->
  steps (k e) h (k e') h'.
Proof.
  intros Hctx Hsteps.
  induction Hsteps; [apply steps_refl |].
  apply steps_step with (k e2) h2; [|done].
  by apply step_context_step.
Qed.

Lemma step_once e h e' h' :
  step e h e' h' -> steps e h e' h'.
Proof.
  intros Hstep.
  econstructor; [done | constructor].
Qed.

Create HintDb headstep.
Global Hint Resolve step_once : headstep.
Global Hint Resolve head_step_step : headstep.
Global Hint Constructors head_step : headstep.
Global Hint Constructors pure_step : headstep.

Lemma step_heap_mono e m e' m' x :
  step e m e' m' → m' ##ₘ x → m ##ₘ x.
Proof.
  intros []?. destruct H; 
  try (
    inversion H0; try assumption;
    rewrite <- H5, map_disjoint_insert_l in H1;
    by destruct H1
  ).
  inversion H0; try assumption;
    rewrite <- H7, map_disjoint_insert_l in H1;
    by destruct H1.
Qed.

Lemma steps_heap_mono e m e' m' x :
  steps e m e' m' → m' ##ₘ x -> m ##ₘ x.
Proof.
  induction 1; eauto using step_heap_mono.
Qed.

Lemma steps_trans e1 e2 e3 h1 h2 h3 :
  steps e1 h1 e2 h2 -> steps e2 h2 e3 h3 -> steps e1 h1 e3 h3.
Proof.
  intros H1 H2.
  induction H1; [done|].
  eauto using steps_step.
Qed.

Lemma steps_context e k v v' h1 h2 h3 :
  ctx k ->
  steps e h1 (EVal v') h2 ->
  steps (k (EVal v')) h2 (EVal v) h3 ->
  steps (k e) h1 (EVal v) h3.
Proof.
  intros Hctx Hsteps1 Hsteps2.
  induction Hsteps1; [done|].
  eapply steps_step.
  - apply step_context_step; done.
  - by apply IHHsteps1.
Qed.

Lemma head_step_frame_equiv e m e' m' :
  head_step e m e' m' <-> ∀ mf, m' ##ₘ mf -> head_step e (m ∪ mf) e' (m' ∪ mf).
Proof.
  split.
  1: {intros. destruct H; rewrite -? insert_union_l; try by econstructor; eauto;
    try apply lookup_union_Some_l; eauto. constructor.
    intros e He. specialize (H e). apply H. rewrite <- He.
    symmetry. apply lookup_union_l.
    assert (is_Some ((h ∪ mf) !! l)) by (by exists e).
    rewrite lookup_union_is_Some in H1. destruct H1; [done|].
    destruct H1. rewrite map_disjoint_insert_l in H0. destruct H0.
    rewrite H1 in H0. done. }
  intros. specialize (H ∅). rewrite !right_id in H.
  apply H. solve_map_disjoint.
Qed.

Lemma step_frame_equiv e m e' m' :
  step e m e' m'  ↔ ∀ mf, m' ##ₘ mf -> step e (m ∪ mf) e' (m' ∪ mf).
Proof.
  split.
  - intros []. rewrite head_step_frame_equiv in H0.
    eauto using step.
  - intros. specialize (H _ (map_disjoint_empty_r _)).
    by rewrite !right_id_L in H.
Qed.

Lemma steps_frame_equiv e h e' h' :
  steps e h e' h' ↔ ∀ hf, h' ##ₘ hf → steps e (h ∪ hf) e' (h' ∪ hf).
Proof.
  split.
  - induction 1; eauto using steps.
    intros.
    assert (h2 ##ₘ hf). { eapply steps_heap_mono; eauto. }
    rewrite step_frame_equiv in H.
    eapply steps_step; eauto.
  - intros. specialize (H _ (map_disjoint_empty_r _)).
    by rewrite !right_id_L in H.
Qed.

Delimit Scope S with S.

Definition iProp := heap → Prop.

Definition iEntails (P Q : iProp) : Prop := ∀ m, P m → Q m.
Definition iEmp : iProp := λ m, m = ∅.
Definition iPoints (l : nat) (v : val) : iProp := λ m, m = {[ l := (Value v) ]}.
Definition iNegPoints (l : nat) : iProp := λ m, m = {[ l := Reserved ]}.
Definition iSep (P Q : iProp) : iProp := λ m, ∃ m1 m2, P m1 ∧ Q m2 ∧ m = m1 ∪ m2 ∧ m1 ##ₘ m2 .
Definition iWand (P Q : iProp) : iProp := λ m, ∀ m', m ##ₘ m' → P m' → Q (m' ∪ m).
Definition iTrue : iProp := λ m , True.
Definition iAnd (P Q : iProp) : iProp := λ m, P m ∧ Q m.
Definition iOr (P Q : iProp) : iProp := λ m, P m ∨ Q m.
Definition iForall {A} (P : A → iProp) : iProp := λ m, ∀ x, P x m.
Definition iExists {A} (P : A → iProp) : iProp := λ m, ∃ x, P x m.
Definition iPure (φ : Prop) : iProp := λ m, φ ∧ m = ∅.
Definition iOwn (m : heap) : iProp := λ m', m' = m.

Notation "P ⊢ Q" := (iEntails P%S Q%S) (at level 99, Q at level 200).
Notation "P ∗ Q" := (iSep P%S Q%S) (at level 80, right associativity) : S.
Notation "P ∧ Q" := (iAnd P%S Q%S) (at level 80, right associativity) : S.
Notation "P ∨ Q" := (iOr P%S Q%S) (at level 85, right associativity) : S.
Notation "l ↦ v" := (iPoints l v) (at level 20) : S.
Notation "l ↦ ⊥" := (iNegPoints l) (at level 20) : S.
Notation "'emp'" := iEmp : S.
Notation "P -∗ Q" := (iWand P%S Q%S) (at level 99, Q at level 200, right associativity) : S.
Notation "@[ p ]" := (iPure p) (at level 1, p at level 200) : S.
Notation "∀ x1 .. xn , P" :=
  (iForall (fun x1 => .. (iForall (fun xn => P%S)) ..))
  (at level 200, x1 binder, xn binder, right associativity) : S.
Notation "∃ x1 .. xn , P" :=
  (iExists (fun x1 => .. (iExists (fun xn => P%S)) ..))
  (at level 200, x1 binder, xn binder, right associativity) : S.

Ltac iUnfold := unfold iEmp, iNegPoints, iPoints, iSep, iWand, iForall, iExists, iPure, iEntails, iAnd, iOr, iTrue in *.

Section seplogic.

  Ltac duh := iUnfold;
    naive_solver (
      rewrite ?map_union_assoc ?left_id ?right_id;
      simplify_map_eq;
      try apply map_union_comm;
      solve_map_disjoint).

  Lemma iEntails_refl P : P ⊢ P.
  Proof. duh. Qed.

  Lemma iEntails_trans Q P R : (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R).
  Proof. duh. Qed.

  Lemma iSep_mono_l P₁ P₂ Q : (P₁ ⊢ P₂) → P₁ ∗ Q ⊢ P₂ ∗ Q.
  Proof. duh. Qed.

  Lemma iSep_comm P Q : P ∗ Q ⊢ Q ∗ P.
  Proof. duh. Qed.

  Lemma iSep_assoc P Q R : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R.
  Proof. duh. Qed.

  Lemma iSep_emp_l P : P ⊢ emp ∗ P.
  Proof. duh. Qed.

  Lemma iSep_emp_l_inv P : emp ∗ P ⊢ P.
  Proof. duh. Qed.

  Lemma iWand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof. duh. Qed.

  Lemma iWand_elim P Q : P ∗ (P -∗ Q) ⊢ Q.
  Proof. duh. Qed.

  Lemma iAnd_intro (P Q R : iProp) : (R ⊢ P) → (R ⊢ Q) → R ⊢ P ∧ Q.
  Proof. duh. Qed.

  Lemma iAnd_elim_l (P Q : iProp) : P ∧ Q ⊢ P.
  Proof. duh. Qed.

  Lemma iAnd_elim_r (P Q : iProp) : P ∧ Q ⊢ Q.
  Proof. duh. Qed.

  Lemma iOr_intro_l (P Q : iProp) : P ⊢ P ∨ Q.
  Proof. duh. Qed.

  Lemma iOr_intro_r (P Q : iProp) : Q ⊢ P ∨ Q.
  Proof. duh. Qed.

  Lemma iOr_elim (P Q R : iProp) : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof. duh. Qed.

  Lemma iForall_intro {A} P (Q : A → iProp) : (∀ x, P ⊢ Q x) → (P ⊢ ∀ x, Q x).
  Proof. duh. Qed.

  Lemma iForall_elim {A} (P : A → iProp) x : (∀ z, P z) ⊢ P x.
  Proof. duh. Qed.

  Lemma iExists_intro {A} (P : A → iProp) x : P x ⊢ ∃ z, P z.
  Proof. duh. Qed.

  Lemma iExists_elim {A} (P : A → iProp) Q :  (∀ x, P x ⊢ Q) → (∃ z, P z) ⊢ Q.
  Proof. duh. Qed.

  Lemma iSep_emp_r P : P ⊢ P ∗ emp.
  Proof. duh. Qed.

  Lemma iSep_emp_r_inv P : P ∗ emp ⊢ P.
  Proof. duh. Qed.

  Lemma iSep_mono_r P Q₁ Q₂ : (Q₁ ⊢ Q₂) → P ∗ Q₁ ⊢ P ∗ Q₂.
  Proof. duh. Qed.

  Lemma iSep_mono P₁ P₂ Q₁ Q₂ : (P₁ ⊢ P₂) → (Q₁ ⊢ Q₂) → P₁ ∗ Q₁ ⊢ P₂ ∗ Q₂.
  Proof. duh. Qed.

  Lemma iSep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof. intros ? (? & ? & (? & ? & ?) & ?); repeat eexists; duh. Qed.

  Lemma iWand_intro_l P Q R : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R.
  Proof. duh. Qed.

  Lemma iExists_sep {A} (P : A → iProp) Q : (∃ x, P x) ∗ Q ⊢ ∃ x, P x ∗ Q.
  Proof. duh. Qed.

  Lemma iPure_intro (φ : Prop) : φ → emp ⊢ @[ φ ].
  Proof. duh. Qed.

  Lemma iPure_elim (φ : Prop) P Q : (φ → P ⊢ Q) → @[ φ ] ∗ P ⊢ Q.
  Proof. duh. Qed.

  Lemma iPure_elim' (φ : Prop) Q : (φ → emp ⊢ Q) → @[ φ ] ⊢ Q.
  Proof. duh. Qed.

End seplogic.

Create HintDb seplogic.

Global Hint Resolve iEntails_refl : seplogic.
Global Hint Resolve iSep_mono_l : seplogic.
Global Hint Resolve iSep_comm : seplogic.
Global Hint Resolve iSep_assoc : seplogic.
Global Hint Resolve iSep_emp_l : seplogic.
Global Hint Resolve iSep_emp_l_inv : seplogic.
Global Hint Resolve iWand_intro_r : seplogic.
Global Hint Resolve iWand_elim : seplogic.
Global Hint Resolve iAnd_intro : seplogic.
Global Hint Resolve iAnd_elim_l : seplogic.
Global Hint Resolve iAnd_elim_r : seplogic.
Global Hint Resolve iOr_intro_l : seplogic.
Global Hint Resolve iOr_intro_r : seplogic.
Global Hint Resolve iOr_elim : seplogic.
Global Hint Resolve iForall_intro : seplogic.
Global Hint Resolve iForall_elim : seplogic.
Global Hint Resolve iExists_intro : seplogic.
Global Hint Resolve iExists_elim : seplogic.
Global Hint Resolve iSep_emp_r : seplogic.
Global Hint Resolve iSep_emp_r_inv : seplogic.
Global Hint Resolve iSep_mono_r : seplogic.
Global Hint Resolve iSep_mono iSep_assoc' : seplogic.
Global Hint Resolve iWand_intro_l : seplogic.
Global Hint Resolve iExists_sep : seplogic.
Global Hint Resolve iPure_intro : seplogic.
Global Hint Resolve iPure_elim : seplogic.
Global Hint Resolve iPure_elim' : seplogic.

Definition is_val (e : expr) :=
  match e with
    | EVal _ => True
    | _ => False
  end.

Lemma not_is_val_context e k :
  ctx k -> ¬ is_val e -> ¬ is_val (k e).
Proof.
  intros Hctx. generalize e. induction Hctx; simpl; try easy.
  intros e' Hnval. by apply IHHctx1, IHHctx2.
Qed.

Definition is_error (e : expr) (h : heap) :=
  ¬ (is_val e) /\ forall e' h', not (step e h e' h').

Definition IL (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  forall v h', Q v h' -> exists h, P h /\ steps e h (EVal v) h'.

Definition ILERR (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall h', Q h' -> exists e' h, P h /\ steps e h e' h' /\ is_error e' h'.

Definition ISL (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  forall R, IL (P ∗ R)%S e (fun v => Q v ∗ R)%S.

Definition ISLERR (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall R, ILERR (P ∗ R)%S e (Q ∗ R)%S.

Lemma ISL_val (v : val) : ISL (emp)%S (EVal v) (fun x => @[ x = v ])%S.
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
  ISL P e Q ->
  (forall v, ISL (Q v) (k (EVal v)) R) ->
  ISL P (k e) R.
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
  ISL P e Q ->
  (exists v, ISL (Q v) (k (EVal v)) R) ->
  ISL P (k e) R.
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
  destruct (H h' HQ) as (e' & h & HP & Hsteps & [Hnval Herr]).
  exists (k e'), h. repeat split; [done | | |].
  - by apply steps_context_steps.
  - by apply not_is_val_context.
  - admit.
Admitted.

Lemma ISLERR_context (P Q : iProp) e k :
  ctx k ->
  ISLERR P e Q ->
  ISLERR P (k e) Q.
Proof.
  intros Hctx H R.
  by apply ILERR_context.
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
  ISL P' e Q' ->
  ISL P e Q.
Proof.
  intros HP HQ H' R. specialize (H' R).
  eapply IL_cons; [| intros v | done]; simpl; eauto with seplogic.
Qed.

Lemma ISL_IL P e Q : ISL P e Q -> IL P e Q.
Proof.
  intros H.
  specialize (H (emp)%S).
  eapply IL_cons; [| intros v | done]; simpl; eauto with seplogic.
Qed.

(* Seq rules *)
Lemma ISL_seq_val (P : iProp) (Q : val -> iProp) v e :
  ISL P e Q -> ISL P (ESeq (EVal v) e) Q.
Proof.
  intros HPQ R v' h' HQ.
  destruct (HPQ R v' h' HQ) as (h & HP & Hsteps).
  exists h. split; [done|].
  eapply steps_step; [|done].
  eauto with headstep.
Qed.

Lemma ISL_seq (P : iProp) (Q R : val -> iProp) e1 e2 :
  ISL P e1 R ->
  (exists v, ISL (R v) e2 Q) ->
  ISL P (ESeq e1 e2) Q.
Proof.
  intros HPR HRQ.
  eapply ISL_context with (k := fun x => ESeq x e2); eauto using ctx.
  destruct HRQ as [v HRQ].
  exists v. by apply ISL_seq_val.
Qed.

Lemma ctx_id k e :
  ctx k ->
  k e = e ->
  k = fun x => x.
Proof.
  intros Hctx Heq. Search (fun x => x).
  f_equal. admit.
Admitted.

Lemma ctx_seq k e e1 e2 :
  ctx k ->
  k e = ESeq e1 e2 ->
  (exists k', ctx k' /\ k = (fun x => ESeq x e2) /\ k' e = e1) \/ (k = (fun x => x) /\ e = ESeq e1 e2).
Proof.
  intros H1 Heq. revert Heq. revert e.
  induction H1; intros e' Heq; try done.
  - injection Heq. intros -> ->. left. exists (fun x => x). repeat split; try done; constructor.
  - by right.
  - destruct (IHctx1 (k2 e')) as [(h' & Hctx & Hk & He) | [Hk He]]; try done.
    + rewrite Hk in Heq. injection Heq. intros Heq2.
      rewrite Heq2 in He. apply ctx_id in He; [|done]. admit.
Admitted.

Lemma seq_step e1 e2 e' h h' :
  step (ESeq e1 e2) h e' h' ->
  (exists v, e1 = EVal v /\ e2 = e') \/ (exists e0, step e1 h e0 h' /\ e' = ESeq e0 e2).
Proof.
  intros Hstep.
  inv Hstep. apply head_step_step in H1. revert H1 H. revert e.
  induction H0; intros e' H1 H; simplify_eq.
  - right. exists e'0. by split.
  - admit. (*inv H1. inv H. inv H2.  left. by exists v.*)
  - admit.
Admitted.

Lemma not_step_seq e1 e2 h :
  is_error e1 h ->
  is_error (ESeq e1 e2) h.
Proof.
  intros [Hnval Hnstep].
  split; [easy |].
  intros e' h' Hstep.
  inv Hstep. revert H1 H. generalize e. generalize e'0. induction H0; intros e'1 e0' H1 H; simplify_eq.
  - by eapply Hnstep, head_step_step.
  - inv H1. inv H. by apply Hnval.
  - inv H0_.
    + eapply Hnstep, step_context_step; [done|].
      by apply head_step_step.
    + by eapply IHctx2.
    + admit.
Admitted.

Lemma ISLERR_seq (P Q : iProp) e1 e2 :
  ISLERR P e1 Q ->
  ISLERR P (ESeq e1 e2) Q.
Proof.
  intros HPQ R h' HQ.
  destruct (HPQ R h' HQ) as (e & h & HP & Hsteps & Herr).
  exists (ESeq e e2), h. do 2 try split; [done | | ] .
  - apply steps_context_steps with (k := fun x => ESeq x e2); [constructor | done].
  - by apply not_step_seq.
Qed.

(* EPar rules *)

Definition left (Q : val -> iProp) (v : val) : iProp := fun h =>
  match v with
    | VPair v1 v2 => Q v1 h
    | _ => False
  end.

Definition right (Q : val -> iProp) (v : val) : iProp := fun h =>
  match v with
    | VPair v1 v2 => Q v2 h
    | _ => False
  end.

Lemma ISL_par_val (Q1 Q2 : val -> iProp) v v' : 
ISL (Q1 v ∗ Q2 v')%S (EPar (EVal v) (EVal v')) (fun v0 => (@[ v0 = VPair v v' ] ∗ (left Q1 v0 ∗ right Q2 v0))%S).
Proof.
  intros R v0 h0 H.
  destruct H as (h & hr & (hemp & h12 & [-> ->] & H & -> & Hdisj) & HR & -> & HdisjR).
  destruct H as (h1 & h2 & H1 & H2 & -> & Hdisj12).
  rewrite map_empty_union. rewrite map_empty_union in HdisjR.
  simpl in H1, H2.
  exists (h1 ∪ h2 ∪ hr). split.
  - exists (h1 ∪ h2), hr. repeat split; try done.
    exists h1, h2. by repeat split.
  - eauto with headstep.
Qed.

Lemma ISL_par (P1 P2 : iProp) (Q1 Q2 : val -> iProp) e1 e2 v1 v2 :
  ISL P1 e1 (fun v => @[ v = v1 ] ∗ Q1 v)%S ->
  ISL P2 e2 (fun v => @[ v = v2 ] ∗ Q2 v)%S ->
  ISL (P1 ∗ P2)%S (EPar e1 e2) (fun v => @[ v = VPair v1 v2 ] ∗ left Q1 v ∗ right Q2 v)%S.
Proof.
  intros H1 H2.
  eapply (ISL_context _ _ _ _ (fun x => EPar x e2)).
  - constructor.
  - intros R. specialize (H1 (P2 ∗ R)%S).
    eapply IL_cons; [| | done].
    + apply iSep_assoc.
    + simpl. intros v.
      apply iSep_assoc'.
  - simpl. exists v1. eapply ISL_context.
    + constructor.
    + intros R. specialize (H2 (Q1 v1 ∗ R)%S).
      eapply IL_cons; [| | done].
      * eapply iEntails_trans.
        ++ apply iSep_assoc.
        ++ apply iSep_mono_l. eapply iEntails_trans; [apply iSep_emp_l |].
           eapply iEntails_trans; [| apply iSep_assoc].
           apply iSep_mono; by [apply iPure_intro | apply iSep_comm].
      * intros v'. simpl. apply iSep_assoc'.
    + simpl. exists v2. eapply ISL_cons; [| | apply ISL_par_val].
      2: { intros v. simpl. apply iEntails_refl. }
      eapply iEntails_trans; [apply iSep_emp_l |].
      eapply iEntails_trans; [| apply iSep_assoc].
      apply iSep_mono; by [apply iPure_intro | apply iSep_comm].
Qed.

Lemma ISL_par_err (P1 P2 Q1 Q2 : iProp) (e1 e2 : expr) :
  (ISLERR P1 e1 Q1 \/ ISLERR P2 e2 Q2) ->
  ISLERR (P1 ∗ P2)%S (EPar e1 e2) (Q1 ∗ Q2)%S.
Proof.
Admitted.

Lemma ISL_par_l (P : iProp) (R Q : val -> iProp) e1 e2 e3 :
  ISL P e1 R ->
  (exists v, ISL (R v) (EPar e2 e3) Q) ->
  ISL P (EPar (ESeq e1 e2) e3) Q.
Proof.
  intros HPR [v HRQ] W v' h' HQ.
  destruct (HRQ W v' h' HQ) as (hr & Hhr & Hsteps).
  destruct (HPR W v hr Hhr) as (hp & Hhp & Hsteps').
  exists hp. split; [done|].
  eapply steps_trans.
  {
    apply steps_context_steps with (k := fun x => EPar (ESeq x e2) e3); [|done].
    apply (Compose_ctx (fun x => EPar x e3)); constructor.
  }
  eapply steps_trans; [|done].
  eapply steps_context_steps with (k := fun x => EPar x e3); [constructor|].
  eauto with headstep.
Qed.

Lemma ISL_par_r (P : iProp) (R Q : val -> iProp) e1 e2 e3 :
  ISL P e2 R ->
  (exists v, ISL (R v) (EPar e1 e3) Q) ->
  ISL P (EPar e1 (ESeq e2 e3)) Q.
Proof.
  intros HPR [v HRQ] W v' h' HQ.
  destruct (HRQ W v' h' HQ) as (hr & Hhr & Hsteps).
  destruct (HPR W v hr Hhr) as (hp & Hhp & Hsteps').
  exists hp. split; [done|].
  eapply steps_trans.
  {
    apply steps_context_steps with (k := fun x => EPar e1 (ESeq x e3)); [|done].
    apply Compose_ctx; constructor.
  }
  eapply steps_trans; [|done].
  eapply steps_context_steps; [constructor|].
  eauto with headstep.
Qed.
