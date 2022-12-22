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
Inductive cell :=
  | Value : val -> cell
  | Reserved : cell.

(* A heap maps a natural number to a memory location *)
Notation heap := (gmap nat cell).

Definition valid_alloc (h : heap) (n : nat) := ∀ c, h !! n = Some c → c = Reserved.

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

Inductive ctx1 : (expr -> expr) -> Prop :=
  | Pair_l_ctx e : ctx1 (fun x => EPair x e)
  | Pair_r_ctx v : ctx1 (EPair (EVal v))
  | Fst_ctx : ctx1 EFst
  | Snd_ctx : ctx1 ESnd
  | Let_ctx y e : ctx1 (fun x => ELet y x e)
  | If_ctx e1 e2 : ctx1 (fun x => EIf x e1 e2)
  | Seq_ctx e : ctx1 (fun x => ESeq x e)
  | Alloc_ctx : ctx1 EAlloc
  | Load_ctx : ctx1 ELoad
  | Store_l_ctx e : ctx1 (fun x => EStore x e)
  | Store_r_ctx v : ctx1 (EStore (EVal v))
  | Free_ctx : ctx1 EFree
  | Par_l_ctx e : ctx1 (fun x => EPar x e)
  | Par_r_ctx e : ctx1 (EPar e).

Inductive ctx : (expr -> expr) -> Prop :=
  | Id_ctx : ctx (fun x => x)
  | Compose_ctx k1 k2 : ctx1 k1 -> ctx k2 -> ctx (fun x => k1 (k2 x)).

Lemma Single_ctx k : ctx1 k -> ctx k.
Proof.
  intros Hk. apply Compose_ctx; [done | constructor].
Qed.

Create HintDb context.
Global Hint Resolve Single_ctx : context.
Global Hint Constructors ctx1 : context.
Global Hint Constructors ctx : context.

Lemma context_EVal k e v :
  ctx k -> 
  k e = EVal v ->
  k = (fun x => x) /\ e = EVal v.
Proof.
  intros Hk. induction Hk; [done|].
  intros Hk12. inv H.
Qed.

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

Strategy 100 [Acc_intro_generator]. (* Remove? *)

Lemma head_step_step e e' h h' :
  head_step e h e' h' -> step e h e' h'.
Proof.
  intros Hhead.
  apply (do_step (fun x => x)).
  - repeat constructor.
  - assumption.
Qed.

Lemma step_context_step e e' h h' k :
  ctx k ->
  step e h e' h' ->
  step (k e) h (k e') h'.
Proof.
  intros Hctx Hstep. induction Hctx; [done|].
  inv IHHctx. apply (do_step (fun x => (k1 (k x)))); [|done].
  by apply Compose_ctx.
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

Infix "###" := map_disjoint (at level 70). (* Replace everywhere *)

Lemma step_heap_mono e m e' m' x :
  step e m e' m' → m' ### x → m ### x.
Proof.
  intros []?. destruct H; 
  inv H0; try assumption;
  rewrite map_disjoint_insert_l in H1;
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

Definition is_val (e : expr) :=
  match e with
    | EVal _ => True
    | _ => False
  end.

Lemma not_is_val_context e k :
  ctx k -> ¬ is_val e -> ¬ is_val (k e).
Proof.
  intros Hctx. generalize e. induction Hctx; intros e' Hnval;
  [done | destruct H; easy].
Qed.

(*
Immediate unsafe: An expression is immediately unsafe if:
  1. It is not a value
  2. None of the subexpressions within it can step
*)

Definition imm_unsafe (e : expr) (h : heap) :=
  ¬ is_val e /\ forall e' h', ¬ step e h e' h'.

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

Delimit Scope S with S.

Definition iProp := heap → Prop.

Bind Scope S with iProp.

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

  Lemma iPure_intro' (φ : Prop) P : φ → P ⊢ @[ φ ] ∗ P.
  Proof. duh. Qed.

  Lemma iPure_elim (φ : Prop) P Q : (φ → P ⊢ Q) → @[ φ ] ∗ P ⊢ Q.
  Proof. duh. Qed.

  Lemma iPure_elim' (φ : Prop) Q : (φ → emp ⊢ Q) → @[ φ ] ⊢ Q.
  Proof. duh. Qed.

  Lemma iOr_distr (P Q R : iProp) : (P ∨ Q) ∗ R ⊢ (P ∗ R) ∨ (Q ∗ R).
  Proof. duh. Qed.

  Lemma iOr_distr' (P Q R : iProp) : (P ∗ R) ∨ (Q ∗ R) ⊢ (P ∨ Q) ∗ R.
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
Global Hint Resolve iPure_intro' : seplogic.
Global Hint Resolve iPure_elim : seplogic.
Global Hint Resolve iPure_elim' : seplogic.

(* Notation for triples *)

Definition IL (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  forall v h', Q v h' -> exists h, P h /\ steps e h (EVal v) h'.

Definition ILERR (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall h', Q h' -> exists e' h, P h /\ steps e h e' h' /\ is_error e' h'.

Definition ISL (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  forall R, IL (P ∗ R)%S e (fun v => Q v ∗ R)%S.

Definition ISLERR (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall R, ILERR (P ∗ R)%S e (Q ∗ R)%S.

Lemma ISL_val (v : val) : ISL emp (EVal v) (fun x => @[ x = v ])%S.
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
  destruct (H h' HQ) as (e' & h & HP & Hsteps & (k' & es & Hctx' & Heq & Herr)).
  exists (k e'), h. repeat split; [done | | ].
  - by apply steps_context_steps.
  - simplify_eq. do 2 (apply is_error_ctx; [done|]). by apply unsafe_is_error.
Qed.

Lemma ISLERR_context (P Q : iProp) e k :
  ctx k ->
  ISLERR P e Q ->
  ISLERR P (k e) Q.
Proof.
  intros Hctx H R.
  by apply ILERR_context.
Qed.

(* ISLERR_context_ISL met exists ipv @[x = v] *)

Lemma ISLERR_context_ISL (P Q : iProp) (R : val -> iProp) e v k :
  ctx k ->
  ISL P e (fun x => @[x = v] ∗ R x)%S ->
  ISLERR (R v) (k (EVal v)) Q ->
  ISLERR P (k e) Q.
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
  ISLERR P' e Q' ->
  ISLERR P e Q.
Proof.
  intros ????.
  eauto using ILERR_cons, iSep_mono_l.
Qed.

Lemma ISL_sep_assoc_post (P Q2 Q3 : iProp) (Q1 : val -> iProp) e :
  ISL P e (fun x => (Q1 x ∗ Q2) ∗ Q3)%S ->
  ISL P e (fun x => Q1 x ∗ Q2 ∗ Q3)%S.
Proof.
  intros HISL.
  eapply ISL_cons; [apply iEntails_refl | |done].
  intros v. simpl. apply iSep_assoc.
Qed.

Lemma ISL_sep_assoc'_post (P Q2 Q3 : iProp) (Q1 : val -> iProp) e :
  ISL P e (fun x => Q1 x ∗ Q2 ∗ Q3)%S ->
  ISL P e (fun x => (Q1 x ∗ Q2) ∗ Q3)%S.
Proof.
  intros HISL.
  eapply ISL_cons; [apply iEntails_refl | |done].
  intros v. simpl. apply iSep_assoc'.
Qed.

(* Frame rules *)

Lemma ISL_frame (R P : iProp) (Q : val -> iProp) e :
  ISL P e Q -> ISL (P ∗ R)%S e (fun x => Q x ∗ R)%S.
Proof.
  intros HPQ T v h' HQRT.
  apply iSep_assoc' in HQRT.
  specialize (HPQ (R ∗ T)%S v h' HQRT).
  destruct HPQ as (h & HPRT & Hsteps).
  exists h. split; by [apply iSep_assoc |].
Qed.

Lemma ISL_frame_left (R P : iProp) (Q : val -> iProp) e :
  ISL P e Q -> ISL (R ∗ P)%S e (fun x => R ∗ Q x)%S.
Proof.
  intros HPQ.
  apply (ISL_cons _ (P ∗ R) _ (fun x => Q x ∗ R)%S).
  - apply iSep_comm.
  - intros v. apply iSep_comm.
  - by apply ISL_frame.
Qed.

Lemma ISLERR_frame (R P Q : iProp) e :
  ISLERR P e Q -> ISLERR (P ∗ R)%S e (Q ∗ R)%S.
Proof.
  intros HPQ T.
  specialize (HPQ (R ∗ T)%S).
  eapply ILERR_cons; [ | | done]; eauto with seplogic.
Qed.

(* Step rules *)

Lemma ISL_pure_step (P : iProp) (Q : val -> iProp) e e' :
  ISL P e' Q ->
  pure_step e e' ->
  ISL P e Q.
Proof.
  intros HPQ Hstep W v h Hh.
  destruct (HPQ W v h Hh) as (h' & Hh' & Hsteps).
  exists h'. split; [done|].
  eapply steps_step; [|done].
  eauto with headstep.
Qed.

Lemma ISL_pure_step_context (P : iProp) (Q : val -> iProp) e e' k :
  ctx k ->
  ISL P (k e') Q ->
  pure_step e e' ->
  ISL P (k e) Q.
Proof.
  intros Hctx HPQ Hstep W v h Hh.
  destruct (HPQ W v h Hh) as (h' & Hh' & Hsteps).
  exists h'. split; [done|].
  eapply steps_step; [|done].
  apply do_step; by [|constructor].
Qed.

Lemma ISLERR_pure_step (P Q : iProp) e e' :
  ISLERR P e' Q ->
  pure_step e e' ->
  ISLERR P e Q.
Proof.
  intros HPQ Hstep W h Hh.
  destruct (HPQ W h Hh) as (e0 & h0 & Hh0 & Hsteps & Herr).
  exists e0, h0. do 2 try split; [done | | done].
  eapply steps_step; [|done].
  eauto with headstep.
Qed.

Lemma ISLERR_pure_step_context (P Q : iProp) e e' k :
  ctx k ->
  ISLERR P (k e') Q ->
  pure_step e e' ->
  ISLERR P (k e) Q.
Proof.
  intros Hctx HPQ Hstep W h Hh.
  destruct (HPQ W h Hh) as (e0 & h0 & Hh0 & Hsteps & Herr).
  exists e0, h0. do 2 try split; [done | | done].
  eapply steps_step; [|done].
  apply do_step; by [|constructor].
Qed.

(* Quantifier rules *)
Lemma ISL_exists_post {A} (P : iProp) (Q : A -> val -> iProp) e :
  (forall s, ISL P e (Q s)) ->
  ISL P e (fun x => ∃ s, Q s x)%S.
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
  ISL P e Q ->
  ISL P' e Q' ->
  ISL (P ∨ P')%S e (fun x => Q x ∨ Q' x)%S.
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
  [ destruct (H h' HQ) as (e' & h & HP & Hsteps & Herr) | destruct (H' h' HQ') as (e' & h & HP & Hsteps & Herr) ];
  exists e', h; split; eauto; by [left | right].
Qed.

Lemma ISLERR_disj (P P' Q Q' : iProp) e :
  ISLERR P e Q ->
  ISLERR P' e Q' ->
  ISLERR (P ∨ P')%S e (Q ∨ Q')%S.
Proof.
  intros H H' R.
  eapply ILERR_cons.
  3: { apply ILERR_disj; [apply H | apply H']. }
  1,2: eauto using iOr_distr, iOr_distr'.
Qed.

(* Pure rules *)

Lemma ISL_pure (P : iProp) (Q : val -> iProp) (phi : Prop) e :
  (phi -> ISL P e Q) -> ISL P e (fun x => @[phi] ∗ Q x)%S.
Proof.
  intros H R v h (h' & hR & (h0 & hQ & [Hphi ->] & HQ & -> & Hdisj') & HR & -> & Hdisj).
  rewrite left_id. rewrite left_id in Hdisj.
  destruct (H Hphi R v (hQ ∪ hR)) as (h & HP & Hsteps); [exists hQ, hR|]; eauto.
Qed.

Lemma ISL_pure' (P : iProp) (Q : val -> iProp) (phi : val -> Prop) e :
  ((exists x, phi x) -> ISL P e Q) -> ISL P e (fun x => @[phi x] ∗ Q x)%S.
Proof.
  intros H R v h (h' & hR & (h0 & hQ & [Hphi ->] & HQ & -> & Hdisj') & HR & -> & Hdisj).
  rewrite left_id. rewrite left_id in Hdisj.
  destruct (H (ex_intro _ _ Hphi) R v (hQ ∪ hR)) as (h & HP & Hsteps); [exists hQ, hR|]; eauto.
Qed.

Lemma ISLERR_pure (P Q : iProp) (phi : Prop) e :
  (phi -> ISLERR P e Q) -> ISLERR P e (@[phi] ∗ Q).
Proof.
  intros H R h (h' & hR & (h0 & hQ & [Hphi ->] & HQ & -> & Hdisj') & HR & -> & Hdisj).
  rewrite left_id. rewrite left_id in Hdisj.
  destruct (H Hphi R (hQ ∪ hR)) as (h & HP & Hsteps); [exists hQ, hR|]; eauto.
Qed.

(* ESeq rules *)

Lemma ISL_seq_val (P : iProp) (Q : val -> iProp) v e :
  ISL P e Q -> ISL P (ESeq (EVal v) e) Q.
Proof.
  intros HPQ.
  eapply ISL_pure_step; [done | constructor].
Qed.

Lemma ISL_seq (P : iProp) (Q R : val -> iProp) e1 e2 :
  ISL P e1 R ->
  (exists v, ISL (R v) e2 Q) ->
  ISL P (ESeq e1 e2) Q.
Proof.
  intros HPR HRQ.
  eapply ISL_context with (k := fun x => ESeq x e2);
  eauto with context.
  destruct HRQ as [v HRQ].
  exists v. by apply ISL_seq_val.
Qed.

Lemma ISLERR_seq (P Q : iProp) e1 e2 :
  ISLERR P e1 Q ->
  ISLERR P (ESeq e1 e2) Q.
Proof.
  intros HPQ.
  apply ISLERR_context with (k := fun x => ESeq x e2);
  [eauto with context | done].
Qed.

Lemma ISLERR_seq_right (P Q : iProp) (R : val -> iProp) e1 e2 :
  ISL P e1 R ->
  (exists v, ISLERR (R v) e2 Q) ->
  ISLERR P (ESeq e1 e2) Q.
Proof.
  intros HPR [v HRQ].
  eapply ISLERR_context_ISL with (k := fun x => ESeq x e2);
  [eauto with context | |].
  - eapply ISL_cons; [apply iEntails_refl | | done].
    intros v'. apply iPure_elim. intros ->. apply iEntails_refl.
  - eapply ISLERR_pure_step; [done | constructor].
Qed.

(* EIf rules *)

Lemma ISL_if_true (P : iProp) (Q R : val -> iProp) e1 e2 e3 :
  ISL P e1 (fun x => @[x = VBool true] ∗ R x)%S ->
  ISL (R (VBool true)) e2 Q ->
  ISL P (EIf e1 e2 e3) Q.
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
  ISL P e1 (fun x => @[x = VBool false] ∗ R x)%S ->
  ISL (R (VBool false)) e3 Q ->
  ISL P (EIf e1 e2 e3) Q.
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
  ISLERR P e1 Q ->
  ISLERR P (EIf e1 e2 e3) Q.
Proof.
  intros HPQ.
  eapply ISLERR_context with (k := fun x => EIf x e2 e3);
  [eauto with context | done].
Qed.

Lemma ISLERR_if_true (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  ISL P e1 (fun x => @[x = VBool true] ∗ R x)%S ->
  ISLERR (R (VBool true)) e2 Q ->
  ISLERR P (EIf e1 e2 e3) Q.
Proof.
  intros HPR HRQ.
  eapply ISLERR_context_ISL with (k := fun x => EIf x e2 e3);
  [eauto with context | done |].
  eapply ISLERR_pure_step; [done | constructor].
Qed.

Lemma ISLERR_if_false (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  ISL P e1 (fun x => @[x = VBool false] ∗ R x)%S ->
  ISLERR (R (VBool false)) e3 Q ->
  ISLERR P (EIf e1 e2 e3) Q.
Proof.
  intros HPR HRQ.
  eapply ISLERR_context_ISL with (k := fun x => EIf x e2 e3);
  [eauto with context | done |].
  eapply ISLERR_pure_step; [done | constructor].
Qed.

(* EAlloc rules *)

Ltac empty_left H := rewrite left_id; rewrite left_id in H.

(* The basic behavior of alloc *)
Lemma ISL_Alloc_val l v :
  ISL emp (EAlloc (EVal v)) (fun x => @[x = VRef l] ∗ l ↦ v)%S.
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
  ISL emp (EAlloc (EVal v)) (fun x => ∃ l, @[x = VRef l] ∗ l ↦ v)%S.
Proof.
  eauto using ISL_exists_post, ISL_Alloc_val.
Qed.

(* This lemma shows that we can reuse previously freed locations *)
Lemma ISL_Alloc_reuse l v :
  ISL (l ↦ ⊥) (EAlloc (EVal v)) (fun x => @[x = VRef l] ∗ l ↦ v)%S.
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
  ISL (l ↦ v) (ELoad (EVal (VRef l))) (fun x => @[x = v] ∗ l ↦ v)%S.
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
  - inv H2. apply (context_EVal _ _ _ H3) in H.
    destruct H. simplify_eq.
    inv H1. inv H.
Qed.

Lemma ISLERR_load l :
  ISLERR (l ↦ ⊥) (ELoad (EVal (VRef l))) (l ↦ ⊥).
Proof.
  intros R h' (h1 & h2 & -> & H2 & -> & Hdisj).
  exists (ELoad (EVal (VRef l))), ({[l := Reserved]} ∪ h2).
  repeat split; [by exists {[l := Reserved]}, h2 | apply steps_refl | ].
  apply unsafe_is_error. split;
  auto using load_reserved_not_step.
Qed.

(* EStore rules *)

Lemma ISL_Store l v w :
  ISL (l ↦ v) (EStore (EVal (VRef l)) (EVal w)) (fun x => @[x = VUnit] ∗ (l ↦ w))%S.
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
  - inv H2.
    + apply (context_EVal _ _ _ H3) in H.
      destruct H. simplify_eq.
      inv H1. inv H.
    + apply (context_EVal _ _ _ H3) in H0.
      destruct H0. simplify_eq.
      inv H1. inv H.
Qed.

Lemma ISLERR_store l v :
  ISLERR (l ↦ ⊥) (EStore (EVal (VRef l)) (EVal v)) (l ↦ ⊥).
Proof.
  intros R h' (h0 & hR & -> & HR & -> & Hdisj).
  exists (EStore (EVal (VRef l)) (EVal v)), ({[l := Reserved]} ∪ hR).
  repeat split; [by exists {[l := Reserved]}, hR | apply steps_refl | ].
  apply unsafe_is_error. split;
  auto using store_reserved_not_step.
Qed.

(* EFree rules *)

Lemma ISL_free l v :
  ISL (l ↦ v) (EFree (EVal (VRef l))) (fun x => @[x = VUnit] ∗ l ↦ ⊥)%S.
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
  - inv H2.
    apply (context_EVal _ _ _ H3) in H.
    destruct H. simplify_eq.
    inv H1. inv H.
Qed.

Lemma ISLERR_free l :
  ISLERR (l ↦ ⊥) (EFree (EVal (VRef l))) (l ↦ ⊥).
Proof.
  intros R h' (h0 & hR & -> & HR & -> & Hdisj).
  exists (EFree (EVal (VRef l))), ({[l := Reserved]} ∪ hR).
  repeat split; [by exists {[l := Reserved]}, hR | apply steps_refl | ].
  apply unsafe_is_error. split;
  auto using free_reserved_not_step.
Qed.

(* EPar rules *)

Lemma ISL_par_val (Q1 Q2 : val -> iProp) v v' :
  ISL (Q1 v ∗ Q2 v')%S (EPar (EVal v) (EVal v')) (fun v0 => (@[ v0 = VPair v v' ] ∗ Q1 v ∗ Q2 v')%S).
Proof.
  eapply ISL_pure_step; [|constructor].
  eapply ISL_sep_assoc_post, ISL_frame, ISL_cons; [apply iSep_emp_l_inv | intros v0; apply iEntails_refl |].
  eapply ISL_frame, ISL_val.
Qed.

Lemma ISL_par_val_emp v v' :
  ISL (emp)%S (EPar (EVal v) (EVal v')) (fun v0 => @[ v0 = VPair v v'])%S.
Proof.
  eauto using ISL_pure_step, ISL_val, pure_step.
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
  ISL P1 e1 (fun v => @[ v = v1 ] ∗ Q1 v)%S ->
  ISL P2 e2 (fun v => @[ v = v2 ] ∗ Q2 v)%S ->
  ISL (P1 ∗ P2)%S (EPar e1 e2) (fun v => @[ v = VPair v1 v2 ] ∗ Q1 v1 ∗ Q2 v2)%S.
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
  (ISLERR P e1 Q \/ ISLERR P e2 Q) ->
  ISLERR P (EPar e1 e2) Q.
Proof.
  intros [H | H].
  - apply ISLERR_context with (k := fun x => EPar x e2); [eauto with context | done].
  - apply ISLERR_context with (k := fun x => EPar e1 x); [eauto with context | done].
Qed.

Lemma ISL_par_l (P : iProp) (R Q : val -> iProp) e1 e2 e3 :
  ISL P e1 R ->
  (exists v, ISL (R v) (EPar e2 e3) Q) ->
  ISL P (EPar (ESeq e1 e2) e3) Q.
Proof.
  intros HPR [v HRQ].
  eapply ISL_context with (k := fun x => EPar (ESeq x e2) e3); [|done|].
  - apply Compose_ctx with (k1 := fun x => EPar x e3); eauto with context.
  - exists v. eapply ISL_pure_step_context with (k := fun x => EPar x e3);
    [eauto with context | done | constructor].
Qed.

Lemma ISL_par_l_err (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  ISL P e1 R ->
  (exists v, ISLERR (R v) (EPar e2 e3) Q) ->
  ISLERR P (EPar (ESeq e1 e2) e3) Q.
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
  ISL P e2 R ->
  (exists v, ISL (R v) (EPar e1 e3) Q) ->
  ISL P (EPar e1 (ESeq e2 e3)) Q.
Proof.
  intros HPR [v HRQ].
  eapply ISL_context with (k := fun x => EPar e1 (ESeq x e3)); [|done|].
  - apply Compose_ctx with (k1 := fun x => EPar e1 x); eauto with context.
  - exists v. eapply ISL_pure_step_context;
    [eauto with context | done | constructor].
Qed.

Lemma ISL_par_r_err (P Q : iProp) (R : val -> iProp) e1 e2 e3 :
  ISL P e2 R ->
  (exists v, ISLERR (R v) (EPar e1 e3) Q) ->
  ISLERR P (EPar e1 (ESeq e2 e3)) Q.
Proof.
  intros HPR [v HRQ].
  eapply ISLERR_context_ISL with (k := fun x => EPar e1 (ESeq x e3)).
  - eauto with context.
  - eapply ISL_cons; [apply iEntails_refl | | done].
    intros v'. apply iPure_elim. intros ->. apply iEntails_refl.
  - eapply ISLERR_pure_step_context; [|done|]; repeat constructor.
Qed.


(*
  1) Alloc, Load, Store, Free --> DONE
  2) Examples with Par rules
  3) Use proofmode.v for Iris tactics
  4) Write down in paper
    -> Operational semantics
    -> Contexts using K ::= O | load K | ..., same order as operational semantics
    -> Unsafe
    -> Triple definitions
    -> Rules
    -> Example (also after operational semantics, then show how to prove it unsafe here)
  5) CISL RD/DD
*)
