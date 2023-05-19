From Coq Require Export Strings.String.
From Coq Require Import Program.Equality.
From iris.proofmode Require Import tactics.

Tactic Notation "inv" ident(H) "as" simple_intropattern(ipat) :=
  inversion H as ipat; clear H; simplify_eq.

Tactic Notation "inv" ident(H) :=
  inversion H; clear H; simplify_eq.

Inductive bin_op :=
  | PlusOp
  | MinusOp
  | LeOp
  | LtOp
  | EqOp.

Inductive val :=
  | VUnit : val
  | VBool : bool -> val
  | VNat : nat -> val
  | VRef : nat -> val
  | VPair : val -> val -> val
  | VLock : bool -> val.

Lemma val_eq_dec (v v' : val) :
  v = v' \/ v ≠ v'.
Proof.
  dependent induction v; destruct v'; eauto.
  1, 5: destruct b; destruct b0; eauto.
  1, 2: destruct (Nat.eq_dec n n0);
    try (left; by f_equal);
    right; intros Heq; simplify_eq.
  destruct (IHv1 v'1); destruct (IHv2 v'2); simplify_eq;
  try (by left); right; intros Heq; simplify_eq.
Qed.

Inductive expr :=
  | EVal : val -> expr
  | EAmb : expr
  | EVar : string -> expr
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | ELet : string -> expr -> expr -> expr
  | EOp : bin_op -> expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | EWhile : expr -> expr -> expr
  | ESeq : expr -> expr -> expr
  | EAlloc : expr -> expr
  | ELoad : expr -> expr
  | EStore : expr -> expr -> expr
  | EFree : expr -> expr
  | EPar : expr -> expr -> expr
  | ELock : expr -> expr
  | EUnlock : expr -> expr.

Fixpoint subst (x : string) (w : val) (e : expr) : expr :=
  match e with
  | EVal _ => e
  | EAmb => EAmb
  | EVar y => if string_dec y x then EVal w else EVar y
  | EPair e1 e2 => EPair (subst x w e1) (subst x w e2)
  | EFst e' => EFst (subst x w e')
  | ESnd e' => ESnd (subst x w e')
  | ELet y e1 e2 => if string_dec x y
     then ELet y (subst x w e1) e2
     else ELet y (subst x w e1) (subst x w e2)
  | EOp op e1 e2 => EOp op (subst x w e1) (subst x w e2)
  | EIf e1 e2 e3 => EIf (subst x w e1) (subst x w e2) (subst x w e3)
  | EWhile e1 e2 => EWhile (subst x w e1) (subst x w e2)
  | ESeq e1 e2 => ESeq (subst x w e1) (subst x w e2)
  | EAlloc e' => EAlloc (subst x w e')
  | ELoad e' => ELoad (subst x w e')
  | EStore e1 e2 => EStore (subst x w e1) (subst x w e2)
  | EFree e' => EFree (subst x w e')
  | EPar e1 e2 => EPar (subst x w e1) (subst x w e2)
  | ELock e => ELock (subst x w e)
  | EUnlock e => EUnlock (subst x w e)
  end.

Definition option_and (v1 v2 : option val) : option val :=
  match v1 with
  | Some (VBool b1) =>
      match v2 with
      | Some (VBool b2) => Some (VBool (andb b1 b2))
      | _ => None
      end
  | _ => None
  end.

Fixpoint eval_bin_op (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | PlusOp, VNat n1, VNat n2 => Some (VNat (n1 + n2))
  | MinusOp, VNat n1, VNat n2 => Some (VNat (n1 - n2))
  | LeOp, VNat n1, VNat n2 => Some (VBool (Nat.leb n1 n2))
  | LtOp, VNat n1, VNat n2 => Some (VBool (Nat.ltb n1 n2))
  | EqOp, VUnit, VUnit => Some (VBool true)
  | EqOp, VBool n1, VBool n2 => Some (VBool (Bool.eqb n1 n2))
  | EqOp, VNat n1, VNat n2 => Some (VBool (Nat.eqb n1 n2))
  | EqOp, VRef l1, VRef l2 => Some (VBool (Nat.eqb l1 l2))
  | EqOp, VPair p1 p2, VPair q1 q2 =>
      option_and (eval_bin_op EqOp p1 q1) (eval_bin_op EqOp p2 q2)
  | EqOp, VLock b1, VLock b2 => Some (VBool (Bool.eqb b1 b2))
  | _, _, _ => None
  end.

(* Small steps that don't alter the heap *)
Inductive pure_step : expr -> expr -> Prop :=
  | Amb_step n : pure_step EAmb (EVal (VNat n))
  | Pair_step v1 v2 :
      pure_step (EPair (EVal v1) (EVal v2)) (EVal (VPair v1 v2))
  | Fst_step v1 v2 :
      pure_step (EFst (EVal (VPair v1 v2))) (EVal v1)
  | Snd_step v1 v2 :
      pure_step (ESnd (EVal (VPair v1 v2))) (EVal v2)
  | Let_step y e v :
      pure_step (ELet y (EVal v) e) (subst y v e)
  | Op_step op v1 v2 v3 :
      eval_bin_op op v1 v2 = Some v3 ->
      pure_step (EOp op (EVal v1) (EVal v2)) (EVal v3)
  | If_true_step e1 e2 :
      pure_step (EIf (EVal (VBool true)) e1 e2) e1
  | If_false_step e1 e2 :
      pure_step (EIf (EVal (VBool false)) e1 e2) e2
  | While_step e1 e2 :
      pure_step (EWhile e1 e2) (EIf e1 (ESeq e2 (EWhile e1 e2)) (EVal VUnit))
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
  | Alloc_headstep h v l :
      valid_alloc h l →
      head_step (EAlloc (EVal v)) h (EVal (VRef l)) (<[ l := (Value v) ]> h)
  | Load_headstep h v l :
      h !! l = Some (Value v) →
      head_step (ELoad (EVal (VRef l))) h (EVal v) h
  | Store_headstep h v w l :
      h !! l = Some (Value w) →
      head_step (EStore (EVal (VRef l)) (EVal v)) h (EVal VUnit) (<[ l := (Value v) ]> h)
  | Free_headstep h v l :
      h !! l = Some (Value v) →
      head_step (EFree (EVal (VRef l))) h (EVal VUnit) (<[l := Reserved ]> h)
  | Lock_headstep h l :
      h !! l = Some (Value (VLock false)) →
      head_step (ELock (EVal (VRef l))) h (EVal VUnit) (<[ l := (Value (VLock true)) ]> h)
  | Unlock_headstep h l :
      h !! l = Some (Value (VLock true)) →
      head_step (EUnlock (EVal (VRef l))) h (EVal VUnit) (<[ l := (Value (VLock false)) ]> h).

Inductive ctx1 : (expr -> expr) -> Prop :=
  | Pair_l_ctx e : ctx1 (fun x => EPair x e)
  | Pair_r_ctx v : ctx1 (EPair (EVal v))
  | Fst_ctx : ctx1 EFst
  | Snd_ctx : ctx1 ESnd
  | Let_ctx y e : ctx1 (fun x => ELet y x e)
  | Op_l_ctx op e : ctx1 (fun x => EOp op x e)
  | Op_r_ctx op v : ctx1 (fun x => EOp op (EVal v) x)
  | If_ctx e1 e2 : ctx1 (fun x => EIf x e1 e2)
  | Seq_ctx e : ctx1 (fun x => ESeq x e)
  | Alloc_ctx : ctx1 EAlloc
  | Load_ctx : ctx1 ELoad
  | Store_l_ctx e : ctx1 (fun x => EStore x e)
  | Store_r_ctx v : ctx1 (EStore (EVal v))
  | Free_ctx : ctx1 EFree
  | Par_l_ctx e : ctx1 (fun x => EPar x e)
  | Par_r_ctx e : ctx1 (EPar e)
  | Lock_ctx : ctx1 ELock
  | Unlock_ctx : ctx1 EUnlock.

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

Ltac inv_ctx := repeat
  match goal with
  | H : ctx1 _ |- _ => inv H; try done
  | H : ctx _ |- _ => inv H; try done
  end.

Lemma context_EVal k e v :
  ctx k -> 
  k e = EVal v ->
  k = (fun x => x) /\ e = EVal v.
Proof.
  intros Hk. induction Hk; [done|].
  intros Hk12. inv H.
Qed.

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

Infix "###" := map_disjoint (at level 70).

Lemma step_heap_mono e m e' m' x :
  step e m e' m' → m' ### x → m ### x.
Proof.
  intros []?. destruct H; 
  inv H0; try assumption;
  rewrite map_disjoint_insert_l in H1;
  by destruct H1.
Qed.

Lemma steps_heap_mono e m e' m' x :
  steps e m e' m' → m' ### x -> m ### x.
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
  head_step e m e' m' <-> ∀ mf, m' ### mf -> head_step e (m ∪ mf) e' (m' ∪ mf).
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
  step e m e' m'  ↔ ∀ mf, m' ### mf -> step e (m ∪ mf) e' (m' ∪ mf).
Proof.
  split.
  - intros []. rewrite head_step_frame_equiv in H0.
    eauto using step.
  - intros. specialize (H _ (map_disjoint_empty_r _)).
    by rewrite !right_id_L in H.
Qed.

Lemma steps_frame_equiv e h e' h' :
  steps e h e' h' ↔ ∀ hf, h' ### hf → steps e (h ∪ hf) e' (h' ∪ hf).
Proof.
  split.
  - induction 1; eauto using steps.
    intros.
    assert (h2 ### hf). { eapply steps_heap_mono; eauto. }
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

Lemma not_is_val_ctx1 e k :
  ctx1 k -> ¬ is_val (k e).
Proof.
  intros Hctx Hnval.
  by inv Hctx.
Qed.

Lemma not_is_val_context e k :
  ctx k -> ¬ is_val e -> ¬ is_val (k e).
Proof.
  intros Hctx. generalize e. induction Hctx; intros e' Hnval;
  [done | destruct H; easy].
Qed.

Definition is_lock (e : expr) :=
  match e with
    | ELock _ => True
    | EUnlock _ => True
    | _ => False
  end.

Declare Scope S.
Delimit Scope S with S.

Definition iProp := heap → Prop.

Bind Scope S with iProp.

Definition iEntails (P Q : iProp) : Prop := ∀ m, P m → Q m.
Definition iEmp : iProp := λ m, m = ∅.
Definition iPoints (l : nat) (v : val) : iProp := λ m, m = {[ l := (Value v) ]}.
Definition iNegPoints (l : nat) : iProp := λ m, m = {[ l := Reserved ]}.
Definition iSep (P Q : iProp) : iProp := λ m, ∃ m1 m2, P m1 ∧ Q m2 ∧ m = m1 ∪ m2 ∧ m1 ### m2 .
Definition iWand (P Q : iProp) : iProp := λ m, ∀ m', m ### m' → P m' → Q (m' ∪ m).
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
