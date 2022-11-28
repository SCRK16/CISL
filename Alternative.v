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
  | Par_r_ctx e : ctx (EPar e).

Definition cfg : Type := expr * heap.

Inductive step : expr -> heap -> expr -> heap -> Prop :=
  | do_head_step e e' h h' :
      head_step e h e' h' ->
      step e h e' h'
  | do_context_step k e e' h h' :
      ctx k ->
      step e h e' h' ->
      step (k e) h (k e') h'.

Inductive steps : expr -> heap -> expr -> heap -> Prop :=
  | steps_refl e h :
      steps e h e h
  | steps_step e1 h1 e2 h2 e3 h3 :
      step e1 h1 e2 h2 ->
      steps e2 h2 e3 h3 ->
      steps e1 h1 e3 h3.

Section Alt_ctx.

Inductive ctx_alt : (expr -> expr) -> Prop :=
  | Id_ctx_alt : ctx_alt (fun x => x)
  | Compose_ctx_alt k1 k2 : ctx_alt k1 -> ctx_alt k2 -> ctx_alt (fun x => k1 (k2 x))
  | Ctx_ctx_alt k : ctx k -> ctx_alt k.

Inductive step_alt : expr -> heap -> expr -> heap -> Prop :=
  | do_step_alt k e e' h h' :
      ctx_alt k ->
      head_step e h e' h' ->
      step_alt (k e) h (k e') h'.

Inductive step_alt' : expr -> heap -> expr -> heap -> Prop :=
  | do_step_alt' k e e' h h' :
      ctx_alt k ->
      step e h e' h' ->
      step_alt' (k e) h (k e') h'.

Lemma step_alt_equivalent e1 h1 e2 h2 :
  step_alt e1 h1 e2 h2 <-> step_alt' e1 h1 e2 h2.
Proof.
  split; intros Hstep.
  - inv Hstep. apply do_step_alt'; [done|].
    by apply do_head_step.
  - inv Hstep. revert H. revert k. induction H0; intros k' H'.
    + by apply do_step_alt.
    + apply (IHstep (fun x => k' (k x))).
      constructor; [done|].
      by apply Ctx_ctx_alt.
Qed.

Lemma step_equivalent e1 h1 e2 h2 :
  step e1 h1 e2 h2 <-> step_alt e1 h1 e2 h2.
Proof.
  split; intros Hstep.
  - induction Hstep.
    + apply (do_step_alt (fun x => x)); [|done].
      apply Id_ctx_alt.
    + inv IHHstep.
      apply (do_step_alt (fun x => k (k0 x))); [|done].
      apply Compose_ctx_alt; [|done].
      by apply Ctx_ctx_alt.
  - rewrite step_alt_equivalent in Hstep. inv Hstep.
    revert H0. revert e e'. induction H; intros e e' H'.
    + done.
    + by apply IHctx_alt1, IHctx_alt2.
    + by apply do_context_step.
Qed.

End Alt_ctx.

Lemma compose_context_step k1 k2 e1 h1 e2 h2 :
  ctx k1 -> ctx k2 ->
  step e1 h1 e2 h2 ->
  step (k1 (k2 e1)) h1 (k1 (k2 e2)) h2.
Proof.
  intros Hctx1 Hctx2 Hstep.
  apply do_context_step; [done|].
  by apply do_context_step.
Qed.

Lemma step_once e1 h1 e2 h2 :
  step e1 h1 e2 h2 ->
  steps e1 h1 e2 h2.
Proof.
  intros Hstep.
  eapply steps_step; [done|].
  apply steps_refl.
Qed.

Create HintDb headstep.
Global Hint Resolve step_once : headstep.
Global Hint Resolve do_head_step : headstep.
Global Hint Constructors head_step : headstep.
Global Hint Constructors pure_step : headstep.

Lemma step_heap_mono e m e' m' x :
  step e m e' m' → m' ##ₘ x → m ##ₘ x.
Proof.
  intros H0 H.
  induction H0.
  - inv H0; try done;
    rewrite map_disjoint_insert_l in H;
    by destruct H.
  - by apply IHstep.
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

Lemma steps_context_steps e e' h h' k :
  ctx k ->
  steps e h e' h' ->
  steps (k e) h (k e') h'.
Proof.
  intros Hctx Hsteps.
  induction Hsteps; [apply steps_refl |].
  apply steps_step with (k e2) h2; [|done].
  by apply do_context_step.
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
  - apply do_context_step; done.
  - by apply IHHsteps1.
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

Lemma is_val_em (e : expr) :
  is_val e \/ ¬ is_val e.
Proof.
  destruct e; [left |..]; try done; right; by intro.
Qed.

Lemma eventually_not_step e h :
  exists e' h', 
    steps e h e' h' /\
    forall e'' h'', ¬ step e' h' e'' h''.
Proof.
  revert h. induction e; intros h.
  1, 2: eexists _, h; split; try apply steps_refl; intros ?? Hstep; inv Hstep; [inv H | inv H0]; inv H0.
  - destruct (IHe1 h) as (e' & h' & Hsteps & Hnstep).
    destruct (IHe2 h') as (e'' & h'' & Hsteps' & Hnstep').
    destruct (is_val_em e') as [Hval | Hnval]; [destruct e'; try done; destruct (is_val_em e'') as [Hval' | Hnval']|].
    + destruct e''; try done. exists (EVal (VPair v v0)), h''. split.
      * eapply steps_trans; [eapply steps_context_steps with (k := fun x => EPair x e2)|]; [constructor | done |].
        eapply steps_trans; [eapply steps_context_steps|]; [constructor | done |].
        eauto with headstep.
      * intros ?? Hstep. inv Hstep.
        -- inv H. inv H0.
        -- inv H0.
    + exists (EPair (EVal v) e''), h''. split.
      * eapply steps_trans; [eapply steps_context_steps with (k := fun x => EPair x e2)|]; [constructor | done |].
        eapply steps_context_steps; [constructor | done].
      * intros e0 h0 Hstep0. inv Hstep0.
        -- inv H. inv H0. done.
        -- inv H0.
          ++ inv H1.
            ** inv H. inv H0.
            ** inv H0.
          ++ by eapply Hnstep'.
    + exists (EPair e' e2), h'. split.
      * apply steps_context_steps with (k := fun x => EPair x e2); [constructor |done].
      * intros e0 h0 Hstep0. inv Hstep0.
        -- inv H. inv H0. done.
        -- inv H0; [|done]. by eapply Hnstep.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma not_is_val_context e k :
  ctx k -> ¬ is_val e -> ¬ is_val (k e).
Proof.
  intros Hctx Hnval.
  destruct Hctx; easy.
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
  destruct (H h' HQ) as (e' & h & HP & Hsteps & [Hnval Hnsteps]).
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
  apply do_head_step, do_pure_step. constructor.
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

Lemma ctx_seq k e e1 e2 :
  ctx k ->
  k e = ESeq e1 e2 ->
  k = (fun x => ESeq x e2).
Proof.
  intros Hctx Hk.
  by inv Hctx.
Qed.

Lemma seq_step e1 e2 e' h h' :
  step (ESeq e1 e2) h e' h' ->
  (exists v, e1 = EVal v /\ e2 = e') \/ (exists e0, step e1 h e0 h' /\ e' = ESeq e0 e2).
Proof.
  intros Hstep. remember (ESeq e1 e2) as e.
  destruct Hstep; simplify_eq.
  - inv H. inv H0. left. by exists v.
  - assert (k = (fun x => ESeq x e2)) by (by eapply ctx_seq).
    subst. injection Heqe. intros He. subst.
    right. by exists e'.
Qed.

Lemma not_step_seq e1 e2 h :
  is_error e1 h ->
  is_error (ESeq e1 e2) h.
Proof.
  intros [Hnval Hnsteps].
  split; [easy|].
  intros e' h' Hstep.
  destruct (seq_step _ _ _ _ _ Hstep) as [[v [Hv He2]] | [e [Hstep1 ->]]]; subst.
  - apply Hnval. easy.
  - by eapply Hnsteps.
Qed.

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

Lemma ISL_par_err_and (P1 P2 Q1 Q2 : iProp) (e1 e2 : expr) :
  (ISLERR P1 e1 Q1 /\ ISLERR P2 e2 Q2) ->
  ISLERR (P1 ∗ P2)%S (EPar e1 e2) (Q1 ∗ Q2)%S.
Proof.
  intros [HISL1 HISL2] R h HQQR.
  (*destruct HQQR as (h0 & hr & (h1 & h2 & H1 & H2 & -> & Hdisj12) & Hr & -> & Hdisjr).*)
  destruct (HISL2 (Q1 ∗ R)%S h) as (e2r & h2r & HQPR & Hsteps2 & [Hnval2 Hnsteps2]).
  { apply iSep_assoc'. eapply iSep_mono_l; [apply iSep_comm | done]. }
  destruct (HISL1 (P2 ∗ R)%S h2r) as (e1r & h1r & HPPR & Hsteps1 & [Hnval1 Hnsteps1]).
  { apply iSep_assoc'. eapply iSep_mono_l; [apply iSep_comm|by apply iSep_assoc]. }
  exists (EPar e1r e2r), h1r. repeat split.
  - by apply iSep_assoc.
  - eapply steps_trans.
    + apply steps_context_steps with (k := fun x => EPar x e2); [constructor | done].
    + apply steps_context_steps; [constructor | done].
  - easy.
  - intros e' h' Hstep.
    inv Hstep.
    + inv H. inv H0. done.
    + inv H0.
        * admit.
        * by eapply Hnsteps2.
Admitted.

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
  *eapply steps_trans.
  {
    apply steps_context_steps with (k := fun x => EPar x e3); [constructor |].
    apply steps_context_steps with (k := fun x => ESeq x e2); [constructor | done].
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
    apply steps_context_steps with (k := fun x => EPar e1 x); [constructor|].
    apply steps_context_steps with (k := fun x => ESeq x e3); [constructor | done].
  }
  eapply steps_trans; [|done].
  eapply steps_context_steps; [constructor|].
  eauto with headstep.
Qed.




