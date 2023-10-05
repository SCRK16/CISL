From Coq Require Export Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Program.Equality.
From Coq Require Import Bool.DecBool.
From iris.proofmode Require Import tactics.
Require Export val.

Inductive base_event :=
  | Lock : nat -> base_event
  | Unlock : nat -> base_event
  | Join : base_event.

Inductive event :=
  | Base : base_event -> event
  | Left : event -> event
  | Right : event -> event.

Global Instance base_event_eq_dec : EqDecision base_event.
Proof. solve_decision. Defined.

Global Instance event_eq_dec : EqDecision event.
Proof. solve_decision. Defined.

Definition trace : Type := list event.

Inductive can_swap : event -> event -> Prop :=
  | left_right_swap e e' :
      can_swap (Left e) (Right e')
  | right_left_swap e e' :
      can_swap (Right e) (Left e')
  | left_left_swap e e' :
      can_swap e e' ->
      can_swap (Left e) (Left e')
  | right_right_swap e e' :
      can_swap e e' ->
      can_swap (Right e) (Right e').

Lemma can_swap_symm e e' :  
  can_swap e e' ->
  can_swap e' e.
Proof.
  intros Hswap.
  induction Hswap; 
  eauto using can_swap.
Qed.

Lemma can_swap_irreflexive e :
  ¬ can_swap e e.
Proof.
  intros Hswap.
  induction e; inv Hswap; eauto.
Qed.

Inductive perm1 : trace -> trace -> Prop :=
  | perm1_refl t :
      perm1 t t
  | perm1_skip x t t' :
      perm1 t t' ->
      perm1 (x :: t) (x :: t')
  | perm1_swap x y t :
      can_swap x y ->
      perm1 (x :: y :: t) (y :: x :: t).

Inductive perm : trace -> trace -> Prop :=
  | perm_single t t' :
      perm1 t t' ->
      perm t t'
  | perm_trans1 t t' t'' : 
      perm1 t t' ->
      perm t' t'' ->
      perm t t''.

Create HintDb perm.
Global Hint Resolve can_swap_symm can_swap_irreflexive : perm.
Global Hint Constructors perm1 perm : perm.

Lemma perm_trans t t' t'' :
  perm t t' ->
  perm t' t'' ->
  perm t t''.
Proof.
  intros Hperm Hperm'.
  induction Hperm;
  eauto with perm.
Qed.

Lemma perm1_symm t t' :
  perm1 t t' ->
  perm1 t' t.
Proof.
  intros Hperm.
  induction Hperm;
  eauto using perm1, can_swap_symm.
Qed.

Lemma perm_symm t t' :
  perm t t' ->
  perm t' t.
Proof.
  intros Hperm.
  induction Hperm.
  - eauto using perm1_symm with perm.
  - apply perm1_symm in H.
    eapply perm_trans; [done|].
    by eapply perm_single.
Qed.

Lemma perm1_nil_is_nil t :
  perm1 [] t ->
  t = [].
Proof.
  intros Hperm.
  by inv Hperm.
Qed.

Lemma perm_nil_is_nil t :
  perm [] t ->
  t = [].
Proof.
  intros Hperm.
  remember [] as t' in Hperm.
  induction Hperm.
  - rewrite Heqt' in H.
    by apply perm1_nil_is_nil.
  - simplify_eq.
    apply IHHperm.
    by apply perm1_nil_is_nil in H.
Qed.

Lemma perm1_singleton_is_singleton b t :
  perm1 [b] t ->
  t = [b].
Proof.
  intros Hperm.
  inv Hperm;
  by try rewrite (perm1_nil_is_nil _ H2).
Qed.

Lemma perm_singleton_is_singleton b t :
  perm [b] t ->
  t = [b].
Proof.
  intros Hperm.
  remember [b] as t' in Hperm.
  induction Hperm; simplify_eq.
  - by apply perm1_singleton_is_singleton.
  - apply IHHperm, (perm1_singleton_is_singleton _ _ H).
Qed.

Lemma perm1_app_nil t t' :
  perm1 t (t ++ t') ->
  t' = [].
Proof.
  intros Hperm. remember (t ++ t') as t0.
  induction Hperm.
  - rewrite <- app_nil_r in Heqt0 at 1.
    by eapply app_inv_head.
  - apply IHHperm.
    rewrite <- app_comm_cons in Heqt0.
    by simplify_eq.
  - do 2 rewrite <- app_comm_cons in Heqt0. simplify_eq.
    by apply can_swap_irreflexive in H.
Qed.

Lemma perm1_length t t' :
  perm1 t t' ->
  List.length t = List.length t'.
Proof.
  intros Hperm.
  induction Hperm; try done.
  simpl. by f_equal.
Qed.

Lemma perm_length t t' :
  perm t t' ->
  List.length t = List.length t'.
Proof.
  intros Hperm. induction Hperm; [by apply perm1_length|].
  rewrite <- IHHperm. by apply perm1_length.
Qed.

Lemma perm_app_nil t t' :
  perm t (t ++ t') ->
  t' = [].
Proof.
  intros Hperm.
  apply length_zero_iff_nil.
  apply perm_length in Hperm.
  rewrite app_length in Hperm.
  lia.
Qed.

Lemma perm_refl t :
  perm t t.
Proof. eauto 2 with perm. Qed.

Lemma perm_skip x t t' :
  perm t t' ->
  perm (x :: t) (x :: t').
Proof.
  intros Hperm.
  induction Hperm;
  eauto 3 with perm.
Qed.

Lemma perm_swap x y t t' :
  can_swap x y ->
  perm t t' ->
  perm (x :: y :: t) (y :: x :: t').
Proof.
  intros Hswap Hperm.
  induction Hperm;
  eauto 6 with perm.
Qed.

Global Hint Resolve perm_refl perm_skip perm_swap perm_symm : perm.

Lemma perm_can_swap_all a t t' :
  Forall (can_swap a) t ->
  perm (a :: t ++ t') (t ++ a :: t').
Proof.
  intros H.
  induction H; [apply perm_refl|].
  eapply perm_trans1.
  - by apply perm1_swap with (t := l ++ t').
  - simpl. apply perm_skip, IHForall.
Qed.

Lemma perm1_skip_or_swap a b a' b' t t' : 
  perm1 (a :: b :: t) (a' :: b' :: t') ->
  (a = a' /\ perm1 (b :: t) (b' :: t')) \/
  (a = b' /\ b = a' /\ t = t' /\ can_swap a b).
Proof.
  intros Hperm.
  inv Hperm; eauto with perm.
Qed.

Lemma perm1_inv a t t' :
  perm1 (a :: t) (a :: t') ->
  perm1 t t'.
Proof.
  intros Hperm.
  inv Hperm;
  by try apply perm1_refl.
Qed.

Section perm_inv.
(****
  This section is devoted to proving the lemma perm_inv:
  Lemma perm_inv a t t' : perm (a :: t) (a :: t') -> perm t t'.
  This is non-trivial, so we'll need multiple auxiliary definitions and lemmas
****)

  Inductive perm' : trace -> trace -> Prop :=
    | perm'_refl t : perm' t t
    | perm'_skip x t t' :
        perm' t t' ->
        perm' (x :: t) (x :: t')
    | perm'_swap x y t :
        can_swap x y ->
        perm' (x :: y :: t) (y :: x :: t)
    | perm'_trans t t' t'' :
        perm' t t' ->
        perm' t' t'' ->
        perm' t t''.

  Lemma perm1_perm' t t' :
    perm1 t t' -> perm' t t'.
  Proof.
    intros. induction H; eauto using perm'.
  Qed.

  Lemma perm_perm' t t' :
    perm t t' <-> perm' t t'.
  Proof.
    split; intros Hperm.
    - induction Hperm.
      + by apply perm1_perm'.
      + eapply perm'_trans; [|done].
        by apply perm1_perm'.
    - induction Hperm; eauto with perm.
      by eapply perm_trans.
  Qed.

  Lemma perm'_ind_bis (P : trace -> trace -> Prop) :
    (forall t, P t t) ->
    (forall x t t', perm' t t' -> P t t' -> P (x :: t) (x :: t')) ->
    (forall x y t t', can_swap x y ->
      perm' t t' -> P t t' -> P (y :: x :: t) (x :: y :: t')) ->
    (forall t t' t'', perm' t t' -> P t t' -> perm' t' t'' -> P t' t'' -> P t t'') ->
    forall t t', perm' t t' -> P t t'.
  Proof.
    intros Hrefl Hskip Hswap Htrans t t' Hperm.
    induction Hperm; eauto using can_swap_symm, perm'.
  Qed.

  Lemma perm_ind_bis (P : trace -> trace -> Prop) :
    (forall t, P t t) ->
    (forall x t t', perm t t' -> P t t' -> P (x :: t) (x :: t')) ->
    (forall x y t t', can_swap x y ->
      perm1 t t' -> P t t' -> P (y :: x :: t) (x :: y :: t')) ->
    (forall t t' t'', perm t t' -> P t t' -> perm t' t'' -> P t' t'' -> P t t'') ->
    forall t t', perm t t' -> P t t'.
  Proof.
    intros Hemp Hskip Hswap Htrans t t' Hperm.
    rewrite perm_perm' in Hperm. induction Hperm;
    eauto with perm.
    - apply Hskip; [|done].
      by rewrite perm_perm'.
    - eapply Htrans; by try rewrite perm_perm'.
  Qed.

  Inductive add : event -> trace -> trace -> Prop :=
    | add_head a t : add a t (a :: t)
    | add_cons a a' t t' :
        can_swap a a' ->
        add a t t' ->
        add a (a' :: t) (a' :: t').

  Lemma add_eq a t1 t2 t :
    add a t1 t ->
    add a t2 t ->
    t1 = t2.
  Proof.
    intros Hadd1. revert t2. induction Hadd1; intros t2 Hadd2.
    - inv Hadd2; [done|].
      by apply can_swap_irreflexive in H3.
    - inv Hadd2.
      + by apply can_swap_irreflexive in H.
      + by rewrite (IHHadd1 t0 H5).
  Qed.

  Lemma add_front x t t' :
    add x t (x :: t') ->
    t = t'.
  Proof.
    intros Hadd.
    inv Hadd; [done|].
    by apply can_swap_irreflexive in H3.
  Qed.

  Fixpoint in_front a t : Prop :=
    match t with
    | [] => False
    | (b :: t') => a = b \/ can_swap a b /\ in_front a t'
    end.

  Lemma in_add a t :
    in_front a t ->
    exists t', add a t' t.
  Proof.
    induction t; [done|].
    intros Hin.
    destruct Hin as [<- | [Hswap Hin]].
    - exists t. apply add_head.
    - destruct (IHt Hin) as [t' Hadd].
      exists (a0 :: t').
      by apply add_cons.
  Qed.

  Lemma add_in a t t' :
    add a t t' ->
    in_front a t'.
  Proof.
    intros Hadd.
    induction Hadd; simpl; tauto.
  Qed.

  Lemma perm_in a t t' :
    perm t t' ->
    in_front a t ->
    in_front a t'.
  Proof.
    revert t t'. refine (perm_ind_bis _ _ _ _ _); [done|..].
    - intros. destruct H1 as [<- | [Hswap Hin]]; simpl; tauto.
    - intros. destruct H2 as [<- | [Hswap Hin]].
      + simpl. apply can_swap_symm in H. tauto.
      + destruct Hin as [<- | [Hswap' Hin]]; simpl; tauto.
    - intros. tauto.
  Qed.

  Lemma perm_add a t t' t0 :
    perm t t' ->
    add a t0 t ->
    exists t0', add a t0' t'.
  Proof.
    intros Hperm Hadd.
    eauto using perm_in, in_add, add_in.
  Qed.

  Lemma perm_add_inv a t1 t2 :
    perm t1 t2 ->
    forall t1' t2',
      add a t1' t1 ->
      add a t2' t2 ->
      perm t1' t2'.
  Proof.
    revert t1 t2. refine (perm_ind_bis _ _ _ _ _).
    - intros t t1 t2 Hadd1 Hadd2.
      rewrite (add_eq _ _ _ _ Hadd1 Hadd2).
      apply perm_refl.
    - intros x t t' Hperm IH t1 t2 Hadd1 Hadd2.
      inv Hadd1; inv Hadd2; [done|..];
      try by apply can_swap_irreflexive in H3.
      eauto with perm.
    - intros x y t t' Hswap Hperm IH t1 t2 Hadd1 Hadd2.
      inv Hadd1; inv Hadd2; [|rewrite (add_front _ _ _ H4)..|];
      eauto with perm.
      inv H4; [by apply can_swap_irreflexive in H5|].
      inv H6; [by apply can_swap_irreflexive in H3|].
      apply perm_swap; [by apply can_swap_symm|].
      by apply IH.
    - intros t t' t'' Hperm IH Hperm' IH' t1 t2 Hadd1 Hadd2.
      assert (exists t3, add a t3 t') by by eapply perm_add.
      destruct H as [t3 Hadd3].
      eapply perm_trans; eauto.
  Qed.

  Lemma perm_inv a t t' :
    perm (a :: t) (a :: t') ->
    perm t t'.
  Proof.
    intros Hperm.
    eapply (perm_add_inv _ _ _ Hperm);
    apply add_head.
  Qed.

End perm_inv.

Lemma perm1_app_inv t t0 t1 :
  perm1 (t ++ t0) (t ++ t1) ->
  perm1 t0 t1.
Proof.
  intros Hperm.
  induction t; [auto|].
  eapply IHt, perm1_inv.
  by do 2 rewrite app_comm_cons.
Qed.

Lemma perm_app_inv t t0 t1 :
  perm (t ++ t0) (t ++ t1) ->
  perm t0 t1.
Proof.
  induction t; intros Hperm; [done|].
  apply IHt. by eapply perm_inv.
Qed.

Lemma perm1_app t0 t1 t :
  perm1 t0 t1 ->
  perm (t0 ++ t) (t1 ++ t).
Proof.
  intros Hperm.
  induction Hperm; eauto with perm.
Qed.

Lemma perm_app_single t0 t1 a :
  perm t0 t1 ->
  perm (t0 ++ [a]) (t1 ++ [a]).
Proof.
  intros Hperm.
  induction Hperm.
  - induction H; eauto with perm.
  - eapply perm_trans; eauto using perm1_app.
Qed.

Lemma perm_app t0 t1 t :
  perm t0 t1 ->
  perm (t0 ++ t) (t1 ++ t).
Proof.
  revert t0 t1. induction t as [ | a t IH ];
  intros t0 t1 Hperm.
  - by rewrite! app_nil_r.
  - rewrite !cons_middle !app_assoc.
    by apply IH, perm_app_single.
Qed.

Lemma perm_app_right t t0 t1 :
  perm t0 t1 ->
  perm (t ++ t0) (t ++ t1).
Proof.
  intros Hperm. induction t; [done|].
  by apply perm_skip.
Qed.

Lemma perm1_map_left {t t'} :
  perm1 t t' ->
  perm1 (map Left t) (map Left t').
Proof.
  intros Hperm.
  induction Hperm; simpl;
  eauto using can_swap with perm.
Qed.

Lemma perm_map_left {t t'} :
  perm t t' ->
  perm (map Left t) (map Left t').
Proof.
  intros Hperm.
  induction Hperm;
  eauto using perm1_map_left with perm.
Qed.

Lemma perm1_map_right {t t'} :
  perm1 t t' ->
  perm1 (map Right t) (map Right t').
Proof.
  intros Hperm.
  induction Hperm; simpl;
  eauto using can_swap with perm.
Qed.

Lemma perm_map_right {t t'} :
  perm t t' ->
  perm (map Right t) (map Right t').
Proof.
  intros Hperm.
  induction Hperm;
  eauto using perm1_map_right with perm.
Qed.

(**************************
    Language definition
**************************)

Notation lock_heap := (gmap nat bool).

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
  | EPar e1 e2 => EPar (subst x w e1) (subst x w e2)
  | ELock e => ELock (subst x w e)
  | EUnlock e => EUnlock (subst x w e)
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

Inductive head_step : expr -> lock_heap -> expr -> lock_heap -> Prop :=
  | do_pure_step e e' h :
      pure_step e e' ->
      head_step e h e' h
  | Lock_headstep h l :
      l ∉ dom (gset nat) h \/ h !! l = Some (false) ->
      head_step (ELock (EVal (VRef l))) h (EVal VUnit) (<[ l := true ]> h)
  | Unlock_headstep h l :
      h !! l = Some (true) ->
      head_step (EUnlock (EVal (VRef l))) h (EVal VUnit) (<[ l := false ]> h).

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
Global Hint Constructors ctx1 ctx : context.

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

Inductive step : expr -> lock_heap -> expr -> lock_heap -> Prop :=
  | do_step k e e' h h' :
      ctx k ->
      head_step e h e' h' ->
      step (k e) h (k e') h'.

Inductive steps : expr -> lock_heap -> expr -> lock_heap -> Prop :=
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
Global Hint Resolve step_once head_step_step : headstep.
Global Hint Constructors head_step pure_step : headstep.

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
  1: {
    intros. destruct H; rewrite -? insert_union_l; try by econstructor; eauto;
    try apply lookup_union_Some_l; eauto. constructor.
    rewrite elem_of_dom lookup_union_is_Some. rewrite elem_of_dom in H.
    rewrite map_disjoint_insert_l eq_None_not_Some in H0.
    destruct H as [Hnew | Hunlocked].
    - left. intros ?. tauto.
    - right. by rewrite lookup_union_l.
  }
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
