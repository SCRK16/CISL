Require Export permutation_definitions.

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
