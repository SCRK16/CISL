Require Export permutation_theorems.

(************************************************
  Language definition: DLL (DeadLock Language)
    This is the language we want to study
    If it tries to do a lock/unlock instruction
    when that is impossible, it will get stuck
************************************************)

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
      l ∉ dom h \/ h !! l = Some (false) ->
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

Definition is_val (e : expr) :=
  match e with
    | EVal _ => True
    | _ => False
  end.

(********************
  stuck definition
********************)

Definition imm_stuck (e : expr) (h : lock_heap) :=
  ¬ is_val e /\ forall e' h', ¬ step e h e' h'.

Definition stuck (e : expr) (h : lock_heap) := 
  exists e' h', steps e h e' h' /\ imm_stuck e' h'.

(************************************************
  Language definition: HL (History Language)
    Language that builds up an execution trace
    instead of getting stuck when it tries to
    do an impossible lock/unlock instruction
************************************************)

Inductive pure_step_trace : expr -> expr -> option base_event -> Prop :=
  | Amb_step_trace n : pure_step_trace EAmb (EVal (VNat n)) None
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

Inductive ctxs_trace : (expr -> expr) -> Prop :=
  | Id_ctxs_trace : ctxs_trace (λ x, x)
  | Compose_ctxs_trace k1 k2 :
      ctx_trace k1 ->
      ctxs_trace k2 ->
      ctxs_trace (λ x, k1 (k2 x)).

(***********************************
  Definitions of concepts used in
  the definition of deadlock
***********************************)

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

Global Instance cell_eq_dec : EqDecision cell.
Proof. solve_decision. Defined.

Definition heap_locks (h : lock_heap) : gset nat :=
  dom (filter (λ lc, lc.2 = true) h).

(**********************
  Deadlock definition
**********************)

Definition deadlock (t : trace) : Prop :=
  ∃ (ph pt : trace),
      perm t (ph ++ pt) ∧
      valid ph ∧
      pt ≠ [] ∧
      set_Forall (is_locking (alocks ph)) (next_events pt).
