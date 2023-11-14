From Coq Require Export Strings.String.
From iris.proofmode Require Export tactics.
Require Export separation_logic.

(* Language definition *)

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

Inductive head_step : expr -> heap -> expr -> heap -> Prop :=
  | do_pure_step e e' h :
      pure_step e e' ->
      head_step e h e' h
  | Alloc_headstep h v l :
      valid_alloc h l ->
      head_step (EAlloc (EVal v)) h (EVal (VRef l)) (<[ l := (Value v) ]> h)
  | Load_headstep h v l :
      h !! l = Some (Value v) ->
      head_step (ELoad (EVal (VRef l))) h (EVal v) h
  | Store_headstep h v w l :
      h !! l = Some (Value w) ->
      head_step (EStore (EVal (VRef l)) (EVal v)) h (EVal VUnit) (<[ l := (Value v) ]> h)
  | Free_headstep h v l :
      h !! l = Some (Value v) ->
      head_step (EFree (EVal (VRef l))) h (EVal VUnit) (<[l := Reserved ]> h)
  | Lock_headstep h l :
      h !! l = Some (Value (VLock false)) ->
      head_step (ELock (EVal (VRef l))) h (EVal VUnit) (<[ l := (Value (VLock true)) ]> h)
  | Unlock_headstep h l :
      h !! l = Some (Value (VLock true)) ->
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

Definition is_val (e : expr) :=
  match e with
    | EVal _ => True
    | _ => False
  end.

Definition is_lock (e : expr) :=
  match e with
    | ELock _ => True
    | EUnlock _ => True
    | _ => False
  end.

(* Error *)

Definition imm_unsafe (e : expr) (h : heap) :=
  ¬ is_val e /\ ¬ is_lock e /\ forall e' h', ¬ step e h e' h'.

Definition is_error (e : expr) (h : heap) :=
  exists k e', ctx k /\ e = k e' /\ imm_unsafe e' h.

(* CISL triples *)

Definition IL (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  forall v h', Q v h' -> exists h, P h /\ steps e h (EVal v) h'.

Definition ILERR (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall h', Q h' -> exists e' h, P h /\ steps e h e' h' /\ is_error e' h'.

Definition ISL (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  forall R, IL (P ∗ R)%S e (fun v => Q v ∗ R)%S.

Definition ISLERR (P : iProp) (e : expr) (Q : iProp) : Prop :=
  forall R, ILERR (P ∗ R)%S e (Q ∗ R)%S.

Definition is_error_or_val (e : expr) (h : heap) (mv : option val) : Prop :=
  match mv with
  | Some v => e = EVal v
  | None => is_error e h
  end.

Definition IL_Gen (P : iProp) (e : expr) (Q : option val -> iProp) : Prop :=
  forall mv h', Q mv h' -> exists e' h, P h /\ steps e h e' h' /\ is_error_or_val e' h' mv.

Definition ISL_Gen (P : iProp) (e : expr) (Q : option val -> iProp) : Prop :=
  forall R, IL_Gen (P ∗ R)%S e (fun mv => Q mv ∗ R)%S.

Definition to_option_some (Q : val -> iProp) : option val -> iProp :=
  fun mv => match mv with
  | Some v => Q v
  | None => (@[False])%S
  end.

Definition to_option_none (Q : iProp) : option val -> iProp :=
  fun mv => match mv with
  | Some v => (@[False])%S
  | None => Q
  end.

Definition from_option_some (Q : option val -> iProp) : val -> iProp :=
  fun v => Q (Some v).

Definition from_option_none (Q : option val -> iProp) : iProp :=
  Q None.

Definition ISL' (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  ISL_Gen P e (to_option_some Q).

Definition ISLERR' (P : iProp) (e : expr) (Q : iProp) : Prop :=
  ISL_Gen P e (to_option_none Q).

Notation "[[[ P ]]] e [[[ v , Q ]]]" := (ISL P%S e (λ v , Q%S))
    (at level 20, e, P at level 200, Q at level 200, only parsing).
Notation "[[[ P ]]] e [[[ Q ]]]" := (ISL P%S e Q%S)
    (at level 20, e, P at level 200, Q at level 200, only parsing).
Notation "[[[ P ]]] e [[[ERR: Q ]]]" := (ISLERR P%S e Q%S)
  (at level 20, e, P at level 200, Q at level 200, only parsing).
