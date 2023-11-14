From Coq Require Export Strings.String.
From Coq Require Export Lists.List.
From Coq Require Export Program.Equality.
From Coq Require Export Bool.DecBool.
From iris.proofmode Require Export tactics.
Require Export separation_logic.

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
