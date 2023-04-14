From Coq Require Export Strings.String.
From iris.proofmode Require Import tactics.
Require Import Lang.

Definition stuck (e : expr) (h : heap) :=
  ¬ is_val e /\ forall e' h', ¬ step e h e' h'.

Definition global_stuck (e : expr) (h : heap) := 
  exists e' h', steps e h e' h' /\ stuck e' h'.

