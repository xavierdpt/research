Require Import XR_R.
Require Import XR_Rabs.
Require Import XR_Rabs_pos.
Require Import XR_Rabs_pos_eq.

Local Open Scope R_scope.

Lemma Rabs_Rabsolu : forall x:R, Rabs (Rabs x) = Rabs x.
Proof.
  intro x.
  apply Rabs_pos_eq.
  apply Rabs_pos.
Qed.
