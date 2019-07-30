Require Import XR_R.
Require Import XR_Rsqr.
Require Import XR_Rminus.
Require Import XR_Rmult_comm.
Require Import XR_Rsqr_minus_plus.

Local Open Scope R_scope.

Lemma Rsqr_plus_minus : forall a b:R, (a + b) * (a - b) = Rsqr a - Rsqr b.
Proof.
  intros x y.
  rewrite Rmult_comm.
  apply Rsqr_minus_plus.
Qed.
