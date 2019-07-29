Require Import XR_Rsqr.
Require Import XR_Rminus.
Require Import XR_Rsqr_minus.
Require Import XR_Rplus_comm.
Require Import XR_Rmult_assoc.
Require Import XR_Rmult_comm.
Require Import XR_Rplus_eq_compat_r.


Local Open Scope R_scope.

Lemma Rsqr_neg_minus : forall x y:R, Rsqr (x - y) = Rsqr (y - x).
Proof.
  intros x y.
  repeat rewrite Rsqr_minus.
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm y).
  unfold Rminus.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  reflexivity.
Qed.