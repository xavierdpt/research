Require Import XR_Rsqr.
Require Import XR_Rmult_comm.
Require Import XR_Rmult_assoc.
Require Import XR_Rmult_eq_compat_l.
Require Import XR_Rmult_eq_compat_r.

Local Open Scope R_scope.

Lemma Rsqr_mult : forall x y:R, Rsqr (x * y) = Rsqr x * Rsqr y.
Proof.
  intros x y.
  unfold Rsqr.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  rewrite Rmult_comm.
  reflexivity.
Qed.