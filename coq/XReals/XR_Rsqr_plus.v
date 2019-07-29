Require Import XR_Rsqr.
Require Import XR_Rplus_eq_compat_l.
Require Import XR_Rplus_eq_compat_r.
Require Import XR_Rplus_assoc.
Require Import XR_Rplus_comm.
Require Import XR_Rmult_assoc.
Require Import XR_double.

Local Open Scope R_scope.

Lemma Rsqr_plus : forall x y:R, Rsqr (x + y) = Rsqr x + Rsqr y + R2 * x * y.
Proof.
  intros x y.
  unfold Rsqr.
  rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  rewrite (Rplus_comm (y*y)).
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite (Rmult_comm y).
  rewrite <- double.
  repeat rewrite <- Rmult_assoc.
  reflexivity.
Qed.