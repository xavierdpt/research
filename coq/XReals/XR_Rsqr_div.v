Require Import XR_Rsqr.
Require Import XR_Rdiv.
Require Import XR_R0.
Require Import XR_Rmult_assoc.
Require Import XR_Rmult_eq_compat_l.
Require Import XR_Rmult_eq_compat_r.
Require Import XR_Rinv_mult_distr.

Local Open Scope R_scope.

Lemma Rsqr_div : forall x y:R, y <> R0 -> Rsqr (x / y) = Rsqr x / Rsqr y.
Proof.
  intros x y h.
  unfold Rsqr.
  unfold Rdiv.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rinv_mult_distr.
  {
    repeat rewrite <- Rmult_assoc.
    apply Rmult_eq_compat_r.
    rewrite Rmult_comm.
    reflexivity.
  }
  { exact h. }
  { exact h. }
Qed.