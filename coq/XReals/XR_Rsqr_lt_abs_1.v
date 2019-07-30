Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rsqr.
Require Import XR_Ropp_lt_cancel.
Require Import XR_Rmult_le_0_lt_compat.
Require Import XR_Ropp_mult_distr_l.
Require Import XR_Ropp_mult_distr_r.
Require Import XR_Ropp_0.

Local Open Scope R_scope.

Lemma Rsqr_lt_abs_1 : forall x y:R, Rabs x < Rabs y -> Rsqr x < Rsqr y.
Proof.
  intros x y h.
  unfold Rabs in h.
  unfold Rsqr.
  destruct (Rcase_abs x) as [ hx | hx ] ;
  destruct (Rcase_abs y) as [ hy | hy ].
  {
  apply Ropp_lt_cancel.
  repeat rewrite Ropp_mult_distr_l.
  apply Ropp_lt_cancel.
  repeat rewrite Ropp_mult_distr_r.
  apply Rmult_le_0_lt_compat.
  {
    left.
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact hx.
  }
  {
    left.
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact hx.
  }
  { exact h. }
  { exact h. }
  }
  {
  rewrite <- (Ropp_involutive (x*x)).
  rewrite Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_r.
  apply Rmult_le_0_lt_compat.
  {
    left.
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact hx.
  }
  {
    left.
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact hx.
  }
  { exact h. }
  { exact h. }
}
{
  rewrite <- (Ropp_involutive (y*y)).
  rewrite Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_r.
  apply Rmult_le_0_lt_compat.
  { exact hx. }
  { exact hx. }
  { exact h. }
  { exact h. }
}
{
  apply Rmult_le_0_lt_compat.
  { exact hx. }
  { exact hx. }
  { exact h. }
  { exact h. }
}
Qed.