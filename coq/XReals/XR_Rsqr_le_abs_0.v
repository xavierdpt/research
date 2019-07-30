Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rsqr.
Require Import XR_Rsqr_neg.
Require Import XR_Rsqr_incr_0_var.
Require Import XR_Ropp_0.
Require Import XR_Ropp_le_contravar.

Local Open Scope R_scope.

Lemma Rsqr_le_abs_0 : forall x y:R, Rsqr x <= Rsqr y -> Rabs x <= Rabs y.
Proof.
  intros x y h.
  unfold Rabs.
  destruct (Rcase_abs x) as [ hx | hx ] ;
  destruct (Rcase_abs y) as [ hy | hy ].
  {
    apply Rsqr_incr_0_var.
    {
      rewrite <- Rsqr_neg.
      rewrite <- Rsqr_neg.
      exact h.
    }
    {
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      left.
      exact hy.
    }
  }
  {
    apply Rsqr_incr_0_var.
    {
      rewrite <- Rsqr_neg.
      exact h.
    }
    { exact hy. }
  }
  {
  apply Rsqr_incr_0_var.
  {
    rewrite <- Rsqr_neg.
    exact h.
  }
  {
    rewrite <- Ropp_0.
    apply Ropp_le_contravar.
    left.
    exact hy.
  }
  }
  {
    apply Rsqr_incr_0_var.
    { exact h. }
    { exact hy. }
  }
Qed.