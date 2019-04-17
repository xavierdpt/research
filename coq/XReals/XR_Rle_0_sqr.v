Require Export XR_Rle.
Require Export XR_Rsqr.
Require Export XR_Rtotal_order.
Require Export XR_Ropp_involutive.
Require Export XR_Ropp_mult_distr_r.
Require Export XR_Rmult_lt_0_compat.
Require Export XR_Ropp_0.
Require Export XR_Ropp_lt_contravar.

Local Open Scope R_scope.

Lemma Rle_0_sqr : forall r, R0 <= Rsqr r.
Proof.
  intros x.
  unfold Rsqr.
  destruct (Rtotal_order x R0) as [ hx | [ heq | hx ] ].
  {
    rewrite <- Ropp_involutive with (x*x).
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_mult_distr_r.
    unfold "<=".
    left.
    apply Rmult_lt_0_compat.
    {
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      exact hx.
    }
    {
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      exact hx.
    }
  }
  {
    subst x.
    rewrite Rmult_0_l.
    unfold "<=".
    right.
    reflexivity.
  }
  {
    unfold "<=".
    left.
    apply Rmult_lt_0_compat.
    { exact hx. }
    { exact hx. }
  }
Qed.