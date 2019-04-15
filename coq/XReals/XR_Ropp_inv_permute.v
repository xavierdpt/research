Require Export XR_Rmult_eq_reg_l.
Require Export XR_Rinv_r.
Require Export XR_Ropp_mult_distr_r.
Require Export XR_Ropp_involutive.
Require Export XR_Ropp_eq_0_compat.

Local Open Scope R_scope.

Lemma Ropp_inv_permute : forall r, r <> R0 -> - / r = / - r.
Proof.
  intros x h.
  apply Rmult_eq_reg_l with (-x).
  {
    rewrite Rinv_r.
    {
      rewrite <- Ropp_mult_distr_l.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_involutive.
      rewrite Rinv_r.
      { reflexivity. }
      { exact h. }
    }
    {
      unfold not.
      intro heq.
      unfold not in h.
      apply h.
      apply Ropp_eq_0_compat in heq.
      rewrite Ropp_involutive in heq.
      exact heq.
    }
  }
  {
    unfold not.
    intro heq.
    unfold not in h.
    apply h.
    apply Ropp_eq_0_compat in heq.
    rewrite Ropp_involutive in heq.
    exact heq.
  }
Qed.