Require Export XR_Rinv_0_lt_compat.
Require Export XR_Ropp_lt_cancel.
Require Export XR_Ropp_inv_permute.

Local Open Scope R_scope.

Lemma Rinv_lt_0_compat : forall r, r < R0 -> / r < R0.
Proof.
  intros x h.
  apply Ropp_lt_cancel.
  rewrite Ropp_0.
  rewrite Ropp_inv_permute.
  {
    apply Rinv_0_lt_compat.
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact h.
  }
  {
    apply Rlt_not_eq.
    exact h.
  }
Qed.