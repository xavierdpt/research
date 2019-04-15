Require Export XR_Rinv_neq_0_compat.

Local Open Scope R_scope.

Lemma Rinv_involutive : forall r, r <> R0 -> / / r = r.
Proof.
  intros x hneq.
  apply Rmult_eq_reg_l with (/x).
  {
    rewrite Rinv_r.
    {
      rewrite Rinv_l.
      { reflexivity. }
      { exact hneq. }
    }
    {
      apply Rinv_neq_0_compat.
      exact hneq.
    }
  }
  {
    apply Rinv_neq_0_compat.
    exact hneq.
  }
Qed.