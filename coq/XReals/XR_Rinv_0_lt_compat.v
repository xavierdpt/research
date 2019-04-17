Require Export XR_Rlt_0_1.
Require Export XR_Rmult_lt_reg_r.

Local Open Scope R_scope.

Lemma Rinv_0_lt_compat : forall r,
  R0 < r ->
  R0 < / r.
Proof.
  intros x h.
  apply Rmult_lt_reg_r with x.
  { exact h. }
  {
    rewrite Rmult_0_l.
    rewrite Rinv_l.
    { exact Rlt_0_1. }
    {
      apply not_eq_sym.
      apply Rlt_not_eq.
      exact h.
    }
  }
Qed.