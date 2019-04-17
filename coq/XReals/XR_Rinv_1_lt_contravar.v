Require Export XR_Rlt_0_1.
Require Export XR_Rlt_le_trans.
Require Export XR_Rinv_lt_contravar.

Local Open Scope R_scope.

Lemma Rinv_1_lt_contravar : forall r1 r2,
  R1 <= r1 ->
  r1 < r2 ->
  / r2 < / r1.
Proof.
  intros x y hx hxy.
  apply Rinv_lt_contravar.
  {
    apply Rmult_lt_0_compat.
    {
      apply Rlt_le_trans with R1.
      { exact Rlt_0_1. }
      { exact hx. }
    }
    {
      apply Rlt_trans with x.
      {
        apply Rlt_le_trans with R1.
        { exact Rlt_0_1. }
        { exact hx. }
      }
      { exact hxy. }
    }
  }
  { exact hxy. }
Qed.