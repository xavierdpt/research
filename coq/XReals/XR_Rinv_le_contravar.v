Require Export XR_Rle.
Require Export XR_Rinv_lt_contravar.
Require Export XR_Rmult_lt_0_compat.

Local Open Scope R_scope.

Lemma Rinv_le_contravar : forall x y,
  R0 < x ->
  x <= y ->
  / y <= / x.
Proof.
  intros x y hx hxy.
  unfold "<=" in hxy.
  destruct hxy as [ hxy | heq ].
  {
    unfold "<=".
    left.
    apply Rinv_lt_contravar.
    {
      apply Rmult_lt_0_compat.
      { exact hx. }
      {
        apply Rlt_trans with x.
        { exact hx. }
        { exact hxy. }
      }
    }
    { exact hxy. }
  }
  {
    subst y.
    unfold "<=".
    right.
    reflexivity.
  }
Qed.