Require Export XR_Rmult_lt_0_compat.
Require Export XR_Rle.

Local Open Scope R_scope.

Lemma Rmult_le_pos : forall r1 r2,
  R0 <= r1 ->
  R0 <= r2 ->
  R0 <= r1 * r2.
Proof.
  intros x y hx hy.
  unfold "<=" in hx.
  destruct hx as [ hx | heq ].
  {
    unfold "<=" in hy.
    destruct hy as [ hy | heq ].
    {
      unfold "<=".
      left.
      apply Rmult_lt_0_compat.
      { exact hx. }
      { exact hy. }
    }
    {
      subst y.
      rewrite Rmult_0_r.
      unfold "<=".
      right.
      reflexivity.
    }
  }
  {
    subst x.
    rewrite Rmult_0_l.
    unfold "<=".
    right.
    reflexivity.
  }
Qed.

