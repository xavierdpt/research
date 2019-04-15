Require Export XR_R.
Require Export XR_Rle.
Require Export XR_Rlt_trans.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_lt_trans : forall r1 r2 r3, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros x y z.
  intros hxy hyz.
  unfold "<=" in hxy.
  destruct hxy as [ hxy | heq ].
  {
    apply Rlt_trans with y.
    { exact hxy. }
    { exact hyz. }
  }
  {
    subst y.
    exact hyz.
  }
Qed.
