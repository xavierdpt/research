Require Export XR_Rle.
Require Export XR_Rplus_lt_0_compat.
Require Export XR_Rplus_0_r.

Local Open Scope R_scope.

Lemma Rplus_lt_le_0_compat : forall r1 r2, R0 < r1 -> R0 <= r2 -> R0 < r1 + r2.
Proof.
  intros x y.
  intros hx hy.
  unfold "<=" in hy.
  destruct hy as [ hy | heq ].
  {
    apply Rplus_lt_0_compat.
    { exact hx. }
    { exact hy. }
  }
  {
    subst y.
    rewrite Rplus_0_r.
    exact hx.
  }
Qed.