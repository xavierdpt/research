Require Export XR_Rplus_lt_le_0_compat.

Local Open Scope R_scope.

Lemma Rplus_le_le_0_compat : forall r1 r2, R0 <= r1 -> R0 <= r2 -> R0 <= r1 + r2.
Proof.
  intros x y.
  intros hx hy.
  unfold "<=" in hx.
  destruct hx as [ hx | heq ].
  {
    unfold "<=".
    left.
    apply Rplus_lt_le_0_compat.
    { exact hx. }
    { exact hy. }
  }
  {
    subst x.
    rewrite Rplus_0_l.
    exact hy.
  }
Qed.