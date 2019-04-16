Require Export XR_Rle.
Require Export XR_Ropp_lt_contravar.

Local Open Scope R_scope.

Lemma Ropp_le_contravar : forall r1 r2,
  r2 <= r1 ->
  - r1 <= - r2.
Proof.
  intros x y hyx.
  unfold "<=" in hyx.
  destruct hyx as [ hyx | heq ].
  {
    unfold "<=".
    left.
    apply Ropp_lt_contravar.
    exact hyx.
  }
  {
    subst y.
    unfold "<=".
    right.
    reflexivity.
  }
Qed.