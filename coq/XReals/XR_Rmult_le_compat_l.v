Require Export XR_Rle.
Require Export XR_Rmult_0_l.
Require Export XR_Rmult_lt_compat_l.

Local Open Scope R_scope.

Lemma Rmult_le_compat_l : forall r r1 r2,
  R0 <= r ->
  r1 <= r2 ->
  r * r1 <= r * r2.
Proof.
  intros x y z.
  intros hx hyz.
  unfold "<=" in hx.
  destruct hx as [ hx | heq ].
  {
    unfold "<=" in hyz.
    destruct hyz as [ hyz | heq ].
    {
      unfold "<=".
      left.
      apply Rmult_lt_compat_l.
      { exact hx. }
      { exact hyz. }
    }
    {
      subst z.
      unfold "<=".
      right.
      reflexivity.
    }
  }
  {
    subst x.
    rewrite Rmult_0_l.
    rewrite Rmult_0_l.
    unfold "<=".
    right.
    reflexivity.
  }
Qed.

