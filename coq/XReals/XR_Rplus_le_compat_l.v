Require Export XR_Rle.
Require Export XR_Rplus_lt_compat_l.

Local Open Scope R_scope.

Lemma Rplus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
Proof.
intros x y z.
intros hyz.
unfold "<=" in hyz.
destruct hyz as [ hyz | heq ].
{
  unfold "<=".
  left.
  apply Rplus_lt_compat_l.
  exact hyz.
}
{
  subst z.
  unfold "<=".
  right.
  reflexivity.
}
Qed.
