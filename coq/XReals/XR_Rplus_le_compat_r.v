Require Export XR_Rle.
Require Export XR_Rplus_lt_compat_r.

Local Open Scope R_scope.

Lemma Rplus_le_compat_r : forall r r1 r2, r1 <= r2 -> r1 + r <= r2 + r.
Proof.
  intros x y z.
  unfold "<=".
  intros [ hyz | heq ].
  {
    left.
    apply Rplus_lt_compat_r.
    exact hyz.
  }
  {
    subst z.
    right.
    reflexivity.
  }
Qed.