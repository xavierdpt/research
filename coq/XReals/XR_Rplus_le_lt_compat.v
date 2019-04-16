Require Export XR_Rle.
Require Export XR_Rplus_lt_compat.

Local Open Scope R_scope.

Lemma Rplus_le_lt_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros u v w x.
  intros huv hwx.
  unfold "<=" in huv.
  destruct huv as [ huv | heq ].
  {
    apply Rplus_lt_compat.
    { exact huv. }
    { exact hwx. }
  }
  {
    subst v.
    apply Rplus_lt_compat_l.
    exact hwx.
  }
Qed.
