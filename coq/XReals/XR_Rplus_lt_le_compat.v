Require Export XR_Rle.
Require Export XR_Rplus_lt_compat.
Require Export XR_Rplus_lt_compat_r.

Local Open Scope R_scope.

Lemma Rplus_lt_le_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 <= r4 -> r1 + r3 < r2 + r4.
Proof.
  intros u v w x.
  intros huv hwx.
  unfold "<=" in hwx.
  destruct hwx as [ hwx | heq ].
  {
    apply Rplus_lt_compat.
    { exact huv. }
    { exact hwx. }
  }
  {
    subst w.
    apply Rplus_lt_compat_r.
    exact huv.
  }
Qed.

