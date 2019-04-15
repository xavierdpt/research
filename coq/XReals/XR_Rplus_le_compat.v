Require Export XR_Rle_trans.
Require Export XR_Rplus_le_compat_l.
Require Export XR_Rplus_le_compat_r.

Local Open Scope R_scope.

Lemma Rplus_le_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros u v w x.
  intros huv hwx.
  apply Rle_trans with (u+x).
  {
    apply Rplus_le_compat_l.
    exact hwx.
  }
  {
    apply Rplus_le_compat_r.
    exact huv.
  }
Qed.