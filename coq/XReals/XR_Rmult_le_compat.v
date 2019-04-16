Require Export XR_Rle_trans.
Require Export XR_Rmult_le_compat_l.
Require Export XR_Rmult_le_compat_r.

Local Open Scope R_scope.

Lemma Rmult_le_compat : forall r1 r2 r3 r4,
  R0 <= r1 ->
  R0 <= r3 ->
  r1 <= r2 ->
  r3 <= r4 ->
  r1 * r3 <= r2 * r4.
Proof.
  intros u v w x.
  intros hu hw huv hwx.
  apply Rle_trans with (v*w).
  {
    apply Rmult_le_compat_r.
    { exact hw. }
    { exact huv. }
  }
  {
    apply Rmult_le_compat_l.
    {
      apply Rle_trans with u.
      { exact hu. }
      { exact huv. }
    }
    { exact hwx. }
  }
Qed.