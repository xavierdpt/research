Require Export XR_Rmult_lt_compat_r.
Require Export XR_Rle_lt_trans.
Require Export XR_Rmult_0_l.

Local Open Scope R_scope.

Lemma Rmult_le_0_lt_compat : forall r1 r2 r3 r4,
  R0 <= r1 ->
  R0 <= r3 ->
  r1 < r2 ->
  r3 < r4 ->
  r1 * r3 < r2 * r4.
Proof.
  intros u v w x.
  intros hu hw huv hwx.
  unfold "<=" in hu.
  destruct hu as [ hu | heq ].
  {
    apply Rlt_trans with (u*x).
    {
      apply Rmult_lt_compat_l.
      { exact hu. }
      { exact hwx. }
    }
    {
      apply Rmult_lt_compat_r.
      {
        apply Rle_lt_trans with w.
        { exact hw. }
        { exact hwx. }
      }
      { exact huv. }
    }
  }
  {
    subst u.
    rewrite Rmult_0_l.
    rewrite <- Rmult_0_r with v.
    apply Rmult_lt_compat_l.
    { exact huv. }
    {
      apply Rle_lt_trans with w.
      { exact hw. }
      { exact hwx. }
    }
  }
Qed.
