Require Export XR_Rlt_trans.
Require Export XR_Rplus_lt_compat_r.
Require Export XR_Rplus_lt_compat_l.

Local Open Scope R_scope.

Lemma Rplus_lt_compat : forall r1 r2 r3 r4,
  r1 < r2 ->
  r3 < r4 ->
  r1 + r3 < r2 + r4.
Proof.
  intros u v w x.
  intros huv hwx.
  apply Rlt_trans with (u+x).
  {
    apply Rplus_lt_compat_l.
    exact hwx.
  }
  {
    apply Rplus_lt_compat_r.
    exact huv.
  }
Qed.