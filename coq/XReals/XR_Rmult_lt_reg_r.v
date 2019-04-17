Require Export XR_Rmult_lt_reg_l.
Require Export XR_Rmult_comm.

Local Open Scope R_scope.

Lemma Rmult_lt_reg_r : forall r r1 r2,
  R0 < r ->
  r1 * r < r2 * r ->
  r1 < r2.
Proof.
  intros x y z hx hyz.
  apply Rmult_lt_reg_l with x.
  { exact hx. }
  {
    repeat rewrite (Rmult_comm x).
    exact hyz.
  }
Qed.
