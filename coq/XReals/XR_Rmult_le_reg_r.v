Require Export XR_Rmult_comm.
Require Export XR_Rmult_le_reg_l.

Local Open Scope R_scope.

Lemma Rmult_le_reg_r : forall r r1 r2,
  R0 < r ->
  r1 * r <= r2 * r ->
  r1 <= r2.
Proof.
  intros x y z hx h.
  apply Rmult_le_reg_l with x.
  { exact hx. }
  {
    repeat rewrite (Rmult_comm x).
    exact h.
  }
Qed.
