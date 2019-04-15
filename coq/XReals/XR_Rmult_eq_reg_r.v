Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult.
Require Export XR_Rmult_comm.
Require Export XR_Rmult_eq_reg_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_eq_reg_r : forall r r1 r2, r1 * r = r2 * r -> r <> R0 -> r1 = r2.
Proof.
  intros x y z heq hneq.
  apply Rmult_eq_reg_l with x.
  {
    repeat rewrite (Rmult_comm x).
    exact heq.
  }
  { exact hneq. }
Qed.
