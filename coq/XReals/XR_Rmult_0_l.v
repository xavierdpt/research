Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult.
Require Export XR_Rmult_comm.
Require Export XR_Rmult_0_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_0_l : forall r, R0 * r = R0.
Proof.
  intro x.
  rewrite Rmult_comm.
  rewrite Rmult_0_r.
  reflexivity.
Qed.
