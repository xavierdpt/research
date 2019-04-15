Require Export XR_R.
Require Export XR_R1.
Require Export XR_Rmult.
Require Export XR_Rmult_comm.
Require Export XR_Rmult_1_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_1_r : forall r, r * R1 = r.
Proof.
  intro x.
  rewrite Rmult_comm.
  rewrite Rmult_1_l.
  reflexivity.
Qed.
