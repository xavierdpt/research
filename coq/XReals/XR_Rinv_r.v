Require Export XR_R.
Require Export XR_R0.
Require Export XR_R1.
Require Export XR_Rmult.
Require Export XR_Rmult_comm.
Require Export XR_Rinv.
Require Export XR_Rinv_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rinv_r : forall r, r <> R0 -> r * / r = R1.
Proof.
  intros x h.
  rewrite Rmult_comm.
  rewrite Rinv_l.
  { reflexivity. }
  { exact h. }
Qed.
