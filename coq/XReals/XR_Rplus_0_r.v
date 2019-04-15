Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rplus.
Require Export XR_Rplus_0_l.
Require Export XR_Rplus_comm.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_0_r : forall r, r + R0 = r.
Proof.
  intro x.
  rewrite Rplus_comm.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
