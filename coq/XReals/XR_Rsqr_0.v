Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult_0_l.
Require Export XR_Rsqr.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rsqr_0 : Rsqr R0 = R0.
Proof.
  unfold Rsqr.
  rewrite Rmult_0_l.
  reflexivity.
Qed.
