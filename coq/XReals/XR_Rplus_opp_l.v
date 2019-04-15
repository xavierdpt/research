Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rplus.
Require Export XR_Rplus_comm.
Require Export XR_Ropp.
Require Export XR_Rplus_opp_r.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_opp_l : forall r, - r + r = R0.
Proof.
  intros x.
  rewrite Rplus_comm.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.
