Require Export XR_R0.
Require Export XR_Rminus.
Require Export XR_Rplus_0_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rminus_0_l : forall r, R0 - r = - r.
Proof.
  intro x.
  unfold Rminus.
  rewrite Rplus_0_l.
  reflexivity.
Qed.