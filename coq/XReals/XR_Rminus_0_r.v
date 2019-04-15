Require Export XR_R0.
Require Export XR_Rminus.
Require Export XR_Ropp_0.
Require Export XR_Rplus_0_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rminus_0_r : forall r, r - R0 = r.
Proof.
  intro x.
  unfold Rminus.
  rewrite Ropp_0.
  rewrite Rplus_0_r.
  reflexivity.
Qed.