Require Export XR_R0.
Require Export XR_Rminus.
Require Export XR_Rplus_0_l.
Require Export XR_Ropp_plus_distr.
Require Export XR_Ropp_involutive.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_minus_distr : forall r1 r2, - (r1 - r2) = r2 - r1.
Proof.
  intros x y.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite Rplus_comm.
  reflexivity.
Qed.
