Require Export XR_Rminus.
Require Export XR_Rplus_assoc.
Require Export XR_Rplus_comm.
Require Export XR_Rplus_opp_r.
Require Export XR_Rplus_0_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rplus_minus : forall r1 r2, r1 + (r2 - r1) = r2.
Proof.
  intros x y.
  unfold Rminus.
  rewrite (Rplus_comm y).
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
