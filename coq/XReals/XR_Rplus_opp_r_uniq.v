Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rplus.
Require Export XR_Rplus_assoc.
Require Export XR_Ropp.
Require Export XR_Rplus_0_l.
Require Export XR_Rplus_0_r.
Require Export XR_Rplus_opp_l.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_opp_r_uniq : forall r1 r2, r1 + r2 = R0 -> r2 = - r1.
Proof.
  intros x y h.
  pattern y ; rewrite <- Rplus_0_l.
  rewrite <- Rplus_opp_l with x.
  rewrite Rplus_assoc.
  rewrite h. clear h.
  rewrite Rplus_0_r.
  reflexivity.
Qed.
