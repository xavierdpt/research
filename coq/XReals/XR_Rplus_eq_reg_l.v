Require Export XR_R.
Require Export XR_Rplus.
Require Export XR_Rplus_assoc.
Require Export XR_Rplus_0_l.
Require Export XR_Rplus_opp_l.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_eq_reg_l : forall r r1 r2, r + r1 = r + r2 -> r1 = r2.
Proof.
  intros x y z.
  intro h.
  pattern y ; rewrite <- Rplus_0_l.
  rewrite <- Rplus_opp_l with x.
  pattern z ; rewrite <- Rplus_0_l.
  rewrite <- Rplus_opp_l with x.
  repeat rewrite Rplus_assoc.
  rewrite h.
  reflexivity.
Qed.

