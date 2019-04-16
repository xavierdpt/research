Require Export XR_Rplus_assoc.
Require Export XR_Rplus_0_l.
Require Export XR_Rplus_opp_l.
Require Export XR_Rplus_lt_compat_l.

Local Open Scope R_scope.

Lemma Rplus_lt_reg_l : forall r r1 r2, r + r1 < r + r2 -> r1 < r2.
Proof.
  intros x y z.
  intro h.
  pattern y ; rewrite <- Rplus_0_l.
  pattern z ; rewrite <- Rplus_0_l.
  rewrite <- Rplus_opp_l with x.
  repeat rewrite Rplus_assoc.
  apply Rplus_lt_compat_l.
  exact h.
Qed.
