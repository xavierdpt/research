Require Export XR_R.
Require Export XR_Ropp.
Require Export XR_Rplus_0_r.
Require Export XR_Rplus_opp_l.
Require Export XR_Rplus_opp_r.
Require Export XR_Rplus_eq_reg_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_plus_distr : forall r1 r2, - (r1 + r2) = - r1 + - r2.
Proof.
  intros x y.
  apply Rplus_eq_reg_r with (x+y).
  rewrite Rplus_opp_l.
  repeat rewrite Rplus_assoc.
  rewrite (Rplus_comm (-y)).
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  rewrite Rplus_opp_l.
  reflexivity.
Qed.