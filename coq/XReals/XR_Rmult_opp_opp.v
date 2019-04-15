Require Export XR_R.
Require Export XR_Rmult.
Require Export XR_Rmult_0_r.
Require Export XR_Ropp.
Require Export XR_Ropp_involutive.
Require Export XR_Ropp_mult_distr_l.
Require Export XR_Rplus_eq_reg_r.
Require Export XR_Rplus_opp_r.
Require Export XR_Rmult_plus_distr_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_opp_opp : forall r1 r2, - r1 * - r2 = r1 * r2.
Proof.
  intros x y.
  apply Rplus_eq_reg_r with (-(-x*-y)).
  rewrite Rplus_opp_r.
  rewrite Ropp_mult_distr_l.
  rewrite Ropp_involutive.
  rewrite <- Rmult_plus_distr_l.
  rewrite Rplus_opp_r.
  rewrite Rmult_0_r.
  reflexivity.
Qed.
