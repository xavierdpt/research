Require Export XR_R.
Require Export XR_Rmult.
Require Export XR_Ropp.
Require Export XR_Ropp_mult_distr_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_mult_distr_l_reverse : forall r1 r2, - r1 * r2 = - (r1 * r2).
Proof.
  intros x y.
  symmetry.
  apply Ropp_mult_distr_l.
Qed.