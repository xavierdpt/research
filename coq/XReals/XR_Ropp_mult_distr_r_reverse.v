Require Export XR_Ropp_mult_distr_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_mult_distr_r_reverse : forall r1 r2, r1 * - r2 = - (r1 * r2).
Proof.
  intros x y.
  symmetry.
  apply Ropp_mult_distr_r.
Qed.
