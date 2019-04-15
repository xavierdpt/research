Require Export XR_Rminus.
Require Export XR_Rmult_plus_distr_l.
Require Export XR_Rplus_eq_compat_l.
Require Export XR_Ropp_mult_distr_r.

Local Open Scope R_scope.

Lemma Rmult_minus_distr_l : forall r1 r2 r3,
  r1 * (r2 - r3) = r1 * r2 - r1 * r3.
Proof.
  intros x y z.
  unfold Rminus.
  rewrite Rmult_plus_distr_l.
  apply Rplus_eq_compat_l.
  rewrite Ropp_mult_distr_r.
  reflexivity.
Qed.

