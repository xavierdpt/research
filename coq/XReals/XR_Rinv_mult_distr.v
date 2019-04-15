Require Export XR_Rinv_neq_0_compat.
Require Export XR_Rmult_1_r.
Require Export XR_Rmult_integral_contrapositive.

Local Open Scope R_scope.

Lemma Rinv_mult_distr : forall r1 r2,
  r1 <> R0 ->
  r2 <> R0 ->
  / (r1 * r2) = / r1 * / r2.
Proof.
  intros x y hx hy.
  apply Rmult_eq_reg_l with (x*y).
  {
    rewrite Rinv_r.
    {
      repeat rewrite Rmult_assoc.
      rewrite (Rmult_comm y).
      repeat rewrite Rmult_assoc.
      rewrite Rinv_l.
      {
        rewrite Rmult_1_r.
        rewrite Rinv_r.
        { reflexivity. }
        { exact hx. }
      }
      { exact hy. }
    }
    {
      apply Rmult_integral_contrapositive.
      split.
      { exact hx. }
      { exact hy. }
    }
  }
  {
    apply Rmult_integral_contrapositive.
    split.
    { exact hx. }
    { exact hy. }
  }
Qed.