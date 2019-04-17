Require Export XR_Rmult_lt_reg_r.
Require Export XR_Rmult_assoc.
Require Export XR_Rinv_l.
Require Export XR_Rlt_not_eq.
Require Export XR_Rmult_neq_0_reg.

Local Open Scope R_scope.

Lemma Rinv_lt_contravar : forall r1 r2,
  R0 < r1 * r2 ->
  r1 < r2 ->
  / r2 < / r1.
Proof.
  intros x y h hxy.
  apply Rmult_lt_reg_r with (x*y).
  { exact h. }
  {
    apply Rlt_not_eq in h.
    apply not_eq_sym in h.
    apply Rmult_neq_0_reg in h.
    destruct h as [ hx hy ].
    pattern (x*y) at 1 ; rewrite (Rmult_comm x).
    repeat rewrite <- Rmult_assoc.
    rewrite Rinv_l.
    {
      rewrite Rinv_l.
      {
        rewrite Rmult_1_l.
        rewrite Rmult_1_l.
        exact hxy.
      }
      { exact hx. }
    }
    { exact hy. }
  }
Qed.