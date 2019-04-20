Require Export XR_Rminus.
Require Export XR_double_var.
Require Export XR_Rplus_eq_compat_l.
Require Export XR_Rmult_eq_compat_r.
Require Export XR_Rmult_lt_compat_r.
Require Export XR_Rinv_0_lt_compat.
Require Export XR_Rlt_R0_R2.
Require Export XR_Rle_lt_trans.

Local Open Scope R_scope.

Lemma le_epsilon : forall r1 r2,
  (forall eps:R,
    R0 < eps ->
    r1 <= r2 + eps
  ) ->
  r1 <= r2.
Proof.
  intros x y h.
  destruct (Rtotal_order x y) as [ hxy | [ heq | hyx ] ].
  {
    unfold "<=".
    left.
    exact hxy.
  }
  {
    unfold "<=".
    right.
    exact heq.
  }
  {
    exfalso.
    specialize (h ((x-y)/R2)).
    replace (y+(x-y)/R2) with ((y+x)/R2) in h.
    assert (hlt:R0 < (x-y)/R2).
    {
      unfold Rminus.
      unfold Rdiv.
      rewrite <- Rmult_0_l with (/R2).
      apply Rmult_lt_compat_r.
      {
        apply Rinv_0_lt_compat.
        exact Rlt_R0_R2.
      }
      {
        apply Rplus_lt_reg_r with y.
        rewrite Rplus_0_l.
        rewrite Rplus_assoc.
        rewrite Rplus_opp_l.
        rewrite Rplus_0_r.
        exact hyx.
      }
    }

    specialize (h hlt).
    clear hlt.

    eapply Rlt_irrefl.
    eapply Rle_lt_trans.
    { exact h. }
    {
      pattern x at 2 ; rewrite double_var.
      unfold Rdiv.
      rewrite Rmult_plus_distr_r.
      apply Rplus_lt_compat_r.
      apply Rmult_lt_compat_r.
      {
        apply Rinv_0_lt_compat.
        exact Rlt_R0_R2.
      }
      exact hyx.
    }
    {
      unfold Rminus.
      pattern y at 2 ; rewrite double_var.
      unfold Rdiv.
      rewrite <- Rmult_plus_distr_r.
      rewrite <- Rmult_plus_distr_r.
      apply Rmult_eq_compat_r.
      repeat rewrite Rplus_assoc.
      apply Rplus_eq_compat_l.
      rewrite (Rplus_comm y).
      rewrite Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_r.
      reflexivity.
    }
  }
Qed.