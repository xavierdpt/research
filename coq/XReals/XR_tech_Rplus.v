Require Export XR_Rle.
Require Export XR_Rlt_irrefl.
Require Export XR_Rlt_trans.
Require Export XR_Rlt_not_eq.
Require Export XR_Rplus_lt_reg_r.
Require Export XR_Rminus_diag_uniq.

Local Open Scope R_scope.

Lemma tech_Rplus : forall r s,
  R0 <= r ->
  R0 < s ->
  r + s <> R0.
Proof.
  intros x y hx hy.
  unfold "<=" in hx.
  destruct hx as [ hx | heq ].
  {
    unfold not.
    intro heq.
    apply Rlt_irrefl with R0.
    apply Rlt_trans with x.
    { exact hx. }
    {
      apply Rplus_lt_reg_r with y.
      rewrite heq.
      rewrite Rplus_0_l.
      exact hy.
    }
  }
  {
    subst x.
    rewrite Rplus_0_l.
    apply not_eq_sym.
    apply Rlt_not_eq.
    exact hy.
  }
Qed.