Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult.
Require Export XR_Rmult_0_r.
Require Export XR_Rmult_eq_reg_l.
Require Export XR_Rtotal_order.
Require Export XR_Rlt_not_eq.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_integral : forall r1 r2, r1 * r2 = R0 -> r1 = R0 \/ r2 = R0.
Proof.
intros x y.
intro heq.
destruct (Rtotal_order x R0) as [ hxneg | [ hxeq | hxpos ] ].
{
  right.
  apply Rmult_eq_reg_l with x.
  {
    rewrite Rmult_0_r.
    exact heq.
  }
  {
    apply Rlt_not_eq.
    exact hxneg.
  }
}
{
  left.
  exact hxeq.
}
{
  right.
  apply Rmult_eq_reg_l with x.
  {
    rewrite Rmult_0_r.
    exact heq.
  }
  {
    apply not_eq_sym.
    apply Rlt_not_eq.
    exact hxpos.
  }
}
Qed.
