Require Export XR_Rlt_irrefl.
Require Export XR_Rlt_trans.
Require Export XR_Rmult_lt_compat_l.
Require Export XR_Rtotal_order.

Local Open Scope R_scope.

Lemma Rmult_lt_reg_l : forall r r1 r2,
  R0 < r ->
  r * r1 < r * r2 ->
  r1 < r2.
Proof.
  intros x y z hx h.
  destruct (Rtotal_order y z) as [ hyz | [ heq | hzy ] ].
  { exact hyz. }
  {
    exfalso.
    subst z.
    apply Rlt_irrefl in h.
    contradiction.
  }
  {
    exfalso.
    apply Rlt_irrefl with (x*y).
    apply Rlt_trans with (x*z).
    { exact h. }
    {
      apply Rmult_lt_compat_l.
      { exact hx. }
      { exact hzy. }
    }
  }
Qed.


