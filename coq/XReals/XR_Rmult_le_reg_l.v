Require Export XR_Rle.
Require Export XR_Rlt_not_eq.
Require Export XR_Rmult_lt_reg_l.
Require Export XR_Rmult_eq_reg_l.

Local Open Scope R_scope.

Lemma Rmult_le_reg_l : forall r r1 r2,
  R0 < r ->
  r * r1 <= r * r2 ->
  r1 <= r2.
Proof.
  intros x y z hx h.
  unfold "<=" in h.
  destruct h as [ h | heq ].
  {
    unfold "<=".
    left.
    apply Rmult_lt_reg_l with x.
    { exact hx. }
    { exact h. }
  }
  {
    unfold "<=".
    right.
    apply Rmult_eq_reg_l with x.
    { exact heq. }
    {
      apply not_eq_sym.
      apply Rlt_not_eq.
      exact hx.
    }
  }
Qed.