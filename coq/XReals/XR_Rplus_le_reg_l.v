Require Export XR_Rle.
Require Export XR_Rplus_lt_reg_l.
Require Export XR_Rplus_eq_reg_l.

Local Open Scope R_scope.

Lemma Rplus_le_reg_l : forall r r1 r2, r + r1 <= r + r2 -> r1 <= r2.
Proof.
  intros x y z h.
  unfold "<=" in h.
  destruct h as [ h | heq ].
  {
    unfold "<=".
    left.
    apply Rplus_lt_reg_l with x.
    exact h.
  }
  {
    unfold "<=".
    right.
    apply Rplus_eq_reg_l with x.
    exact heq.
  }
Qed.
