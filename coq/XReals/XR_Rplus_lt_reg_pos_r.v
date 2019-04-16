Require Export XR_Rplus_0_r.
Require Export XR_Rle_lt_trans.
Require Export XR_Rplus_le_compat_l.

Local Open Scope R_scope.

Lemma Rplus_lt_reg_pos_r : forall r1 r2 r3,
  R0 <= r2 ->
  r1 + r2 < r3 ->
  r1 < r3.
Proof.
  intros x y z.
  intros hy h.
  apply Rle_lt_trans with (x+y).
  {
    pattern x at 1;rewrite <- Rplus_0_r.
    apply Rplus_le_compat_l.
    exact hy.
  }
  { exact h. }
Qed.
