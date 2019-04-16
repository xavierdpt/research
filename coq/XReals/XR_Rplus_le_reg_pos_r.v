Require Export XR_Rplus_0_r.
Require Export XR_Rplus_le_reg_r.
Require Export XR_Rplus_le_compat.

Local Open Scope R_scope.

Lemma Rplus_le_reg_pos_r : forall r1 r2 r3,
  R0 <= r2 ->
  r1 + r2 <= r3 ->
  r1 <= r3.
Proof.
  intros x y z.
  intros hy h.
  apply Rplus_le_reg_r with y.
  apply Rle_trans with z.
  { exact h. }
  {
    pattern z at 1 ; rewrite <- Rplus_0_r.
    apply Rplus_le_compat.
    {
      unfold "<=".
      right.
      reflexivity.
    }
    { exact hy. }
  }
Qed.