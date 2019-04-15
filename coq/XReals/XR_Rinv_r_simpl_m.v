Require Export XR_Rmult_comm.
Require Export XR_Rmult_assoc.
Require Export XR_Rinv_l.
Require Export XR_Rmult_1_l.

Local Open Scope R_scope.

Lemma Rinv_r_simpl_m : forall r1 r2, r1 <> R0 -> r1 * r2 * / r1 = r2.
Proof.
  intros x y h.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc.
  rewrite Rinv_l.
  {
    rewrite Rmult_1_l.
    reflexivity.
  }
  { exact h . }
Qed.