Require Export XR_Rmult_assoc.
Require Export XR_Rinv_r.
Require Export XR_Rmult_1_r.

Local Open Scope R_scope.

Lemma Rinv_r_simpl_l : forall r1 r2, r1 <> R0 -> r2 * r1 * / r1 = r2.
Proof.
  intros x y h.
  rewrite Rmult_assoc.
  rewrite Rinv_r.
  {
rewrite Rmult_1_r.
reflexivity.
}
{ exact h. }
Qed.
