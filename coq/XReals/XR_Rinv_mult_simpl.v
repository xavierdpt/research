Require Export XR_Rmult_assoc.
Require Export XR_Rinv_l.
Require Export XR_Rmult_1_r.

Local Open Scope R_scope.

Lemma Rinv_mult_simpl :
  forall r1 r2 r3, r1 <> R0 -> r1 * / r2 * (r3 * / r1) = r3 * / r2.
Proof.
intros x y z h.
rewrite (Rmult_comm x).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm x).
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
{
rewrite Rmult_1_r.
rewrite Rmult_comm.
reflexivity.
}
{ exact h. }
Qed.