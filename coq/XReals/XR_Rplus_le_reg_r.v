Require Export XR_Rplus_le_reg_l.

Local Open Scope R_scope.

Lemma Rplus_le_reg_r : forall r r1 r2,
  r1 + r <= r2 + r -> r1 <= r2.
Proof.
  intros x y z h.
  apply Rplus_le_reg_l with x.
  repeat rewrite (Rplus_comm x).
  exact h.
Qed.