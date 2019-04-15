Require Export XR_R.
Require Export XR_Rplus.
Require Export XR_Rplus_comm.
Require Export XR_Rplus_eq_reg_l.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_eq_reg_r : forall r r1 r2, r1 + r = r2 + r -> r1 = r2.
Proof.
  intros x y z.
  intro h.
  apply Rplus_eq_reg_l with x.
  repeat rewrite (Rplus_comm x).
  exact h.
Qed.
