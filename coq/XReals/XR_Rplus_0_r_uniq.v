Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rplus.
Require Export XR_Rplus_eq_reg_l.
Require Export XR_Rplus_0_r.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_0_r_uniq : forall r r1, r + r1 = r -> r1 = R0.
Proof.
  intros x y h.
  apply Rplus_eq_reg_l with x.
  rewrite Rplus_0_r.
  exact h.
Qed.
