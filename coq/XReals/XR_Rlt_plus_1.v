Require Export XR_Rlt_0_1.
Require Export XR_Rplus_lt_compat_l.

Local Open Scope R_scope.

Lemma Rlt_plus_1 : forall r,
  r < r + R1.
Proof.
  intros x.
  pattern x at 1 ; rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l.
  exact Rlt_0_1.
Qed.

