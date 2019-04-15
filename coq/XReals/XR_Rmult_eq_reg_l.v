Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult.
Require Export XR_Rmult_assoc.
Require Export XR_Rmult_1_l.
Require Export XR_Rmult_eq_compat_l.
Require Export XR_Rinv_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_eq_reg_l : forall r r1 r2, r * r1 = r * r2 -> r <> R0 -> r1 = r2.
Proof.
  intros x y z.
  intro heq.
  intro hneq.
  pattern y ; rewrite <- Rmult_1_l.
  pattern z ; rewrite <- Rmult_1_l.
  rewrite <- Rinv_l with x.
  {
    repeat rewrite Rmult_assoc.
    apply Rmult_eq_compat_l.
    exact heq.
  }
  { exact hneq. }
Qed.

