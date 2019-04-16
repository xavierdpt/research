Require Export XR_Rplus_0_l.
Require Export XR_Rplus_lt_compat.

Local Open Scope R_scope.

Lemma Rplus_lt_0_compat : forall r1 r2, R0 < r1 -> R0 < r2 -> R0 < r1 + r2.
Proof.
  intros x y.
  intros hx hy.
  pattern R0 at 1 ; rewrite <- Rplus_0_l.
  apply Rplus_lt_compat.
  { exact hx. }
  { exact hy. }
Qed.
