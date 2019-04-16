Require Export XR_Rmult_lt_compat_l.
Require Export XR_Rmult_0_l.

Local Open Scope R_scope.

Lemma Rmult_lt_0_compat : forall r1 r2,
  R0 < r1 ->
  R0 < r2 ->
  R0 < r1 * r2.
Proof.
  intros x y.
  intros hx hy.
  rewrite <- Rmult_0_r with x.
  apply Rmult_lt_compat_l.
  { exact hx. }
  { exact hy. }
Qed.

