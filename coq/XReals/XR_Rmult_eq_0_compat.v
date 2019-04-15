Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult.
Require Export XR_Rmult_0_r.
Require Export XR_Rmult_0_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_eq_0_compat : forall r1 r2, r1 = R0 \/ r2 = R0 -> r1 * r2 = R0.
Proof.
  intros x y.
  intros [ xeq | yeq ].
  { subst x. rewrite Rmult_0_l. reflexivity. }
  { subst y. rewrite Rmult_0_r. reflexivity. }
Qed.
