Require Export XR_Ropp_involutive.
Require Export XR_Ropp_le_contravar.

Local Open Scope R_scope.

Lemma Ropp_le_cancel : forall r1 r2,
  - r2 <= - r1 ->
  r1 <= r2.
Proof.
  intros x y h.
  rewrite <- Ropp_involutive with x.
  rewrite <- Ropp_involutive with y.
  apply Ropp_le_contravar.
  exact h.
Qed.
