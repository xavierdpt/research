Require Export XR_Rminus.
Require Export XR_Rplus_opp_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rminus_diag_eq : forall r1 r2, r1 = r2 -> r1 - r2 = R0.
Proof.
  intros x y heq.
  subst y.
  unfold Rminus.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.
