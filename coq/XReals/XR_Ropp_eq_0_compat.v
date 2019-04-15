Require Export XR_R.
Require Export XR_R0.
Require Export XR_Ropp.
Require Export XR_Ropp_0.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_eq_0_compat : forall r, r = R0 -> - r = R0.
Proof.
  intros x heq.
  subst x.
  rewrite Ropp_0.
  reflexivity.
Qed.
