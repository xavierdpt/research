Require Export XR_R.
Require Export XR_Ropp.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_eq_compat : forall r1 r2, r1 = r2 -> - r1 = - r2.
Proof.
  intros x y h.
  subst y.
  reflexivity.
Qed.
