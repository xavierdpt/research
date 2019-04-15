Require Export XR_R.
Require Export XR_Rplus.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rplus_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r.
Proof.
  intros x y z.
  intro heq.
  subst z.
  reflexivity.
Qed.
