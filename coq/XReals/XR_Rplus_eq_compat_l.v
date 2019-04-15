Require Export XR_R.
Require Export XR_Rplus.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_eq_compat_l : forall r r1 r2, r1 = r2 -> r + r1 = r + r2.
Proof.
  intros x y z.
  intro heq.
  subst z.
  reflexivity.
Qed.
