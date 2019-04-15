Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_eq_compat : forall r1 r2 r3 r4,
  r1 = r2 -> r2 < r4 -> r4 = r3 -> r1 < r3.
Proof.
  intros u v w x.
  intros huv hvx hxw.
  subst v.
  subst w.
  exact hvx.
Qed.
