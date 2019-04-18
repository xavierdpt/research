Require Export XR_minus_IZR.

Local Open Scope R_scope.

Lemma Z_R_minus : forall n m:Z, IZR n - IZR m = IZR (n - m).
Proof.
  intros n m.
  rewrite minus_IZR.
  reflexivity.
Qed.
