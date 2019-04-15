Require Export XR_R.
Require Export XR_Rle.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_refl : forall r, r <= r.
Proof.
  intro r.
  unfold "<=".
  right.
  reflexivity.
Qed.
