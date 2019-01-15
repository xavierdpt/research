Require Export XRaxioms.

Local Open Scope XR_scope.

Lemma Rle_refl : forall r, r <= r.
Proof.
  intros;right;reflexivity.
Qed.
