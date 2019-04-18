Require Export XR_opp_IZR.

Local Open Scope R_scope.

Lemma minus_IZR : forall n m:Z, IZR (n - m) = IZR n - IZR m.
Proof.
  intros n m.
  rewrite <- Z.add_opp_r.
  rewrite plus_IZR.
  rewrite opp_IZR.
  unfold Rminus.
  reflexivity.
Qed.