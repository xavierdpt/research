Require Export XR_le_IZR.

Local Open Scope R_scope.

Lemma le_IZR_R1 : forall n:Z, IZR n <= R1 -> (n <= 1)%Z.
Proof.
  intros n h.
  apply le_IZR.
  simpl.
  exact h.
Qed.
