Require Export XR_INR_eq.

Local Open Scope R_scope.

Lemma not_1_INR : forall n:nat,
  n <> 1%nat ->
  INR n <> R1.
Proof.
  intros n h.
  unfold not.
  intro heq.
  unfold not in h.
  apply h.
  apply INR_eq.
  simpl.
  exact heq.
Qed.

