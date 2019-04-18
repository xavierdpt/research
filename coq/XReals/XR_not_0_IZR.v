Require Export XR_eq_IZR.

Local Open Scope R_scope.

Lemma not_0_IZR : forall n:Z, n <> 0%Z -> IZR n <> R0.
Proof.
  intros n h.
  unfold not.
  intro heq.
  unfold not in h.
  apply h.
  apply eq_IZR_R0.
  exact heq.
Qed.
