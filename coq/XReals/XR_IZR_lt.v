Require Export XR_Rnot_le_lt.
Require Export XR_le_IZR.

Local Open Scope R_scope.

Lemma IZR_lt : forall n m:Z, (n < m)%Z -> IZR n < IZR m.
Proof.
  intros n m h.
  apply Rnot_le_lt.
  intro hle.
  apply le_IZR in hle.
  eapply Z.lt_irrefl.
  eapply Z.lt_le_trans.
  apply h.
  apply hle.
Qed.
