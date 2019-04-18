Require Export XR_Rnot_lt_le.
Require Export XR_lt_IZR.

Local Open Scope R_scope.

Lemma IZR_le : forall n m:Z, (n <= m)%Z -> IZR n <= IZR m.
Proof.
  intros n m h.
  apply Rnot_lt_le.
  intro hlt.
  apply lt_IZR in hlt.
  eapply Z.lt_irrefl.
  eapply Z.lt_le_trans.
  exact hlt.
  exact h.
Qed.
