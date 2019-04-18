Require Export XR_le_IZR.
Require Export XR_archimed.
Require Export XR_Rle_trans.
Require Export XR_Rle_lt_trans.

Local Open Scope R_scope.

Lemma one_IZR_r_R1 : forall r (n m:Z),
  r < IZR n <= r + R1 ->
  r < IZR m <= r + R1 ->
  n = m.
Proof.
  intros r n m ha hb.
  destruct ha as [ hal har ].
  destruct hb as [ hbl hbr ].
  apply Z.le_antisymm.
  {
    apply Z.lt_succ_r.
    apply lt_IZR.
    unfold Z.succ.
    rewrite plus_IZR.
    simpl.
    eapply Rle_lt_trans.
    exact har.
    apply Rplus_lt_compat_r.
    exact hbl.
  }
  {
    apply Z.lt_succ_r.
    apply lt_IZR.
    unfold Z.succ.
    rewrite plus_IZR.
    simpl.
    eapply Rle_lt_trans.
    exact hbr.
    apply Rplus_lt_compat_r.
    exact hal.
  }
Qed.