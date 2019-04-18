Require Export XR_lt_IZR.

Local Open Scope R_scope.

Lemma one_IZR_lt1 : forall n:Z, - R1 < IZR n < R1 -> n = 0%Z.
Proof.
  intros n [hl hr].
  apply Z.le_antisymm.
  {
    apply Z.lt_succ_r.
    apply lt_IZR.
    simpl.
    exact hr.
  }
  {
    apply Z.lt_succ_r.
    apply lt_IZR.
    simpl.
    unfold Z.succ.
    rewrite plus_IZR.
    simpl.
    apply Rplus_lt_reg_l with (-R1).
    rewrite Rplus_0_r.
    rewrite Rplus_comm.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    exact hl.
  }
Qed.