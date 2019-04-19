Require Export XR_archimed.
Require Export XR_Rplus_lt_reg_r.
Require Export XR_Rplus_0_r.

Local Open Scope R_scope.

Lemma for_base_fp : forall r,
  R0 < IZR (up r) - r /\ IZR (up r) - r <= R1.
Proof.
  intro x.
  destruct (archimed x) as [ hl hu ].
  split.
  {
    unfold Rminus.
    apply Rplus_lt_reg_r with x.
    rewrite Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
    exact hl.
  }
  { exact hu. }
Qed.