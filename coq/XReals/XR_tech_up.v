Require Export XR_single_z_r_R1.

Local Open Scope R_scope.

Lemma tech_up : forall r z,
  r < IZR z ->
  IZR z <= r + R1 ->
  z = up r.
Proof.
  intros x n hl hu.
  destruct (archimed x) as [ al au ].
  apply single_z_r_R1 with x.
  { exact hl. }
  { exact hu. }
  { exact al. }
  {
    rewrite (Rplus_comm x).
    apply Rplus_le_reg_r with (-x).
    rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    unfold Rminus in au.
    exact au.
  }
Qed.
