Require Export XR_R.
Require Export XR_R0.
Require Export XR_R1.
Require Export XR_Rplus_opp_r.
Require Export XR_Rmult.
Require Export XR_Rmult_comm.
Require Export XR_Rmult_1_l.
Require Export XR_Rmult_plus_distr_l.
Require Export XR_Rplus_eq_reg_r.
Require Export XR_Rplus_0_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_0_r : forall r, r * R0 = R0.
Proof.
  assert (Rmult_comm := Rmult_comm).
  assert (Rplus_assoc := Rplus_assoc).
  assert (Rplus_opp_r := Rplus_opp_r).
  assert (Rplus_opp_l := Rplus_opp_l).
  assert (Rplus_0_r := Rplus_0_r).
  assert (Rmult_1_l := Rmult_1_l).
  assert (Rmult_plus_distr_l := Rmult_plus_distr_l).
  assert (Rplus_eq_reg_r := Rplus_eq_reg_r).

  intro x.
  pattern R0 at 2;rewrite <- Rplus_opp_r with x.
  apply Rplus_eq_reg_r with x.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  pattern x at 2 ; rewrite <- Rmult_1_l.
  rewrite (Rmult_comm R1).
  rewrite <- Rmult_plus_distr_l.
  rewrite Rplus_0_l.
  rewrite Rmult_comm.
  rewrite Rmult_1_l.
  reflexivity.
Qed.
