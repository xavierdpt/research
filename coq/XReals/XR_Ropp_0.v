Require Export XR_R.
Require Export XR_R0.
Require Export XR_Ropp.
Require Export XR_Rplus_eq_reg_l.
Require Export XR_Rplus_opp_r.
Require Export XR_Rplus_0_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_0 : - R0 = R0.
Proof.
  apply Rplus_eq_reg_l with R0.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  reflexivity.
Qed.
