Require Export XR_R2_neq_R0.
Require Export XR_double.
Require Export XR_Rdiv.
Require Export XR_Rinv_r.
Require Export XR_Rmult_1_r.

Local Open Scope R_scope.

Lemma double_var : forall r1, r1 = r1 / R2 + r1 / R2.
Proof.
  intro x.
  unfold Rdiv.
  rewrite <- Rmult_plus_distr_l.
  rewrite <- double.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  reflexivity.
  exact R2_neq_R0.
Qed.