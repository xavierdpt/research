Require Export XR_Rmult_plus_distr_r.
Require Export XR_Rmult_1_l.
Require Export XR_R2.

Local Open Scope R_scope.

Lemma double : forall r1, R2 * r1 = r1 + r1.
Proof.
  intro x.
  unfold R2.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  reflexivity.
Qed.
