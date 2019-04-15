Require Export XR_R.
Require Export XR_Rmult.
Require Export XR_Rmult_comm.
Require Export XR_Rplus.
Require Export XR_Rmult_plus_distr_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_plus_distr_r : forall r1 r2 r3,
  (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  intros x y z.
  repeat rewrite (Rmult_comm _ z).
  rewrite <- Rmult_plus_distr_l.
  reflexivity.
Qed.
