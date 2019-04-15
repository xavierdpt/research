Require Export XR_R.
Require Export XR_R0.
Require Export XR_R1.
Require Export XR_Rmult.
Require Export XR_Rinv.
Require Export XR_Rinv_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rinv_r_sym : forall r, r <> R0 -> R1 = r * / r.
Proof.
  intros x h.
  symmetry.
  apply Rinv_r.
  exact h.
Qed.


