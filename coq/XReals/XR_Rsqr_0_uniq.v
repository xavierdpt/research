Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rsqr.
Require Export XR_Rmult_integral.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rsqr_0_uniq : forall r, Rsqr r = R0 -> r = R0.
Proof.
  intros x h.
  unfold Rsqr in h.
  assert (mi := Rmult_integral).
  specialize (mi x x).
  specialize (mi h).
  destruct mi as [ mi | mi ].
  { exact mi. }
  { exact mi. }
Qed.
