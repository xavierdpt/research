Require Export XRaxioms.

Local Open Scope XR_scope.

Lemma Rlt_irrefl : forall r, ~ r < r.
Proof.
  red;intros;eapply Rlt_asym;exact H.
Qed.
