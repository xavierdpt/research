Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rlt_asym.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_irrefl : forall r, ~ r < r.
Proof.
  intro r.
  unfold "~".
  intro h.
  assert (asym:=Rlt_asym).
  unfold "~" in asym.
  specialize (asym r r).
  apply asym.
  exact h.
  exact h.
Qed.
