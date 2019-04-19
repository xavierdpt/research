Require Export XR_tech_up.
Require Export XR_Rplus_le_compat_r.

Local Open Scope R_scope.

Lemma up_tech : forall r z,
  IZR z <= r ->
  r < IZR (z + 1) ->
  (z + 1)%Z = up r.
Proof.
  intros x n hu hl.
  apply tech_up.
  { exact hl. }
  {
    rewrite plus_IZR.
    simpl.
    apply Rplus_le_compat_r.
    exact hu.
  }
Qed.
