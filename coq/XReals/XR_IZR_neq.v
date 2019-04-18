Require Export XR_eq_IZR.

Local Open Scope R_scope.

Lemma IZR_neq : forall z1 z2:Z,
  z1 <> z2 ->
  IZR z1 <> IZR z2.
Proof.
  intros x y h.
  unfold not.
  intro eq.
  unfold not in h.
  apply h.
  apply eq_IZR.
  exact eq.
Qed.
