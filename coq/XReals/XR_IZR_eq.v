Require Export XR_IZR.

Local Open Scope R_scope.

Lemma IZR_eq : forall z1 z2:Z,
  z1 = z2 ->
  IZR z1 = IZR z2.
Proof.
  intros x y eq.
  subst y.
  reflexivity.
Qed.