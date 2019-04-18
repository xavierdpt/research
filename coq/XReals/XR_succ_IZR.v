Require Export XR_plus_IZR.

Local Open Scope R_scope.

Lemma succ_IZR : forall n:Z, IZR (Z.succ n) = IZR n + R1.
Proof.
  intro n.
  unfold Z.succ.
  rewrite plus_IZR.
  simpl.
  reflexivity.
Qed.