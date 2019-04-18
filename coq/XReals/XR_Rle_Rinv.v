Require Export XR_Rinv_le_contravar.

Local Open Scope R_scope.

Lemma Rle_Rinv : forall x y:R,
  R0 < x ->
  x <= y ->
  / y <= / x.
Proof.
  intros x y hx hxy.
  apply Rinv_le_contravar.
  { exact hx. }
  { exact hxy. }
Qed.
