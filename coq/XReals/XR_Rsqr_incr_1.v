Require Import XR_Rsqr.
Require Import XR_Rmult_le_compat.

Local Open Scope R_scope.

Lemma Rsqr_incr_1 : forall x y:R, x <= y -> R0 <= x -> Rsqr x <= Rsqr y.
Proof.
  intros x y h hx.
  unfold Rsqr.
  apply Rmult_le_compat.
  { exact hx. }
  { exact hx. }
  { exact h. }
  { exact h. }
Qed.
