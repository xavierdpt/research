Require Import XR_Rsqr.
Require Import XR_Rabs.
Require Import XR_Rsqr_le_abs_1.
Require Import XR_Rle_antisym.

Local Open Scope R_scope.

Lemma Rsqr_eq_asb_1 : forall x y:R, Rabs x = Rabs y -> Rsqr x = Rsqr y.
Proof.
  intros x y h.
  apply Rle_antisym.
  {
    apply Rsqr_le_abs_1.
    right.
    exact h.
  }
  {
    apply Rsqr_le_abs_1.
    right.
    symmetry.
    exact h.
  }
Qed.