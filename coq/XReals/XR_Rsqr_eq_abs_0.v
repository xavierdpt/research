Require Import XR_Rabs.
Require Import XR_Rsqr.
Require Import XR_Rle_antisym.
Require Import XR_Rsqr_le_abs_0.


Local Open Scope R_scope.

Lemma Rsqr_eq_abs_0 : forall x y:R, Rsqr x = Rsqr y -> Rabs x = Rabs y.
Proof.
  intros x y h.
  apply Rle_antisym.
  {
    apply Rsqr_le_abs_0.
    right.
    exact h.
  }
  {
    apply Rsqr_le_abs_0.
    right.
    symmetry.
    exact h.
  }
Qed.