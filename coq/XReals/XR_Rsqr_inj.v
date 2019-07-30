Require Import XR_R.
Require Import XR_R0.
Require Import XR_Rle.
Require Import XR_Rle_antisym.
Require Import XR_Rsqr.
Require Import XR_Rsqr_incr_0.

Local Open Scope R_scope.

Lemma Rsqr_inj : forall x y:R, R0 <= x -> R0 <= y -> Rsqr x = Rsqr y -> x = y.
Proof.
  intros x y.
  intros hx hy heq.
  apply Rle_antisym.
  {
    apply Rsqr_incr_0.
    {
      right.
      exact heq.
    }
    { exact hx. }
    { exact hy. }
  }
  {
    apply Rsqr_incr_0.
    {
      right.
      symmetry.
      exact heq.
    }
    { exact hy. }
    { exact hx. }
  }
Qed.