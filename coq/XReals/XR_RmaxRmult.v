Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rle_antisym.
Require Import XR_Rmult_le_compat_l.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma RmaxRmult :
  forall (p q:R) r, R0 <= r -> Rmax (r * p) (r * q) = r * Rmax p q.
Proof.
  intros x y z h.
  unfold Rmax.
  destruct (Rle_dec (z*x) (z*y)) as [ hpl | hpr ] ;
  destruct (Rle_dec x y) as [ hl | hr ].
  { reflexivity. }
  {
    apply Rle_antisym.
    {
      apply Rmult_le_compat_l.
      { exact h. }
      {
        left.
        apply Rnot_le_lt.
        exact hr.
      }
    }
    { exact hpl. }
  }
  {
    apply Rle_antisym.
    {
      apply Rmult_le_compat_l.
      { exact h. }
      { exact hl. }
    }
    {
      left.
      apply Rnot_le_lt.
      exact hpr.
    }
  }
  { reflexivity. }
Qed.
