Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rnot_le_lt.
Require Import XR_Rle_trans.

Local Open Scope R_scope.

Lemma Rle_max_compat_r : forall x y z, x <= y -> Rmax x z <= Rmax y z.
Proof.
  intros x y z h.
  unfold Rmax.
  destruct (Rle_dec x z) as [ hxl | hxr ] ;
  destruct (Rle_dec y z) as [ hyl | hyr ].
  {
    right.
    reflexivity.
  }
  {
    left.
    apply Rnot_le_lt.
    exact hyr.
  }
  {
    apply Rle_trans with y.
    { exact h. }
    { exact hyl. }
  }
  { exact h. }
Qed.