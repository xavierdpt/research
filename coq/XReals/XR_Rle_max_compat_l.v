Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rle_trans.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rle_max_compat_l : forall x y z, x <= y -> Rmax z x <= Rmax z y.
Proof.
  intros x y z h.
  unfold Rmax.
  destruct (Rle_dec z x) as [ hxl | hxr ] ;
  destruct (Rle_dec z y) as [ hyl | hyr ].
  { exact h. }
  {
    apply Rle_trans with y.
    exact h.
    left.
    apply Rnot_le_lt.
    exact hyr.
  }
  { exact hyl. }
  {
    right.
    reflexivity.
  }
Qed.
