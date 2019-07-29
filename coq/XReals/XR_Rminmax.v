Require Import XR_Rmin.
Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rminmax : forall a b, Rmin a b <= Rmax a b.
Proof.
  intros x y.
  unfold Rmin, Rmax.
  destruct (Rle_dec x y) as [ h | h ].
  { exact h. }
  {
    left.
    apply Rnot_le_lt.
    exact h.
  }
Qed.