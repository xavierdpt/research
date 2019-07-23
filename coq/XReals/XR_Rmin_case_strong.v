Require Import XR_R.
Require Import XR_Rle.
Require Import XR_Rle_dec.
Require Import XR_Rmin.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmin_case_strong : forall r1 r2 (P:R -> Type), 
  (r1 <= r2 -> P r1) -> (r2 <= r1 -> P r2) -> P (Rmin r1 r2).
Proof.
  intros x y p px py.
  unfold Rmin.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  {
    apply px.
    exact hminl.
  }
  {
    apply py.
    left.
    apply Rnot_le_lt.
    exact hminr.
  }
Qed.