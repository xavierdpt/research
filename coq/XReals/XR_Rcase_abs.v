Require Import XR_R0.
Require Import XR_Rle_dec.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rcase_abs : forall r, {r < R0} + {R0 <= r}.
Proof.
  intro x.
  assert (h := Rle_dec).
  specialize (h R0 x).
  destruct h as [ hl | hr ].
  {
    right.
    exact hl.
  }
  {
    left.
    apply Rnot_le_lt.
    exact hr.
  }
Qed.
