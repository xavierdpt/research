Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmax_case_strong : forall r1 r2 (P:R -> Type),
  (r2 <= r1 -> P r1) -> (r1 <= r2 -> P r2) -> P (Rmax r1 r2).
Proof.
  intros x y P hx hy.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hmaxl | hmaxr ].
  {
    apply hy.
    exact hmaxl.
  }
  {
    apply hx.
    left.
    apply Rnot_le_lt.
    exact hmaxr.
  }
Qed.