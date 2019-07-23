Require Import XR_Rmax.
Require Import XR_Rle_dec.

Local Open Scope R_scope.

Lemma Rmax_case : forall r1 r2 (P:R -> Type), P r1 -> P r2 -> P (Rmax r1 r2).
Proof.
  intros x y P px py.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hmaxl | hmaxr ].
  { exact py. }
  { exact px. }
Qed.
