Require Import XR_Rmin.
Require Import XR_Rle_dec.

Local Open Scope R_scope.

Lemma Rmin_case : forall r1 r2 (P:R -> Type), P r1 -> P r2 -> P (Rmin r1 r2).
Proof.
  intros x y p px py.
  unfold Rmin.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  { exact px. }
  { exact py. }
Qed.
