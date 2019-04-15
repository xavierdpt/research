Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_total_order_T.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma inser_trans_R : forall r1 r2 r3 r4,
  r1 <= r2 < r3 -> {r1 <= r2 < r4} + {r4 <= r2 < r3}.
Proof.
  intros u v w x.
  intros [ huv hvw ].
  destruct (total_order_T v x) as [ [ hvx | heq ] | hxv ].
  {
    left.
    split.
    { exact huv. }
    { exact hvx. }
  }
  {
    subst v.
    right.
    split.
    { unfold "<=". right. reflexivity. }
    { exact hvw. }
  }
  {
    right.
    split.
    { unfold "<=". left. exact hxv. }
    { exact hvw. }
  }
Qed.