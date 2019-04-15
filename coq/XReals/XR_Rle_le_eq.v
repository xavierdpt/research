Require Export XR_R.
Require Export XR_Rle.
Require Export XR_Rle_antisym.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_le_eq : forall r1 r2, r1 <= r2 /\ r2 <= r1 <-> r1 = r2.
Proof.
intros x y.
split.
{
  intros [ hxy hyx ].
  apply Rle_antisym.
  { exact hxy. }
  { exact hyx. }
}
{
  intro heq.
  subst y.
  split.
  { unfold "<=". right. reflexivity. }
  { unfold "<=". right. reflexivity. }
}
Qed.
