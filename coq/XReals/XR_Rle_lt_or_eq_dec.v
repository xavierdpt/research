Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_Rlt_asym.
Require Export XR_Rlt_irrefl.
Require Export XR_total_order_T.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_lt_or_eq_dec : forall r1 r2, r1 <= r2 -> {r1 < r2} + {r1 = r2}.
Proof.
intros x y h.
unfold "<=" in h.
destruct (total_order_T x y) as [ [ hxy | heq ] | hyx ].
{ left. exact hxy. }
{ subst y. right. reflexivity. }
{
  exfalso.
  destruct h as [ hxy | heq ].
  {
    generalize dependent hyx.
    apply Rlt_asym.
    exact hxy.
  }
  {
    subst y.
    generalize dependent hyx.
    apply Rlt_irrefl.
  }
}
Qed.
