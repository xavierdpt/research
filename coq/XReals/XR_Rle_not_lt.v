Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_Rlt_asym.
Require Export XR_Rlt_irrefl.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_not_lt : forall r1 r2, r2 <= r1 -> ~ r1 < r2.
Proof.
  intros x y.
  unfold "<=".
  intros h.
  unfold "~".
  intro hxy.
  destruct h as [ hyx | heq ].
  {
    assert (asym := Rlt_asym x y).
    unfold "~" in asym.
    apply asym.
    { exact hxy. }
    { exact hyx. }
  }
  {
    subst y.
    generalize dependent hxy.
    apply Rlt_irrefl.
  }
Qed.
