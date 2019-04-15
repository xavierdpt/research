Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_Rlt_asym.
Require Export XR_Rlt_irrefl.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_not_le : forall r1 r2, r2 < r1 -> ~ r1 <= r2.
Proof.
  intros x y.
  unfold "~".
  unfold "<=".
  intros hyx h.
  destruct h as [ hxy | heq ].
  {
    assert (asym := Rlt_asym).
    specialize (asym x y).
    unfold "~" in asym.
    apply asym.
    { exact hxy. }
    { exact hyx. }
  }
  {
    subst y.
    generalize dependent hyx.
    apply Rlt_irrefl.
  }
Qed.
