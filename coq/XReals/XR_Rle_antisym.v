Require Export XR_R.
Require Export XR_Rle.
Require Export XR_Rlt_asym.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_antisym : forall r1 r2, r1 <= r2 -> r2 <= r1 -> r1 = r2.
Proof.
  intros x y.
  intros hxy hyx.
  unfold "<=" in hxy, hyx.
  destruct hxy as [ hxy | heq ].
  {
    destruct hyx as [ hyx | heq ].
    {
      exfalso.
      assert (asym := Rlt_asym x y).
      unfold "~" in asym.
      apply asym.
      { exact hxy. }
      { exact hyx. }
    }
    { subst y. reflexivity. }
  }
  { subst y. reflexivity. }
Qed.
