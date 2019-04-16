Require Export XR_Rplus_le_lt_compat.
Require Export XR_Rplus_lt_le_compat.

Local Open Scope R_scope.

Lemma sum_inequa_Rle_lt : forall a x b c y d:R,
    a <= x -> x < b -> c < y -> y <= d -> a + c < x + y < b + d.
Proof.
  intros a x b c y d.
  intros hax hxb hcy hyd.
  split.
  {
    apply Rplus_le_lt_compat.
    { exact hax. }
    { exact hcy. }
  }
  {
    apply Rplus_lt_le_compat.
    { exact hxb. }
    { exact hyd. }
  }
Qed.
