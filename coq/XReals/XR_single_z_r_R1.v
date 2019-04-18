Require Export XR_one_IZR_r_R1.

Local Open Scope R_scope.

Lemma single_z_r_R1 : forall r (n m:Z),
  r < IZR n ->
  IZR n <= r + R1 ->
  r < IZR m ->
  IZR m <= r + R1 ->
  n = m.
Proof.
  intros x n m ha hb hc hd.
  eapply one_IZR_r_R1.
  {
    split.
    { exact ha. }
    { exact hb. }
  }
  {
    split.
    { exact hc. }
    { exact hd. }
  }
Qed.