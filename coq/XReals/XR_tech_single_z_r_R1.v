Require Export XR_single_z_r_R1.

Local Open Scope R_scope.

Lemma tech_single_z_r_R1 : forall r (n:Z),
  r < IZR n ->
  IZR n <= r + R1 ->
  (exists s : Z,
    s <> n /\
    r < IZR s /\
    IZR s <= r + R1
  ) -> False.
Proof.
  intros x n ha hb hc.
  destruct hc as [ m [ hca [ hcba hcbb ] ] ].
  apply hca.
  eapply single_z_r_R1.
  { exact hcba. }
  { exact hcbb. }
  { exact ha. }
  { exact hb. }
Qed.