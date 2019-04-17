Require Export XR_pos_INR.
Require Export XR_Rle_lt_trans.
Require Export XR_Rplus_eq_compat_r.

Local Open Scope R_scope.

Lemma not_0_INR : forall n:nat,
  n <> 0%nat ->
  INR n <> R0.
Proof.
  intros n h.
  unfold not.
  intro eq.
  unfold not in h.
  apply h.
  destruct n as [ | n ].
  { reflexivity. }
  {
    rewrite S_INR in eq.
    clear h.
    exfalso.
    apply (Rplus_eq_compat_r (-R1) _  _ ) in eq.
    rewrite Rplus_assoc in eq.
    rewrite Rplus_opp_r in eq.
    rewrite Rplus_0_r in eq.
    rewrite Rplus_0_l in eq.
    apply Rlt_irrefl with R0.
    apply Rle_lt_trans with (INR n).
    { apply pos_INR. }
    {
      rewrite eq.
      clear eq n.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      exact Rlt_0_1.
    }
  }
Qed.


