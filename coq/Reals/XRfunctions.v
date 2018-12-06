Require Export ArithRing.

Require Import XRbase.
Require Export XRpow_def.
Require Export XR_Ifp.
Require Export XRbasic_fun.
Require Export XR_sqr.
Require Export XSplitAbsolu.
Require Export XSplitRmult.
Require Export XArithProp.
Require Import Omega.
Require Import Zpower.
Local Open Scope nat_scope.
Local Open Scope XR_scope.

Lemma INR_fact_neq_0 : forall n:nat, INR (fact n) <> R0.
Proof.
  intros n.
  (* forall n, n <> 0 -> INR n <> 0 *)
  apply not_O_INR. 
  (* forall n : nat, fact n <> 0 *)
  apply fact_neq_0. 
Qed.

Local Open Scope nat_scope.
Lemma fact_simpl : forall n:nat, fact (S n) = (S n * fact n).
Proof.
  intro n. simpl. reflexivity.
Qed.
Local Close Scope nat_scope.

Lemma simpl_fact :
  forall n:nat, / INR (fact (S n)) * / / INR (fact n) = / INR (S n).
Proof.
  intro n.
  rewrite fact_simpl.
  rewrite Rinv_involutive.
  rewrite mult_INR.
  rewrite Rinv_mult_distr.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  reflexivity.
  apply INR_fact_neq_0.
  rewrite S_INR.
  apply tech_Rplus.
  apply pos_INR.
  apply Rlt_0_1.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
Qed.

Infix "^" := pow : XR_scope.

Lemma pow_O : forall x:R, x ^ 0 = R1.
Proof.
  intro x.
  simpl.
  reflexivity.
Qed.

Lemma pow_1 : forall x:R, x ^ 1 = x.
Proof.
  intro x.
  simpl.
  rewrite Rmult_1_r.
  reflexivity.
Qed.

Lemma pow_add : forall (x:R) (n m:nat), x ^ (n + m) = x ^ n * x ^ m.
Proof.
  intros x n.
  induction n as [ | n i ].
  { intro m. simpl. rewrite Rmult_1_l. reflexivity. }
  { intro m. simpl. rewrite i. rewrite Rmult_assoc.
    reflexivity.
  }
Qed.

Lemma Rpow_mult_distr : forall (x y:R) (n:nat), (x * y) ^ n = x^n * y^n.
Proof.
  intros x y n.
  induction n as [ | n i ].
  { simpl. rewrite Rmult_1_l. reflexivity. }
  { simpl. rewrite i.
    repeat (rewrite Rmult_assoc).
    rewrite (Rmult_comm y).
    repeat (rewrite Rmult_assoc).
    rewrite (Rmult_comm _ y).
    reflexivity.
  }
Qed.

Lemma pow_nonzero : forall (x:R) (n:nat), x <> R0 -> x ^ n <> R0.
Proof.
  intro. simple induction n. simpl.
  intro. red. intro. apply R1_neq_R0. assumption.
  intros. red. intro. elim (Rmult_integral x (x ^ n0) H1).
  intro. auto.
  apply H. assumption.
Qed.

Hint Resolve pow_O pow_1 pow_add pow_nonzero: real.

Lemma pow_RN_plus :
  forall (x:R) (n m:nat), x <> R0 -> x ^ n = x ^ (n + m) * / x ^ m.
Proof.
  intros x n m h.
  rewrite pow_add.
  rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  reflexivity.
  apply pow_nonzero.
  assumption.
Qed.

Lemma pow_lt : forall (x:R) (n:nat), R0 < x -> R0 < x ^ n.
Proof.
  intros x n h.
  induction n as [ | n i ].
  simpl. apply Rlt_0_1.
  simpl.
  rewrite <- Rmult_0_r with R0.
  apply Rmult_le_0_lt_compat.
  right;reflexivity.
  right;reflexivity.
  assumption.
  assumption.
Qed.
Hint Resolve pow_lt: real.

Lemma Rlt_pow_R1 : forall (x:R) (n:nat), R1 < x -> (0 < n)%nat -> R1 < x ^ n.
Proof.
  intros x n.
  induction n as [ | n i ].
  {
    intros hx hf.
    inversion hf.
  }
  {
    destruct n.
    {
      intros hx hu.
      simpl.
      rewrite Rmult_1_r.
      exact hx.
    }
    {
      intros hx hn.
      rewrite <- Rmult_1_l with R1.
      apply Rlt_trans with (x * R1).
      { rewrite Rmult_1_r. rewrite Rmult_1_r. exact hx. }
      {
        simpl.
        apply Rmult_lt_compat_l.
        {
          apply Rlt_trans with R1.
          { apply Rlt_0_1. }
          { exact hx. }
        }
        {
          simpl in i.
          apply i.
          { exact hx. }
          { unfold lt. apply le_n_S. apply le_0_n. }
        }
      }
    }
  }
Qed.
Hint Resolve Rlt_pow_R1: real.

Lemma Rlt_pow : forall (x:R) (n m:nat), R1 < x -> (n < m)%nat -> x ^ n < x ^ m.
Proof.
  intros x n.
  induction n as [ | n i ].
  { simpl. intros m hx hm. apply Rlt_pow_R1. exact hx. exact hm. }
  {
    destruct m.
    { simpl. intros hx hn. inversion hn. }
    { intros hx hnm. unfold lt in hnm. apply le_S_n in hnm.
      simpl. apply Rmult_lt_compat_l.
      apply Rlt_trans with R1. apply Rlt_0_1. exact hx.
      apply i. exact hx. unfold lt. exact hnm.
    }
  }
Qed.
Hint Resolve Rlt_pow: real.

Lemma tech_pow_Rmult : forall (x:R) (n:nat), x * x ^ n = x ^ S n.
Proof.
  intros x n.
  simpl.
  reflexivity.
Qed.

Arguments INR _ : simpl nomatch.

Lemma tech_pow_Rplus :
  forall (x:R) (a n:nat), x ^ a + INR n * x ^ a = INR (S n) * x ^ a.
Proof.
  intros x a n.
  induction n as [ | n i ].
  { simpl. rewrite Rmult_0_l. rewrite Rmult_1_l. rewrite Rplus_0_r. reflexivity. }
  {
    simpl.
    rewrite <- i.
    rewrite S_INR.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    rewrite Rplus_comm.
    apply Rplus_eq_compat_r.
    rewrite Rplus_comm.
    reflexivity.
  }
Qed.

Lemma poly : forall (n:nat) (x:R), R0 < x -> R1 + INR n * x <= (R1 + x) ^ n.
Proof.
  intros n x hx.
  induction n as [ | n i ].
  { simpl. rewrite Rmult_0_l. rewrite Rplus_0_r. right. reflexivity. }
  { destruct n.
    { simpl. rewrite Rmult_1_l. rewrite Rmult_1_r. right. reflexivity. }
    {
      rewrite S_INR.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      rewrite <- tech_pow_Rmult.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      pose (l:= R1 + INR (S n) * x).
      fold l in i.
      rewrite <- Rplus_assoc.
      fold l.
      pose (r:= (R1+x)^(S n)).
      fold r in i.
      fold r.
      apply Rplus_le_compat.
      { exact i. }
      {
        pattern x at 1;rewrite <- Rmult_1_r.
        apply Rmult_le_compat_l.
        { left. exact hx. }
        {
          left.
          unfold r.
          apply Rlt_pow_R1.
          {
            pattern R1 at 1;rewrite <- Rplus_0_r.
            apply Rplus_lt_compat_l.
            exact hx.
          }
          {
            unfold lt.
            apply le_n_S.
            apply le_0_n.
          }
        }
      }
    }
  }
Qed.

Lemma Power_monotonic :
  forall (x:R) (m n:nat),
    R1 < Rabs x -> (m <= n)%nat -> Rabs (x ^ m) <= Rabs (x ^ n).
Proof.
  intros x m n hx hmn.

  unfold Rabs in hx. destruct (Rcase_abs x).
  {
    generalize dependent n.
    induction m as [ | m mi ].
    {
      induction n as [ | n ni].
      { simpl. intro u. right. reflexivity. }
      {
        simpl. intro u.
        simpl in ni.
        apply Rle_trans with (Rabs (x^n)).
        apply ni. apply le_0_n.
        rewrite Rabs_mult.
        pattern (Rabs (x^n)) at 1;rewrite <- Rmult_1_l.
        apply Rmult_le_compat_r.
        apply Rabs_pos.
        left.
        unfold Rabs. destruct (Rcase_abs x).
        exact hx.
        destruct r0.
        exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x;assumption.
        subst x. apply Rlt_irrefl in r. contradiction.
      }
    }
    {
      intro n. destruct n.
      { simpl. intro hm.
        rewrite Rabs_mult.
        specialize (mi 0%nat).
        simpl in mi.
        inversion hm.
      }
      {
        intros hmn.
        apply le_S_n in hmn.
        simpl.
        rewrite Rabs_mult.
        rewrite Rabs_mult.
        apply Rmult_le_compat_l.
        apply Rabs_pos.
        apply mi.
        exact hmn.
      }
    }
  }
  {
    destruct r.
    {
      generalize dependent n.
      induction m as [ | m mi ].
      {
        induction n as [ | n ni].
        { simpl. intro u. right. reflexivity. }
        {
          simpl. intro u.
          simpl in ni.
          apply Rle_trans with (Rabs (x^n)).
          apply ni. apply le_0_n.
          rewrite Rabs_mult.
          pattern (Rabs (x^n)) at 1;rewrite <- Rmult_1_l.
          apply Rmult_le_compat_r.
          apply Rabs_pos.
          left.
          unfold Rabs. destruct (Rcase_abs x).
          exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x;assumption.
          exact hx.
        }
      }
      {
        intro n. destruct n.
        { simpl. intro hm.
          inversion hm.
        }
        {
          intros hmn.
          apply le_S_n in hmn.
          simpl.
          rewrite Rabs_mult.
          rewrite Rabs_mult.
          apply Rmult_le_compat_l.
          apply Rabs_pos.
          apply mi.
          exact hmn.
        }
      }
    }
    {
      subst x.
      exfalso. apply Rlt_irrefl with R1. apply Rlt_trans with R0.
      assumption. apply Rlt_0_1.
    }
  }
Qed.

Lemma RPow_abs : forall (x:R) (n:nat), Rabs x ^ n = Rabs (x ^ n).
Proof.
  intros x n.
  induction n as [ | n i ].
  { simpl. rewrite Rabs_R1. reflexivity. }
  { simpl. rewrite Rabs_mult. rewrite i. reflexivity. }
Qed.

Lemma XD_INR_Rge : forall r:R, exists n:nat, r <= INR n.
Proof.
  intro r.
  destruct (archimed r) as [ agt ale ].
  exists (Z.abs_nat (up r)).
  destruct (up r) eqn:upeq.
  { (* up r = 0 *)
    simpl.
    left. exact agt.
  }
  { (* up r = Z.pos p *)
    simpl.
    destruct (Pos.to_nat p) eqn:poseq.
    { (* Pos.to_nat p = 0 *)
      simpl.
      generalize (Pos2Nat.is_pos p);intro hpos.
      rewrite poseq in hpos.
      inversion hpos.
    }
    { (* Pos.to_nat p = S n *)
      (* rewrite S_INR. *)
      left.
      rewrite INR_IZR_INZ.
      rewrite <- poseq.
      rewrite positive_nat_Z.
      exact agt.
    }
  }
  { (* up r = Z.neg p *)
    simpl.
    destruct (Pos.to_nat p) eqn:poseq.
    { (* Pos.to_nat p = 0 *)
      simpl.
      generalize (Pos2Nat.is_pos p);intro hpos.
      rewrite poseq in hpos.
      inversion hpos.
    }
    { (* Pos.to_nat p = S n *)
      left.
      rewrite INR_IZR_INZ.
      rewrite <- poseq.
      rewrite positive_nat_Z.
      apply Rlt_trans with (IZR (Z.neg p)).
      { exact agt. }
      {
        apply IZR_lt.
        apply Pos2Z.neg_lt_pos.
      }
    }
  }
Qed.


Lemma Pow_x_infinity :
  forall x:R,
    R1 < Rabs x ->
    forall b:R,
      exists N : nat, (forall n:nat, (n >= N)%nat -> b <= Rabs (x ^ n) ).
Proof.
  intros.
  pose (exp := b * / (Rabs x - R1)).
  destruct (archimed exp) as [H0 H1].
  clear H1.
  {
    destruct (XD_INR_Rge exp) as [x0 H1].
    exists x0.
    intros n H2.
    apply Rle_trans with (Rabs (x ^ x0)).
    {
      rewrite <- RPow_abs.
      rewrite <- Rplus_0_l with (Rabs x).
      rewrite <- Rplus_opp_r with R1.
      rewrite Rplus_assoc.
      rewrite (Rplus_comm _ (Rabs x)).
      fold (Rabs x - R1).
      apply Rle_trans with (R1 + INR x0 * (Rabs x - R1)).
      {
        apply Rle_trans with (INR x0 * (Rabs x - R1)).
        {
          rewrite <- Rmult_1_r with b.
          pattern R1 at 1;rewrite <- Rinv_l with (Rabs x - R1).
          rewrite <- Rmult_assoc.
          fold (b / (Rabs x - R1)).
          {
            apply Rmult_le_compat_r.
            {
              apply Rplus_le_reg_r with R1.
              unfold Rminus.
              rewrite Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
              left.
              exact H.
            }
            { 
              fold exp.
              fold exp in H0, H1.
              exact H1.
            }
          }
          {
            apply Rlt_dichotomy_converse.
            right.
            apply Rplus_lt_reg_r with R1.
            unfold Rminus.
            rewrite Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
            exact H.
          }
        }
        {
          left.
          rewrite (Rplus_comm R1).
          pattern (INR x0 * (Rabs x - R1)) at 1;rewrite <- Rplus_0_r.
          apply Rplus_lt_compat_l.
          apply Rlt_0_1.
        }
      }
      {
        apply poly.
        apply Rplus_lt_reg_r with R1.
        unfold Rminus.
        rewrite Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
        exact H.
      }
    }
    {
      apply Power_monotonic.
      { exact H. }
      { unfold ge in H2. exact H2. }
    }
  }
Qed.

Lemma pow_ne_zero : forall n:nat, n <> 0%nat -> R0 ^ n = R0.
Proof.
  intros n h.
  destruct n.
  { exfalso. apply h. reflexivity. }
  { simpl. rewrite Rmult_0_l. reflexivity. }
Qed.

Lemma Rinv_pow : forall (x:R) (n:nat), x <> R0 -> / x ^ n = (/ x) ^ n.
Proof.
  intros x n h.
  induction n as [ | n i].
  simpl. rewrite Rinv_1. reflexivity.
  simpl. rewrite Rinv_mult_distr. rewrite i. reflexivity.
  exact h.
  apply pow_nonzero. exact h.
Qed.

(* stopped here *)

Lemma Rlt_0_half : R0 < / (IZR 2). Admitted.
Lemma half_nz : / (IZR 2) <> R0. Admitted.

Lemma lala :
    Rabs (/ (IZR 2)) < R1 ->
    forall y:R,
      R0 < y ->
      exists N : nat, (/ (IZR 2)) ^ N < y.
Proof.
  intros H y hy.
  assert (hadx : R1 < Rabs (/ (/ (IZR 2))) ).
  {
    rewrite <- (Rinv_involutive R1).
    { 
      rewrite Rabs_Rinv.
      {
        apply Rinv_lt_contravar.
        {
          apply Rmult_lt_0_compat.
          {
            apply Rabs_pos_lt.
            exact half_nz.
          }
          {
            rewrite Rinv_1.
            apply Rlt_0_1.
          }
        }
        {
          rewrite Rinv_1.
          exact H.
        }
      }
      { exact half_nz. }
    }
    { 
      apply R1_neq_R0.
    }
  }
  generalize Pow_x_infinity;intro hpow.
  specialize (hpow (/ (/ (IZR 2)))).
  specialize (hpow hadx).
  specialize (hpow (/ y + R1)).
  destruct hpow as [N hpow].
  exists N.
  specialize (hpow N).
  assert (ob:(N >= N)%nat). constructor.
  specialize (hpow ob).
  rewrite <- (Rinv_involutive y).
  {
    {
      {
        {

rewrite <- Rinv_pow.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
exact hy.
apply pow_lt.

(*
      {
        rewrite <- Rabs_Rinv.
        {
          rewrite Rinv_pow.
          {
            apply Rlt_le_trans with (/ y + 1).
            {
              pattern (/ y) at 1;rewrite <- Rplus_0_r.
              apply Rplus_lt_compat_l.
              apply Rlt_0_1.
            }
            {
              apply Rge_le.
              exact hpow.
            }
          }
          { exact half_nz. }
        }
        {
          apply pow_nonzero.
          exact half_nz.
        }
      }
    }
    {
      apply Rabs_no_R0.
      apply pow_nonzero.
      exact half_nz.
    }
  }
  {
    apply Rlt_dichotomy_converse.
    right.
    unfold Rgt.
    exact hy.
  }
*)
Admitted.


Lemma pow_lt_1_zero :
  forall x:R,
    Rabs x < R1 ->
    forall y:R,
      R0 < y ->
      exists N : nat, (forall n:nat, (n >= N)%nat -> Rabs (x ^ n) < y).
Proof.
  intros x H y hy.
  destruct (Req_dec x R0) as [hz | hnz]. (* x = 0 \/ x <> 0 *)
  { (* x = 0 *)
    subst x.
    exists 1%nat.
    intros n hn.
    rewrite pow_ne_zero. (* n <> 0 -> 0 ^ n = 0 *)
    {
      rewrite Rabs_R0. (* Rabs 0 = 0 *)
      exact hy.
    }
    {
      inversion hn as [ heq | m hmn ].
      {
        intro eq.
        inversion eq.
      }
      {
        subst n.
        intro eq.
        inversion eq.
      }
    }
  }
  { (* x <> 0 *)
    assert (hadx : R1 < Rabs (/ x) ).
    {
      rewrite <- (Rinv_involutive R1).
      { 
        rewrite Rabs_Rinv.
        {
          apply Rinv_lt_contravar.
          {
            apply Rmult_lt_0_compat.
            {
              apply Rabs_pos_lt.
              exact hnz.
            }
            {
              rewrite Rinv_1.
              apply Rlt_0_1.
            }
          }
          {
            rewrite Rinv_1.
            exact H.
          }
        }
        { exact hnz. }
      }
      { 
        apply R1_neq_R0.
      }
    }
    generalize Pow_x_infinity;intro hpow.
    specialize (hpow (/ x)).
    specialize (hpow hadx).
    specialize (hpow (/ y + R1)).
    destruct hpow as [N hpow].
    exists N.
    intros n hnN.
    specialize (hpow n).
    specialize (hpow hnN).
    rewrite <- (Rinv_involutive y).
    {
      rewrite <- (Rinv_involutive (Rabs (x ^ n))).
      {
        apply Rinv_lt_contravar.
        {
          apply Rmult_lt_0_compat.
          {
            apply Rinv_0_lt_compat.
            exact hy.
          }
          {
            apply Rinv_0_lt_compat.
            apply Rabs_pos_lt.
            apply pow_nonzero.
            exact hnz.
          }
        }
        {
          rewrite <- Rabs_Rinv.
          {
            rewrite Rinv_pow.
            {
              apply Rlt_le_trans with (/ y + R1).
              {
                pattern (/ y) at 1;rewrite <- Rplus_0_r.
                apply Rplus_lt_compat_l.
                apply Rlt_0_1.
              }
              {
                exact hpow.
              }
            }
            { exact hnz. }
          }
          {
            apply pow_nonzero.
            exact hnz.
          }
        }
      }
      {
        apply Rabs_no_R0.
        apply pow_nonzero.
        exact hnz.
      }
    }
    {
      apply Rlt_dichotomy_converse.
      right.
      exact hy.
    }
  }
Qed.

Lemma XD_Rabs_lt_0_Sn: forall r n,
  r<>R0 ->
  R1 < Rabs r ->
  Rabs r ^ 0 < Rabs r ^ S n.
Proof.
  intros r n hrnz harlt.
  simpl.
  induction n as [ | n i ].
  {
    simpl.
    rewrite Rmult_1_r.
    exact harlt.
  }
  {
    simpl.
    apply Rlt_trans with (Rabs r).
    {
      exact harlt.
    }
    {
      pattern (Rabs r) at 1;rewrite <- Rmult_1_r.
      apply Rmult_lt_compat_l.
      2:exact i.
      {
        apply Rabs_pos_lt.
        exact hrnz.
      }
    }
  }
Qed.

Lemma pow_R1 : forall (r:R) (n:nat), r ^ n = R1 -> Rabs r = R1 \/ n = 0%nat.
Proof.
  intros r n h.
  destruct (Req_dec (Rabs r) R1) as [ hareq | harneq ].
  { (* Rabs r = 1 *)
    left. exact hareq.
  }
  { (* Rabs r <> 1 *)
    right.
    apply Rdichotomy in harneq.
    destruct harneq as [ harlt | hargt ].
    { (* Rabs r < 1 *)
      {
        destruct n as [ | n ].
        { (* n = 0 *)
          reflexivity.
        }
        { (* n <> 0 *)
          {
            (* h is absurd when r = 0 *)
            assert (hrnz: r<>R0).
            {
              intro heq.
              subst r.
              simpl in h.
              rewrite Rmult_0_l in h.
              apply R1_neq_R0.
              symmetry.
              exact h.
            }
            (* from there, it's obvious that Rabs r <> 0 *)
            assert (harnz : Rabs r <> R0).
            { apply Rabs_no_R0. exact hrnz. }
            (* We cannot show this goal, so there must be an inconsistency *)
            exfalso.
            (* We use XD_Rabs_lt_0_Sn to reveal the inconsistency *)
            apply Rlt_irrefl with R1.
            pattern R1 at 1;rewrite <- pow_O with (Rabs (/ r)).
            rewrite <- Rabs_R1.
            rewrite <- Rinv_1.
            rewrite <- h.
            rewrite Rinv_pow.
            2:exact hrnz.
            rewrite <- RPow_abs.
            apply XD_Rabs_lt_0_Sn.
            {
              apply Rinv_neq_0_compat.
              exact hrnz.
            }
            {
              rewrite Rabs_Rinv.
              2:exact hrnz.
              pattern R1 at 1;rewrite <- Rinv_involutive.
              2:exact R1_neq_R0.
              apply Rinv_lt_contravar.
              {
                rewrite Rinv_1.
                rewrite Rmult_1_r.
                apply Rabs_pos_lt.
                exact hrnz.
              }
              {
                rewrite Rinv_1.
                exact harlt.
              }
            }
          }
        }
      }
    }
    {
      destruct n as [ | n ].
      { reflexivity. }
      {
        assert (hrnz:r<>R0).
        {
          intro hrz.
          subst r.
          simpl in h.
          rewrite Rmult_0_l in h.
          symmetry in h.
          apply R1_neq_R0 in h.
          contradiction.
        }
        assert (harnz:Rabs r <> R0).
        {
          apply Rabs_no_R0.
          exact hrnz.
        }
        exfalso.
        apply Rlt_irrefl with R1.
        pattern R1 at 1;rewrite <- pow_O with (Rabs r).
        rewrite <- Rabs_R1.
        rewrite <- h.
        rewrite <- RPow_abs.
        apply XD_Rabs_lt_0_Sn.
        exact hrnz.
        exact hargt.
      }
    }
  }
Qed.

Lemma pow_Rsqr : forall (x:R) (n:nat), x ^ (2 * n) = Rsqr x ^ n.
Proof.
  intros x n.
  induction n as [ | n i ].
  { simpl. reflexivity. }
  {
    simpl.
    rewrite plus_comm.
    simpl.
    rewrite (plus_comm n).
    simpl.
    simpl in i.
    rewrite plus_comm in i.
    rewrite <- plus_assoc in i.
    simpl in i.
    rewrite i.
    unfold Rsqr.
    repeat (rewrite Rmult_assoc).
    reflexivity.
  }
Qed.

Lemma pow_le : forall (a:R) (n:nat), R0 <= a -> R0 <= a ^ n.
Proof.
  intros a n h.
  induction n as [ | n i ].
  { simpl. left. apply Rlt_0_1. }
  { simpl. apply Rmult_le_pos. exact h. exact i. }
Qed.

Lemma pow_1_even : forall n:nat, (-R1) ^ (2 * n) = R1.
Proof.
  intro n. induction n as [ | n i ].
  { simpl. reflexivity. }
  { rewrite pow_Rsqr. rewrite pow_Rsqr in i. simpl.
    rewrite i. rewrite Rmult_1_r.
    unfold Rsqr.
    unfold IZR.
    rewrite <- Ropp_mult_distr_l.
    rewrite <- Ropp_mult_distr_r.
    rewrite Ropp_involutive.
    rewrite Rmult_1_r.
    reflexivity.
  }
Qed.

Lemma pow_1_odd : forall n:nat, (-R1) ^ S (2 * n) = -R1.
Proof.
  intros n.
  pose (twice:=(2*n)%nat).
  fold twice.
  simpl.
  unfold twice.
  rewrite pow_1_even.
  rewrite Rmult_1_r.
  reflexivity.
Qed.

Lemma XD_even_odd : forall n:nat, ((exists n', n=2 * n') \/ (exists n', n = S(2 * n')))%nat.
Proof.
  intro n.
  induction n as [ | n i ].
  {
    simpl.
    left. exists 0%nat. simpl. reflexivity.
  }
  {
    destruct i as [ l | r ].
    {
      destruct l as [ n' h ].
      subst n.
      simpl.
      right. exists n'. reflexivity.
    }
    {
      destruct r as [ n' h ].
      subst n.
      simpl.
      left.
      exists (S n').
      simpl.
      rewrite (plus_comm n').
      rewrite (plus_comm n').
      simpl.
      rewrite plus_n_Sm.
      reflexivity.
    }
  }
Qed.

Lemma pow_1_abs : forall n:nat, Rabs ((-R1) ^ n) = R1.
Proof.
  intros n.
  destruct (XD_even_odd n) as [ heven | hodd ].
  destruct heven as [n' eq].
  subst n. rewrite pow_1_even. rewrite Rabs_R1. reflexivity.
  destruct hodd as [n' eq].
  subst n. rewrite pow_1_odd. unfold IZR. rewrite Rabs_Ropp.
  fold (IZR 1). rewrite Rabs_R1. reflexivity.
Qed.

(* stopped here *)

Lemma pow_mult : forall (x:R) (n1 n2:nat), x ^ (n1 * n2) = (x ^ n1) ^ n2.
Proof.
  intros x n m.
  induction n as [ | n i ].
  { simpl.
    induction m as [ | m i ].
    { simpl. reflexivity. }
    { simpl. rewrite <- i. rewrite Rmult_1_r. reflexivity. }
  }
  {
    simpl.
    rewrite pow_add.
    rewrite i.
    rewrite Rpow_mult_distr.
    reflexivity.
  }
Qed.

Lemma pow_incr : forall (x y:R) (n:nat), R0 <= x <= y -> x ^ n <= y ^ n.
Proof.
  intros x y n h.
  induction n as [ | n i ].
  { simpl. right. reflexivity. }
  {
    simpl.
    destruct h as [ l r ].
    apply Rmult_le_compat.
    { exact l. }
    { apply pow_le. exact l. }
    { exact r. }
    { exact i. }
  }
Qed.

Lemma pow_R1_Rle : forall (x:R) (k:nat), R1 <= x -> R1 <= x ^ k.
Proof.
  intros x n h.
  induction n as [ | n i ].
  { simpl. right. reflexivity. }
  {
    simpl.
    pattern R1 at 1;rewrite <- Rmult_1_l.
    apply Rmult_le_compat.
    left. exact Rlt_0_1.
    left. exact Rlt_0_1.
    exact h.
    exact i.
  }
Qed.

Lemma Rle_pow :
  forall (x:R) (m n:nat), R1 <= x -> (m <= n)%nat -> x ^ m <= x ^ n.
Proof.
  intros x m.
  induction m as [ | m mi ].
  {
    intros n hx hn.
    simpl.
    apply pow_R1_Rle.
    exact hx.
  }
  {
    intros n hx hn.
    destruct n.
    { inversion hn. }
    {
      simpl.
      apply Rmult_le_compat_l.
      apply Rle_trans with R1.
      left. exact Rlt_0_1.
      exact hx.
      apply mi.
      exact hx.
      apply le_S_n.
      exact hn.
    }
  }
Qed.

Lemma pow1 : forall n:nat, R1 ^ n = R1.
Proof.
  intro n.
  induction n as [ | n i ].
  simpl. reflexivity.
  simpl. rewrite i. rewrite Rmult_1_l. reflexivity.
Qed.

Lemma pow_Rabs : forall (x:R) (n:nat), x ^ n <= Rabs x ^ n.
Proof.
  intros x n.
  destruct n.
  { simpl. right. reflexivity. }
  {
    simpl.
    unfold Rabs in *.
    destruct (Rcase_abs x).
    {
      destruct (XD_even_odd n) as [ [ n' heven ] | [ n' hodd ]  ].
      {
        subst n. rename n' into n.
        pattern (-x) at 2;rewrite <- Rmult_1_r.
        rewrite <- (Ropp_mult_distr_l _ R1).
        rewrite (Ropp_mult_distr_r _ R1).
        rewrite Rpow_mult_distr.
        rewrite pow_1_even.
        rewrite Rmult_1_r.
        apply Rmult_le_compat_r.
        {
          rewrite pow_Rsqr.
          apply pow_le.
          apply Rle_0_sqr.
        }
        {
          left.
          apply Rlt_trans with R0.
          exact r.
          rewrite <- Ropp_0.
          apply Ropp_lt_contravar.
          exact r.
        }
      }
      {
        subst n.
        pattern (-x) at 2;rewrite <- Rmult_1_r.
        rewrite <- (Ropp_mult_distr_l _ R1).
        rewrite (Ropp_mult_distr_r _ R1).
        rewrite Rpow_mult_distr.
        rewrite pow_1_odd.
        unfold IZR.
        rewrite <- Ropp_mult_distr_r.
        fold (IZR 1).
        rewrite Rmult_1_r.
        rewrite <- Ropp_mult_distr_r.
        rewrite <- Ropp_mult_distr_l.
        rewrite Ropp_involutive.
        right.
        reflexivity.
      }
    }
    {
      right.
      reflexivity.
    }
  }
Qed.

Lemma pow_maj_Rabs : forall (x y:R) (n:nat), Rabs y <= x -> y ^ n <= x ^ n.
Proof.
  intros x y n h.
  assert (hx:R0 <= x).
  {
    apply Rle_trans with (Rabs y).
    apply Rabs_pos.
    exact h.
  }
  {
    apply Rle_trans with (Rabs y ^ n).
    { apply pow_Rabs. }
    { induction  n as [ | n i ].
      { right. simpl. reflexivity. }
      {
        simpl.
        apply Rle_trans with (x * Rabs y ^ n).
        {
          apply Rmult_le_compat_r.
          {
            apply pow_le.
            apply Rabs_pos.
          }
          { exact h. }
        }
        {
          apply Rmult_le_compat_l.
          { exact hx. }
          { apply i. }
        }
      }
    }
  }
Qed.

Lemma Rsqr_pow2 : forall x, Rsqr x = x ^ 2.
Proof.
  intro x.
  unfold Rsqr.
  simpl.
  rewrite Rmult_1_r.
  reflexivity.
Qed.

Section PowerRZ.

Local Coercion Z_of_nat : nat >-> Z.

Section Z_compl.

Local Open Scope Z_scope.

Inductive Z_spec (x : Z) : Z -> Type :=
| ZintNull : x = 0 -> Z_spec x 0
| ZintPos (n : nat) : x = n -> Z_spec x n
| ZintNeg (n : nat) : x = - n -> Z_spec x (- n).

Lemma intP (x : Z) : Z_spec x x.
Proof.
  induction x.
  {
    apply ZintNull. (* x = 0 -> Z_spec x 0 *)
    reflexivity.
  }
  {
    rewrite <- positive_nat_Z at 2. (* Pos.to_nat p = Z.pos p *)
    apply ZintPos. (* x = n -> Z_spec x n *)
    rewrite positive_nat_Z.
    reflexivity.
  }
  {
    rewrite  <- Pos2Z.opp_pos. (* - Z.pos p = Z.neg p *)
    rewrite <- positive_nat_Z at 2.
    apply ZintNeg.
    rewrite positive_nat_Z.
    reflexivity.
  }
Qed.

End Z_compl.

Definition powerRZ (x:R) (n:Z) :=
  match n with
    | Z0 => R1
    | Zpos p => x ^ Pos.to_nat p
    | Zneg p => / x ^ Pos.to_nat p
  end.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : XR_scope.

Lemma Zpower_NR0 :
  forall (x:Z) (n:nat), (0 <= x)%Z -> (0 <= Zpower_nat x n)%Z.
Proof.
  intros x n h.
  induction n as [ | n i ].
  {
    simpl.
    unfold Z.le.
    simpl.
    intro eq.
    inversion eq.
  }
  {
    simpl.
    apply Z.mul_nonneg_nonneg.
    exact h.
    exact i.
  }
Qed.

Lemma powerRZ_O : forall x:R, x ^Z 0 = R1.
Proof.
  intro x.
  simpl.
  reflexivity.
Qed.

Lemma powerRZ_1 : forall x:R, x ^Z Z.succ 0 = x.
Proof.
  intro x.
  simpl.
  rewrite Rmult_1_r.
  reflexivity.
Qed.

Lemma powerRZ_NOR : forall (x:R) (z:Z), x <> R0 -> x ^Z z <> R0.
Proof.
  intros x z neq eq.
  destruct z;simpl in eq.
  {
    apply R1_neq_R0. exact eq.
  }
  {
    apply (pow_nonzero _ (Pos.to_nat p)) in neq.
    contradiction.
  }
  {
    generalize neq;intro neqpow.
    apply Rinv_neq_0_compat in neqpow.
    apply (pow_nonzero _ (Pos.to_nat p)) in neqpow.
    rewrite Rinv_pow in eq.
    contradiction.
    exact neq.
  }
Qed.

(* skipped *)
Lemma powerRZ_pos_sub (x:R) (n m:positive) : x <> R0 ->
   x ^Z (Z.pos_sub n m) = x ^ Pos.to_nat n * / x ^ Pos.to_nat m.
Proof.
 intro Hx.
 rewrite Z.pos_sub_spec.
 case Pos.compare_spec; intro H; simpl.
 - subst; auto with real.
 - rewrite Pos2Nat.inj_sub by trivial.
   rewrite Pos2Nat.inj_lt in H.
   rewrite (pow_RN_plus x _ (Pos.to_nat n)) by auto with real.
   rewrite plus_comm, le_plus_minus_r by auto with real.
   rewrite Rinv_mult_distr, Rinv_involutive; auto with real.
 - rewrite Pos2Nat.inj_sub by trivial.
   rewrite Pos2Nat.inj_lt in H.
   rewrite (pow_RN_plus x _ (Pos.to_nat m)) by auto with real.
   rewrite plus_comm, le_plus_minus_r by auto with real.
   reflexivity.
Qed.

(* skipped *)
Lemma powerRZ_add :
  forall (x:R) (n m:Z), x <> R0 -> x ^Z (n + m) = x ^Z n * x ^Z m.
Proof.
  intros x [|n|n] [|m|m]; simpl; intros; auto with real.
  - (* + + *)
    rewrite Pos2Nat.inj_add; auto with real.
  - (* + - *)
    now apply powerRZ_pos_sub.
  - (* - + *)
    rewrite Rmult_comm. now apply powerRZ_pos_sub.
  - (* - - *)
    rewrite Pos2Nat.inj_add; auto with real.
    rewrite pow_add; auto with real.
    apply Rinv_mult_distr; apply pow_nonzero; auto.
Qed.
Hint Resolve powerRZ_O powerRZ_1 powerRZ_NOR powerRZ_add: real.

(* skipped *)
Lemma Zpower_nat_powerRZ :
  forall n m:nat, IZR (Zpower_nat (Z.of_nat n) m) = INR n ^Z Z.of_nat m.
Proof.
  intros n m; elim m; simpl; auto with real.
  intros m1 H'; rewrite SuccNat2Pos.id_succ; simpl.
  replace (Zpower_nat (Z.of_nat n) (S m1)) with
  (Z.of_nat n * Zpower_nat (Z.of_nat n) m1)%Z.
  rewrite mult_IZR; auto with real.
  repeat rewrite <- INR_IZR_INZ; simpl.
  rewrite H'; simpl.
  case m1; simpl; auto with real.
  intros m2; rewrite SuccNat2Pos.id_succ; auto.
  unfold Zpower_nat; auto.
Qed.

(* skipped *)
Lemma Zpower_pos_powerRZ :
  forall n m, IZR (Z.pow_pos n m) = IZR n ^Z Zpos m.
Proof.
  intros.
  rewrite Zpower_pos_nat; simpl.
  induction (Pos.to_nat m).
  easy.
  unfold Zpower_nat; simpl.
  rewrite mult_IZR.
  now rewrite <- IHn0.
Qed.

(* skipped *)
Lemma powerRZ_lt : forall (x:R) (z:Z), R0 < x -> R0 < x ^Z z.
Proof.
  intros x z; case z; simpl; auto with real.
Qed.
Hint Resolve powerRZ_lt: real.

(* skipped *)
Lemma powerRZ_le : forall (x:R) (z:Z), R0 < x -> R0 <= x ^Z z.
Proof.
  intros x z H'; apply Rlt_le; auto with real.
Qed.
Hint Resolve powerRZ_le: real.

(* skipped *)
Lemma Zpower_nat_powerRZ_absolu :
  forall n m:Z, (0 <= m)%Z -> IZR (Zpower_nat n (Z.abs_nat m)) = IZR n ^Z m.
Proof.
  intros n m; case m; simpl; auto with zarith.
  intros p H'; elim (Pos.to_nat p); simpl; auto with zarith.
  intros n0 H'0; rewrite <- H'0; simpl; auto with zarith.
  rewrite <- mult_IZR; auto.
  intros p H'; absurd (0 <= Zneg p)%Z; auto with zarith.
Qed.

(* skipped *)
Lemma powerRZ_R1 : forall n:Z, R1 ^Z n = R1.
Proof.
  intros n; case n; simpl; auto.
  intros p; elim (Pos.to_nat p); simpl; auto; intros n0 H'; rewrite H'.
    rewrite Rmult_1_r.
reflexivity.
  intros p; elim (Pos.to_nat p); simpl.
  exact Rinv_1.
  intros n1 H'; rewrite Rinv_mult_distr; try rewrite Rinv_1; try rewrite H';
    auto with real.
Qed.

Local Open Scope Z_scope.

(* skipped *)
Lemma pow_powerRZ (r : R) (n : nat) :
  (r ^ n)%R = powerRZ r (Z_of_nat n).
Proof.
  induction n; [easy|simpl].
  now rewrite SuccNat2Pos.id_succ.
Qed.

(* skipped *)
Lemma powerRZ_ind (P : Z -> R -> R -> Prop) :
  (forall x, P 0 x R1) ->
  (forall x n, P (Z.of_nat n) x (x ^ n)%R) ->
  (forall x n, P ((-(Z.of_nat n))%Z) x (Rinv (x ^ n))) ->
  forall x (m : Z), P m x (powerRZ x m)%R.
Proof.
  intros ? ? ? x m.
  destruct (intP m) as [Hm|n Hm|n Hm].
  - easy.
  - now rewrite <- pow_powerRZ.
  - unfold powerRZ.
    destruct n as [|n]; [ easy |].
    rewrite Nat2Z.inj_succ, <- Zpos_P_of_succ_nat, Pos2Z.opp_pos.
    now rewrite <- Pos2Z.opp_pos, <- positive_nat_Z.
Qed.

(* skipped *)
Lemma powerRZ_inv x alpha : (x <> R0)%R -> powerRZ (/ x) alpha = Rinv (powerRZ x alpha).
Proof.
  intros; destruct (intP alpha).
  - now simpl; rewrite Rinv_1.
  - now rewrite <-!pow_powerRZ, ?Rinv_pow, ?pow_powerRZ.
  - unfold powerRZ.
    destruct (- n).
    + now rewrite Rinv_1.
    + now rewrite Rinv_pow.
    + now rewrite <-Rinv_pow.
Qed.

(* skipped *)
Lemma powerRZ_neg x : forall alpha, x <> R0 -> powerRZ x (- alpha) = powerRZ (/ x) alpha.
Proof.
  intros [|n|n] H ; simpl.
  - easy.
  - now rewrite Rinv_pow.
  - rewrite Rinv_pow by now apply Rinv_neq_0_compat.
    now rewrite Rinv_involutive.
Qed.

(* skipped *)
Lemma powerRZ_mult_distr :
  forall m x y, ((Z.le Z0 m)%Z \/
		(x * y <> R0)%R) ->
           (powerRZ (x*y) m = powerRZ x m * powerRZ y m)%R.
Proof.
  intros m x0 y0 Hmxy.
  destruct (intP m) as [ | | n Hm ].
  - now simpl; rewrite Rmult_1_l.
  - now rewrite <- !pow_powerRZ, Rpow_mult_distr.
  - destruct Hmxy as [H|H].
    + assert(m = 0) as -> by now omega.
      now rewrite <- Hm, Rmult_1_l.
    + assert(x0 <> R0)%R by now intros ->; apply H; rewrite Rmult_0_l.
      assert(y0 <> R0)%R by now intros ->; apply H; rewrite Rmult_0_r.
      rewrite !powerRZ_neg by assumption.
      rewrite Rinv_mult_distr by assumption.
      now rewrite <- !pow_powerRZ, Rpow_mult_distr.
Qed.

End PowerRZ.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : XR_scope.

Definition decimal_exp (r:R) (z:Z) : R := (r * (IZR 10) ^Z z).


Fixpoint sum_nat_f_O (f:nat -> nat) (n:nat) : nat :=
  match n with
    | O => f 0%nat
    | S n' => (sum_nat_f_O f n' + f (S n'))%nat
  end.

Definition sum_nat_f (s n:nat) (f:nat -> nat) : nat :=
  sum_nat_f_O (fun x:nat => f (x + s)%nat) (n - s).

Definition sum_nat_O (n:nat) : nat := sum_nat_f_O (fun x:nat => x) n.

Definition sum_nat (s n:nat) : nat := sum_nat_f s n (fun x:nat => x).

Fixpoint sum_f_R0 (f:nat -> R) (N:nat) : R :=
  match N with
    | O => f 0%nat
    | S i => sum_f_R0 f i + f (S i)
  end.

Definition sum_f (s n:nat) (f:nat -> R) : R :=
  sum_f_R0 (fun x:nat => f (x + s)%nat) (n - s).

Definition fGP (x:R) (n : nat) := x ^n.

Lemma GP_finite :
  forall (x:R) (n:nat),
    sum_f_R0 (fGP x) n * (x - R1) = x ^ (n + 1) - R1.
Proof.
  intros x n.
  pose (f:=fun k => x^k).
  fold f.
  induction n as [ | n i].
  { simpl. rewrite Rmult_1_l. rewrite Rmult_1_r. reflexivity. }
  {
    simpl.
    unfold fGP at 2.
    rewrite Rmult_plus_distr_r.
    rewrite i.
    unfold Rminus.
    rewrite Rmult_plus_distr_l.
    rewrite <- Ropp_mult_distr_r.
    rewrite Rmult_1_r.
    rewrite pow_add.
    simpl.
    rewrite Rmult_1_r.
    repeat (rewrite Rplus_assoc).
    rewrite Rplus_comm at 1.
    repeat (rewrite Rplus_assoc).
    rewrite (Rmult_comm x (x^n)).
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    rewrite Rplus_comm.
    apply Rplus_eq_compat_r.
    rewrite Rmult_comm.
    reflexivity.
  }
Qed.

Definition fTR (f : nat -> R) (n:nat) := Rabs (f n).

Lemma sum_f_R0_triangle :
  forall (f:nat -> R) (n:nat),
    Rabs (sum_f_R0 f n) <= sum_f_R0 (fTR f) n.
Proof.
  intros f n.
  induction n as [ | n i ].
  { simpl. unfold fTR. right. reflexivity. }
  {
    simpl.
    pose (a:=sum_f_R0 f n).
    fold a in i.
    pose (b:=sum_f_R0 (fTR f) n).
    fold b in i. fold b.
    fold a.
    pose (c:= f (S n)).
    fold c.
    apply Rle_trans with (Rabs a + Rabs c).
    apply Rabs_triang.
    apply Rplus_le_compat.
    exact i.
    unfold c. unfold fTR. right. reflexivity.
  }
Qed.

Definition R_dist (x y:R) : R := Rabs (x - y).

Lemma R_dist_pos : forall x y:R, R0 <= R_dist x y .
Proof.
  intros x y.
  unfold R_dist.
  apply Rabs_pos.
Qed.

Lemma R_dist_sym : forall x y:R, R_dist x y = R_dist y x.
Proof.
  intros x y.
  unfold R_dist.
  rewrite Rabs_minus_sym.
  reflexivity.
Qed.

Lemma R_dist_refl : forall x y:R, R_dist x y = R0 <-> x = y.
Proof.
  intros x y.
  split.
  {
    intro eq.
    unfold R_dist in eq.
    unfold Rabs in eq.
    unfold Rminus in eq.
    destruct (Rcase_abs (x + - y)).
    {
      apply Rplus_eq_reg_r with (-y).
      rewrite Rplus_opp_r.
      rewrite <- Ropp_0.
      rewrite <- eq.
      rewrite Ropp_involutive.
      reflexivity.
    }
    {
      apply Rplus_eq_reg_r with (-y).
      rewrite Rplus_opp_r.
      rewrite eq.
      reflexivity.
    }
  }
  { intro eq. subst y. unfold R_dist. unfold Rminus. rewrite Rplus_opp_r. rewrite Rabs_R0. reflexivity. }
Qed.

Lemma R_dist_eq : forall x:R, R_dist x x = R0.
Proof.
  intros x.
  unfold R_dist.
  unfold Rminus.
  rewrite Rplus_opp_r.
  rewrite Rabs_R0.
  reflexivity.
Qed.

Lemma R_dist_tri : forall x y z:R, R_dist x y <= R_dist x z + R_dist z y.
Proof.
  intros x y z.
  unfold R_dist.
  unfold Rminus.
  pattern x at 1;rewrite <- Rplus_0_r.
  rewrite <- Rplus_opp_l with z.
  rewrite Rplus_assoc.
  rewrite Rplus_assoc.
  rewrite <- (Rplus_assoc x).
  apply Rle_trans with (Rabs (x+-z) + Rabs (z+-y)).
  apply Rabs_triang.
  right.
  reflexivity.
Qed.

Lemma R_dist_plus :
  forall a b c d:R, R_dist (a + c) (b + d) <= R_dist a b + R_dist c d.
Proof.
  intros a b c d.
  unfold R_dist.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Rplus_assoc.
  rewrite (Rplus_comm c).
  rewrite Rplus_assoc.
  rewrite (Rplus_comm _ c).
  rewrite <- (Rplus_assoc a).
  apply Rabs_triang.
Qed.

Lemma R_dist_mult_l : forall a b c,
  R_dist (a * b) (a * c) = Rabs a * R_dist b c.
Proof.
  intros a b c.
  unfold R_dist at 1.
  unfold Rminus.
  rewrite Ropp_mult_distr_r.
  rewrite <- Rmult_plus_distr_l.
  fold (b-c).
  rewrite Rabs_mult.
  fold (R_dist b c).
  reflexivity.
Qed.




Definition infinite_sum (s:nat -> R) (l:R) : Prop :=
  forall eps:R,
    R0 < eps ->
    exists N : nat,
      (forall n:nat, (n >= N)%nat -> R_dist (sum_f_R0 s n) l < eps).

Notation infinit_sum := infinite_sum (only parsing).
