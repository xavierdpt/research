Require Export ArithRing.

Require Import Rbase.
Require Export Rpow_def.
Require Export R_Ifp.
Require Export Rbasic_fun.
Require Export R_sqr.
Require Export SplitAbsolu.
Require Export SplitRmult.
Require Export ArithProp.
Require Import Omega.
Require Import Zpower.
Local Open Scope nat_scope.
Local Open Scope R_scope.

Lemma INR_fact_neq_0 : forall n:nat, INR (fact n) <> 0.
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

Infix "^" := pow : R_scope.

Lemma pow_O : forall x:R, x ^ 0 = 1.
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

Lemma pow_nonzero : forall (x:R) (n:nat), x <> 0 -> x ^ n <> 0.
Proof.
  intro. simple induction n. simpl.
  intro. red. intro. apply R1_neq_R0. assumption.
  intros. red. intro. elim (Rmult_integral x (x ^ n0) H1).
  intro. auto.
  apply H. assumption.
Qed.

Hint Resolve pow_O pow_1 pow_add pow_nonzero: real.

Lemma pow_RN_plus :
  forall (x:R) (n m:nat), x <> 0 -> x ^ n = x ^ (n + m) * / x ^ m.
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

Lemma pow_lt : forall (x:R) (n:nat), 0 < x -> 0 < x ^ n.
Proof.
  intros x n h.
  induction n as [ | n i ].
  simpl. apply Rlt_0_1.
  simpl.
  rewrite <- Rmult_0_r with 0.
  apply Rmult_le_0_lt_compat.
  right;reflexivity.
  right;reflexivity.
  assumption.
  assumption.
Qed.
Hint Resolve pow_lt: real.

Lemma Rlt_pow_R1 : forall (x:R) (n:nat), 1 < x -> (0 < n)%nat -> 1 < x ^ n.
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
      rewrite <- Rmult_1_l with 1.
      apply Rlt_trans with (x * 1).
      { rewrite Rmult_1_r. rewrite Rmult_1_r. exact hx. }
      {
        simpl.
        apply Rmult_lt_compat_l.
        {
          apply Rlt_trans with 1.
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

Lemma Rlt_pow : forall (x:R) (n m:nat), 1 < x -> (n < m)%nat -> x ^ n < x ^ m.
Proof.
  intros x n.
  induction n as [ | n i ].
  { simpl. intros m hx hm. apply Rlt_pow_R1. exact hx. exact hm. }
  {
    destruct m.
    { simpl. intros hx hn. inversion hn. }
    { intros hx hnm. unfold lt in hnm. apply le_S_n in hnm.
      simpl. apply Rmult_lt_compat_l.
      apply Rlt_trans with 1. apply Rlt_0_1. exact hx.
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

Lemma poly : forall (n:nat) (x:R), 0 < x -> 1 + INR n * x <= (1 + x) ^ n.
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
      pose (l:= 1 + INR (S n) * x).
      fold l in i.
      rewrite <- Rplus_assoc.
      fold l.
      pose (r:= (1+x)^(S n)).
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
            pattern 1 at 1;rewrite <- Rplus_0_r.
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
    Rabs x > 1 -> (m <= n)%nat -> Rabs (x ^ m) <= Rabs (x ^ n).
Proof.
  intros x m n hx hmn.

  unfold Rabs in hx. destruct (Rcase_abs x).
  {
    apply Rgt_lt in hx.
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
        exfalso. apply Rlt_irrefl with 0. apply Rlt_trans with x;assumption.
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
      apply Rgt_lt in hx.
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
          exfalso. apply Rlt_irrefl with 0. apply Rlt_trans with x;assumption.
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
      exfalso. apply Rgt_lt in hx. apply Rlt_irrefl with 1. apply Rlt_trans with 0.
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

Lemma XD_INR_Rge : forall r:R, exists n:nat, INR n >= r.
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
      apply Rgt_trans with (IZR (Z.neg p)).
      {
        apply Rlt_gt.
        apply IZR_lt.
        apply Pos2Z.neg_lt_pos.
      }
      { exact agt. }
    }
  }
Qed.

Lemma Pow_x_infinity :
  forall x:R,
    Rabs x > 1 ->
    forall b:R,
      exists N : nat, (forall n:nat, (n >= N)%nat -> Rabs (x ^ n) >= b).
Proof.
  intros.
  pose (exp := b * / (Rabs x -1)).
  destruct (archimed exp) as [H0 H1].
  clear H1.
  {
    destruct (XD_INR_Rge exp) as [x0 H1].
    exists x0.
    intros n H2.
    apply Rge_trans with (Rabs (x ^ x0)).
    {
      apply Rle_ge.
      apply Power_monotonic.
      { exact H. }
      { unfold ge in H2. exact H2. }
    }
    {
      rewrite <- RPow_abs.
      rewrite <- Rplus_0_l with (Rabs x).
      rewrite <- Rplus_opp_r with 1.
      rewrite Rplus_assoc.
      rewrite (Rplus_comm _ (Rabs x)).
      fold (Rabs x - 1).
      apply Rge_trans with (1 + INR x0 * (Rabs x - 1)).
      {
        apply Rle_ge.
        apply poly.
        apply Rgt_lt.
        apply Rgt_minus.
        exact H.
      }
      {
        apply Rge_trans with (INR x0 * (Rabs x - 1)).
        {
          apply Rle_ge.
          apply Rlt_le.
          rewrite (Rplus_comm 1).
          pattern (INR x0 * (Rabs x - 1)) at 1;rewrite <- Rplus_0_r.
          apply Rplus_lt_compat_l.
          apply Rlt_0_1.
        }
        {
          rewrite <- Rmult_1_r with b.
          pattern 1 at 2;rewrite <- Rinv_l with (Rabs x - 1).
          rewrite <- Rmult_assoc.
          fold (b / (Rabs x - 1)).
          {
            apply Rmult_ge_compat_r.
            {
              apply Rge_minus.
              unfold Rge.
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
            apply Rgt_minus.
            exact H.
          }
        }
      }
    }
  }
Qed.

Lemma pow_ne_zero : forall n:nat, n <> 0%nat -> 0 ^ n = 0.
Proof.
  intros n h.
  destruct n.
  { exfalso. apply h. reflexivity. }
  { simpl. rewrite Rmult_0_l. reflexivity. }
Qed.

Lemma Rinv_pow : forall (x:R) (n:nat), x <> 0 -> / x ^ n = (/ x) ^ n.
Proof.
  intros x n h.
  induction n as [ | n i].
  simpl. rewrite Rinv_1. reflexivity.
  simpl. rewrite Rinv_mult_distr. rewrite i. reflexivity.
  exact h.
  apply pow_nonzero. exact h.
Qed.

(* stopped here *)

Lemma pow_lt_1_zero :
  forall x:R,
    Rabs x < 1 ->
    forall y:R,
      0 < y ->
      exists N : nat, (forall n:nat, (n >= N)%nat -> Rabs (x ^ n) < y).
Proof.
  intros x H y hy.
  destruct (Req_dec x 0) as [hz | hnz]. (* x = 0 \/ x <> 0 *)
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
    assert (hadx : Rabs (/ x) > 1).
    {
      rewrite <- (Rinv_involutive 1).
      { 
        rewrite Rabs_Rinv.
        {
          unfold Rgt.
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
    specialize (hpow (/ y + 1)).
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
      unfold Rgt.
      exact hy.
    }
  }
Qed.

Lemma pow_R1 : forall (r:R) (n:nat), r ^ n = 1 -> Rabs r = 1 \/ n = 0%nat.
Proof.
  intros r n h.
  case (Req_dec (Rabs r) 1).
  {
    intro hr. left. exact hr.
  }
  {
    intros hr.
    destruct (Rdichotomy _ _ hr)as [ hrlt | hrgt ].
    {
      generalize h.
      {
        destruct n as [ | n ].
        { auto. }
        {
          intros hrsn.
          {
            cut (r <> 0).
            {
              intros hrnz.
              cut (Rabs r <> 0); [ intros Eq2 | apply Rabs_no_R0 ].
              {
                absurd (Rabs (/ r) ^ 0 < Rabs (/ r) ^ S n).
                {
                  replace (Rabs (/ r) ^ S n) with 1.
                  {
                    simpl.
                    apply Rlt_irrefl.
                  }
                  rewrite Rabs_Rinv; auto.
                  {
                    rewrite <- Rinv_pow.
                    {
                      rewrite RPow_abs.
                      {
                        rewrite hrsn.
                        rewrite Rabs_right.
                        {
                          auto with real rorders.
                        }
                        {
                          auto with real rorders.
                        }
                      }
                    }
                    {
                      auto.
                    }
                  }
                }
                {
                  apply Rlt_pow. 
                  {
                    rewrite Rabs_Rinv.
                    apply Rmult_lt_reg_l with (Rabs r).
                    {
                      case (Rabs_pos r).
                      {
                        auto.
                      }
                      {
                        intros hz.
                        case Eq2.
                        auto.
                      }
                    }
                    {
                      rewrite Rmult_1_r.
                      rewrite Rinv_r.
                      {
                        auto with real.
                      }
                      {
                        auto with real.
                      }
                    }
                    {
                      auto.
                    }
                  }
                  {
                    auto with arith.
                  }
                }
              }
              {
                auto.
              }
            }
            {
              red.
              intro.
              absurd (r ^ S n = 1).
              {
                simpl.
                rewrite H.
                rewrite Rmult_0_l.
                auto with real.
              }
              {
                auto.
              }
            }
          }
        }
      }
    }
    {
      generalize h.
      destruct n as [ | n ].
      {
        auto.
      }
      {
        intros H'0.
        cut (r <> 0); [ intros Eq1 | auto with real ].
        {
          cut (Rabs r <> 0); [ intros Eq2 | apply Rabs_no_R0 ].
          {
            clear H'0.
            exfalso.
            assert (ab: forall P:Prop,  (P -> False) -> P -> False).
            {
              intros. apply H. assumption.
            }
            apply ab with (Rabs r ^ 0 < Rabs r ^ S n).
            {
              repeat rewrite RPow_abs.
              rewrite h.
              simpl.
              apply Rlt_irrefl.
            }
            {
              apply Rlt_pow.
              { exact hrgt. }
              {
                unfold lt.
                apply le_n_S.
                apply le_0_n.
              }
            }
          }
          { exact Eq1. }
        }
        {
          intro hrz.
          subst r.
          simpl in h.
          rewrite Rmult_0_l in h.
          symmetry in h.
          apply R1_neq_R0 in h.
          contradiction.
        }
      }
    }
  }
Qed.

Lemma pow_Rsqr : forall (x:R) (n:nat), x ^ (2 * n) = Rsqr x ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  reflexivity.
  replace (2 * S n)%nat with (S (S (2 * n))).
  replace (x ^ S (S (2 * n))) with (x * x * x ^ (2 * n)).
  rewrite Hrecn; reflexivity.
  simpl; ring.
  ring.
Qed.

Lemma pow_le : forall (a:R) (n:nat), 0 <= a -> 0 <= a ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  simpl; left; apply Rlt_0_1.
  simpl; apply Rmult_le_pos; assumption.
Qed.

(**********)
Lemma pow_1_even : forall n:nat, (-1) ^ (2 * n) = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  reflexivity.
  replace (2 * S n)%nat with (2 + 2 * n)%nat by ring.
  rewrite pow_add; rewrite Hrecn; simpl; ring.
Qed.

(**********)
Lemma pow_1_odd : forall n:nat, (-1) ^ S (2 * n) = -1.
Proof.
  intro; replace (S (2 * n)) with (2 * n + 1)%nat by ring.
  rewrite pow_add; rewrite pow_1_even; simpl; ring.
Qed.

(**********)
Lemma pow_1_abs : forall n:nat, Rabs ((-1) ^ n) = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  simpl; apply Rabs_R1.
  replace (S n) with (n + 1)%nat; [ rewrite pow_add | ring ].
  rewrite Rabs_mult.
  rewrite Hrecn; rewrite Rmult_1_l; simpl; rewrite Rmult_1_r.
  change (-1) with (-(1)).
  rewrite Rabs_Ropp; apply Rabs_R1.
Qed.

Lemma pow_mult : forall (x:R) (n1 n2:nat), x ^ (n1 * n2) = (x ^ n1) ^ n2.
Proof.
  intros; induction  n2 as [| n2 Hrecn2].
  simpl; replace (n1 * 0)%nat with 0%nat; [ reflexivity | ring ].
  replace (n1 * S n2)%nat with (n1 * n2 + n1)%nat.
  replace (S n2) with (n2 + 1)%nat by ring.
  do 2 rewrite pow_add.
  rewrite Hrecn2.
  simpl.
  ring.
  ring.
Qed.

Lemma pow_incr : forall (x y:R) (n:nat), 0 <= x <= y -> x ^ n <= y ^ n.
Proof.
  intros.
  induction  n as [| n Hrecn].
  right; reflexivity.
  simpl.
  elim H; intros.
  apply Rle_trans with (y * x ^ n).
  do 2 rewrite <- (Rmult_comm (x ^ n)).
  apply Rmult_le_compat_l.
  apply pow_le; assumption.
  assumption.
  apply Rmult_le_compat_l.
  apply Rle_trans with x; assumption.
  apply Hrecn.
Qed.

Lemma pow_R1_Rle : forall (x:R) (k:nat), 1 <= x -> 1 <= x ^ k.
Proof.
  intros.
  induction  k as [| k Hreck].
  right; reflexivity.
  simpl.
  apply Rle_trans with (x * 1).
  rewrite Rmult_1_r; assumption.
  apply Rmult_le_compat_l.
  left; apply Rlt_le_trans with 1; [ apply Rlt_0_1 | assumption ].
  exact Hreck.
Qed.

Lemma Rle_pow :
  forall (x:R) (m n:nat), 1 <= x -> (m <= n)%nat -> x ^ m <= x ^ n.
Proof.
  intros.
  replace n with (n - m + m)%nat.
  rewrite pow_add.
  rewrite Rmult_comm.
  pattern (x ^ m) at 1; rewrite <- Rmult_1_r.
  apply Rmult_le_compat_l.
  apply pow_le; left; apply Rlt_le_trans with 1; [ apply Rlt_0_1 | assumption ].
  apply pow_R1_Rle; assumption.
  rewrite plus_comm.
  symmetry ; apply le_plus_minus; assumption.
Qed.

Lemma pow1 : forall n:nat, 1 ^ n = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  reflexivity.
  simpl; rewrite Hrecn; rewrite Rmult_1_r; reflexivity.
Qed.

Lemma pow_Rabs : forall (x:R) (n:nat), x ^ n <= Rabs x ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  right; reflexivity.
  simpl; destruct (Rcase_abs x) as [Hlt|Hle].
  apply Rle_trans with (Rabs (x * x ^ n)).
  apply RRle_abs.
  rewrite Rabs_mult.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  right; symmetry; apply RPow_abs.
  pattern (Rabs x) at 1; rewrite (Rabs_right x Hle);
    apply Rmult_le_compat_l.
  apply Rge_le; exact Hle.
  apply Hrecn.
Qed.

Lemma pow_maj_Rabs : forall (x y:R) (n:nat), Rabs y <= x -> y ^ n <= x ^ n.
Proof.
  intros; cut (0 <= x).
  intro; apply Rle_trans with (Rabs y ^ n).
  apply pow_Rabs.
  induction  n as [| n Hrecn].
  right; reflexivity.
  simpl; apply Rle_trans with (x * Rabs y ^ n).
  do 2 rewrite <- (Rmult_comm (Rabs y ^ n)).
  apply Rmult_le_compat_l.
  apply pow_le; apply Rabs_pos.
  assumption.
  apply Rmult_le_compat_l.
  apply H0.
  apply Hrecn.
  apply Rle_trans with (Rabs y); [ apply Rabs_pos | exact H ].
Qed.

Lemma Rsqr_pow2 : forall x, Rsqr x = x ^ 2.
Proof.
intros; unfold Rsqr; simpl; rewrite Rmult_1_r; reflexivity.
Qed.


(*******************************)
(** *       PowerRZ            *)
(*******************************)
(*i Due to L.Thery i*)

Section PowerRZ.

Local Coercion Z_of_nat : nat >-> Z.

(* the following section should probably be somewhere else, but not sure where *)
Section Z_compl.

Local Open Scope Z_scope.

(* Provides a way to reason directly on Z in terms of nats instead of positive *)
Inductive Z_spec (x : Z) : Z -> Type :=
| ZintNull : x = 0 -> Z_spec x 0
| ZintPos (n : nat) : x = n -> Z_spec x n
| ZintNeg (n : nat) : x = - n -> Z_spec x (- n).

Lemma intP (x : Z) : Z_spec x x.
Proof.
  destruct x as [|p|p].
  - now apply ZintNull.
  - rewrite <-positive_nat_Z at 2.
    apply ZintPos.
    now rewrite positive_nat_Z.
  - rewrite <-Pos2Z.opp_pos.
    rewrite <-positive_nat_Z at 2.
    apply ZintNeg.
    now rewrite positive_nat_Z.
Qed.

End Z_compl.

Definition powerRZ (x:R) (n:Z) :=
  match n with
    | Z0 => 1
    | Zpos p => x ^ Pos.to_nat p
    | Zneg p => / x ^ Pos.to_nat p
  end.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : R_scope.

Lemma Zpower_NR0 :
  forall (x:Z) (n:nat), (0 <= x)%Z -> (0 <= Zpower_nat x n)%Z.
Proof.
  induction n; unfold Zpower_nat; simpl; auto with zarith.
Qed.

Lemma powerRZ_O : forall x:R, x ^Z 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma powerRZ_1 : forall x:R, x ^Z Z.succ 0 = x.
Proof.
  simpl; auto with real.
Qed.

Lemma powerRZ_NOR : forall (x:R) (z:Z), x <> 0 -> x ^Z z <> 0.
Proof.
  destruct z; simpl; auto with real.
Qed.

Lemma powerRZ_pos_sub (x:R) (n m:positive) : x <> 0 ->
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

Lemma powerRZ_add :
  forall (x:R) (n m:Z), x <> 0 -> x ^Z (n + m) = x ^Z n * x ^Z m.
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

Lemma powerRZ_lt : forall (x:R) (z:Z), 0 < x -> 0 < x ^Z z.
Proof.
  intros x z; case z; simpl; auto with real.
Qed.
Hint Resolve powerRZ_lt: real.

Lemma powerRZ_le : forall (x:R) (z:Z), 0 < x -> 0 <= x ^Z z.
Proof.
  intros x z H'; apply Rlt_le; auto with real.
Qed.
Hint Resolve powerRZ_le: real.

Lemma Zpower_nat_powerRZ_absolu :
  forall n m:Z, (0 <= m)%Z -> IZR (Zpower_nat n (Z.abs_nat m)) = IZR n ^Z m.
Proof.
  intros n m; case m; simpl; auto with zarith.
  intros p H'; elim (Pos.to_nat p); simpl; auto with zarith.
  intros n0 H'0; rewrite <- H'0; simpl; auto with zarith.
  rewrite <- mult_IZR; auto.
  intros p H'; absurd (0 <= Zneg p)%Z; auto with zarith.
Qed.

Lemma powerRZ_R1 : forall n:Z, 1 ^Z n = 1.
Proof.
  intros n; case n; simpl; auto.
  intros p; elim (Pos.to_nat p); simpl; auto; intros n0 H'; rewrite H';
    ring.
  intros p; elim (Pos.to_nat p); simpl.
  exact Rinv_1.
  intros n1 H'; rewrite Rinv_mult_distr; try rewrite Rinv_1; try rewrite H';
    auto with real.
Qed.

Local Open Scope Z_scope.

Lemma pow_powerRZ (r : R) (n : nat) :
  (r ^ n)%R = powerRZ r (Z_of_nat n).
Proof.
  induction n; [easy|simpl].
  now rewrite SuccNat2Pos.id_succ.
Qed.

Lemma powerRZ_ind (P : Z -> R -> R -> Prop) :
  (forall x, P 0 x 1%R) ->
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

Lemma powerRZ_inv x alpha : (x <> 0)%R -> powerRZ (/ x) alpha = Rinv (powerRZ x alpha).
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

Lemma powerRZ_neg x : forall alpha, x <> R0 -> powerRZ x (- alpha) = powerRZ (/ x) alpha.
Proof.
  intros [|n|n] H ; simpl.
  - easy.
  - now rewrite Rinv_pow.
  - rewrite Rinv_pow by now apply Rinv_neq_0_compat.
    now rewrite Rinv_involutive.
Qed.

Lemma powerRZ_mult_distr :
  forall m x y, ((0 <= m)%Z \/ (x * y <> 0)%R) ->
           (powerRZ (x*y) m = powerRZ x m * powerRZ y m)%R.
Proof.
  intros m x0 y0 Hmxy.
  destruct (intP m) as [ | | n Hm ].
  - now simpl; rewrite Rmult_1_l.
  - now rewrite <- !pow_powerRZ, Rpow_mult_distr.
  - destruct Hmxy as [H|H].
    + assert(m = 0) as -> by now omega.
      now rewrite <- Hm, Rmult_1_l.
    + assert(x0 <> 0)%R by now intros ->; apply H; rewrite Rmult_0_l.
      assert(y0 <> 0)%R by now intros ->; apply H; rewrite Rmult_0_r.
      rewrite !powerRZ_neg by assumption.
      rewrite Rinv_mult_distr by assumption.
      now rewrite <- !pow_powerRZ, Rpow_mult_distr.
Qed.

End PowerRZ.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : R_scope.

(*******************************)
(* For easy interface          *)
(*******************************)
(* decimal_exp r z is defined as r 10^z *)

Definition decimal_exp (r:R) (z:Z) : R := (r * 10 ^Z z).


(*******************************)
(** * Sum of n first naturals  *)
(*******************************)
(*********)
Fixpoint sum_nat_f_O (f:nat -> nat) (n:nat) : nat :=
  match n with
    | O => f 0%nat
    | S n' => (sum_nat_f_O f n' + f (S n'))%nat
  end.

(*********)
Definition sum_nat_f (s n:nat) (f:nat -> nat) : nat :=
  sum_nat_f_O (fun x:nat => f (x + s)%nat) (n - s).

(*********)
Definition sum_nat_O (n:nat) : nat := sum_nat_f_O (fun x:nat => x) n.

(*********)
Definition sum_nat (s n:nat) : nat := sum_nat_f s n (fun x:nat => x).

(*******************************)
(** *          Sum             *)
(*******************************)
(*********)
Fixpoint sum_f_R0 (f:nat -> R) (N:nat) : R :=
  match N with
    | O => f 0%nat
    | S i => sum_f_R0 f i + f (S i)
  end.

(*********)
Definition sum_f (s n:nat) (f:nat -> R) : R :=
  sum_f_R0 (fun x:nat => f (x + s)%nat) (n - s).

Lemma GP_finite :
  forall (x:R) (n:nat),
    sum_f_R0 (fun n:nat => x ^ n) n * (x - 1) = x ^ (n + 1) - 1.
Proof.
  intros; induction  n as [| n Hrecn]; simpl.
  ring.
  rewrite Rmult_plus_distr_r; rewrite Hrecn; cut ((n + 1)%nat = S n).
  intro H; rewrite H; simpl; ring.
  omega.
Qed.

Lemma sum_f_R0_triangle :
  forall (x:nat -> R) (n:nat),
    Rabs (sum_f_R0 x n) <= sum_f_R0 (fun i:nat => Rabs (x i)) n.
Proof.
  intro; simple induction n; simpl.
  unfold Rle; right; reflexivity.
  intro m; intro;
    apply
      (Rle_trans (Rabs (sum_f_R0 x m + x (S m)))
        (Rabs (sum_f_R0 x m) + Rabs (x (S m)))
        (sum_f_R0 (fun i:nat => Rabs (x i)) m + Rabs (x (S m)))).
  apply Rabs_triang.
  rewrite Rplus_comm;
    rewrite (Rplus_comm (sum_f_R0 (fun i:nat => Rabs (x i)) m) (Rabs (x (S m))));
      apply Rplus_le_compat_l; assumption.
Qed.

(*******************************)
(** *     Distance  in R       *)
(*******************************)

(*********)
Definition R_dist (x y:R) : R := Rabs (x - y).

(*********)
Lemma R_dist_pos : forall x y:R, R_dist x y >= 0.
Proof.
  intros; unfold R_dist; unfold Rabs; case (Rcase_abs (x - y));
    intro l.
  unfold Rge; left; apply (Ropp_gt_lt_0_contravar (x - y) l).
  trivial.
Qed.

(*********)
Lemma R_dist_sym : forall x y:R, R_dist x y = R_dist y x.
Proof.
  unfold R_dist; intros; split_Rabs; try ring.
  generalize (Ropp_gt_lt_0_contravar (y - x) Hlt0); intro;
    rewrite (Ropp_minus_distr y x) in H; generalize (Rlt_asym (x - y) 0 Hlt);
      intro; unfold Rgt in H; exfalso; auto.
  generalize (minus_Rge y x Hge0); intro; generalize (minus_Rge x y Hge); intro;
    generalize (Rge_antisym x y H0 H); intro; rewrite H1;
      ring.
Qed.

(*********)
Lemma R_dist_refl : forall x y:R, R_dist x y = 0 <-> x = y.
Proof.
  unfold R_dist; intros; split_Rabs; split; intros.
  rewrite (Ropp_minus_distr x y) in H; symmetry;
    apply (Rminus_diag_uniq y x H).
  rewrite (Ropp_minus_distr x y); generalize (eq_sym H); intro;
    apply (Rminus_diag_eq y x H0).
  apply (Rminus_diag_uniq x y H).
  apply (Rminus_diag_eq x y H).
Qed.

Lemma R_dist_eq : forall x:R, R_dist x x = 0.
Proof.
  unfold R_dist; intros; split_Rabs; intros; ring.
Qed.

(***********)
Lemma R_dist_tri : forall x y z:R, R_dist x y <= R_dist x z + R_dist z y.
Proof.
  intros; unfold R_dist; replace (x - y) with (x - z + (z - y));
    [ apply (Rabs_triang (x - z) (z - y)) | ring ].
Qed.

(*********)
Lemma R_dist_plus :
  forall a b c d:R, R_dist (a + c) (b + d) <= R_dist a b + R_dist c d.
Proof.
  intros; unfold R_dist;
    replace (a + c - (b + d)) with (a - b + (c - d)).
  exact (Rabs_triang (a - b) (c - d)).
  ring.
Qed.

Lemma R_dist_mult_l : forall a b c,
  R_dist (a * b) (a * c) = Rabs a * R_dist b c.
Proof.
unfold R_dist. 
intros a b c; rewrite <- Rmult_minus_distr_l, Rabs_mult; reflexivity.
Qed.

(*******************************)
(** *     Infinite Sum          *)
(*******************************)
(*********)
Definition infinite_sum (s:nat -> R) (l:R) : Prop :=
  forall eps:R,
    eps > 0 ->
    exists N : nat,
      (forall n:nat, (n >= N)%nat -> R_dist (sum_f_R0 s n) l < eps).

(** Compatibility with previous versions *)
Notation infinit_sum := infinite_sum (only parsing).
