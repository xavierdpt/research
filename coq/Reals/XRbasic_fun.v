Require Import XRbase.
Require Import XR_Ifp.
Local Open Scope XR_scope.

Implicit Type r : R.

Definition Rmin (x y:R) : R :=
  match Rle_dec x y with
    | left _ => x
    | right _ => y
  end.

Lemma Rmin_case : forall r1 r2 (P:R -> Type), P r1 -> P r2 -> P (Rmin r1 r2).
Proof.
  intros x y p px py.
  unfold Rmin.
  destruct (Rle_dec x y) as [ le | nle ].
  exact px.
  exact py.
Qed.

Lemma Rmin_case_strong : forall r1 r2 (P:R -> Type), 
  (r1 <= r2 -> P r1) -> (r2 <= r1 -> P r2) -> P (Rmin r1 r2).
Proof.
  intros x y p hxy hyx.
  unfold Rmin.
  destruct (Rle_dec x y) as [ le | nle ].
  apply hxy. exact le.
  apply hyx.
  left.
  apply Rnot_le_lt.
  exact nle.
Qed.

Lemma Rmin_Rgt_l : forall r1 r2 r, r < Rmin r1 r2 -> r < r1 /\ r < r2.
Proof.
  intros x y z h.
  unfold Rmin in h.
  destruct (Rle_dec x y).
  {
    split.
    { exact h. }
    { destruct r as [ lt | eq ].
      { apply Rlt_trans with x. exact h. exact lt. }
      { subst x. exact h. }
    }
  }
  { apply Rnot_le_lt in n. split.
    { apply Rlt_trans with y. exact h. exact n. }
    { exact h. }
  }
Qed.

Lemma Rmin_Rgt_r : forall r1 r2 r, r < r1 /\ r < r2 -> r < Rmin r1 r2.
Proof.
  intros x y z [hx hy].
  unfold Rmin.
  destruct (Rle_dec x y) as [ h | h ].
  exact hx. exact hy.
Qed.

Lemma Rmin_Rgt : forall r1 r2 r, r < Rmin r1 r2 <-> r < r1 /\ r < r2.
Proof.
  intros x y z.
  split.
  { intro h. apply Rmin_Rgt_l. exact h. }
  { intro h. apply Rmin_Rgt_r. exact h. }
Qed.

Lemma Rmin_l : forall x y:R, Rmin x y <= x.
Proof.
  intros x y.
  unfold Rmin.
  destruct (Rle_dec x y) as [ h | h ].
  right. reflexivity.
  left. apply Rnot_le_lt. exact h.
Qed.

Lemma Rmin_r : forall x y:R, Rmin x y <= y.
Proof.
  intros x y.
  unfold Rmin.
  destruct (Rle_dec x y).
  exact r.
  right. reflexivity.
Qed.

Lemma Rmin_left : forall x y, x <= y -> Rmin x y = x.
Proof.
  intros x y h.
  apply Rmin_case_strong.
  intro same. reflexivity.
  intro converse.
  apply Rle_antisym. exact converse. exact h.
Qed.

Lemma Rmin_right : forall x y, y <= x -> Rmin x y = y.
Proof.
  intros x y h.
  unfold Rmin.
  destruct (Rle_dec x y).
  apply Rle_antisym. exact r. exact h.
  reflexivity.
Qed.

Lemma Rle_min_compat_r : forall x y z, x <= y -> Rmin x z <= Rmin y z.
Proof.
  intros x y z h.
  apply Rmin_case_strong.
  intro hxz. apply Rmin_case_strong.
  intro hyz. exact h.
  intro hzy. exact hxz.
  intro hzx. apply Rmin_case_strong.
  intro hyz. apply Rle_trans with x. exact hzx. exact h.
  intro hzy. right. reflexivity.
Qed.

Lemma Rle_min_compat_l : forall x y z, x <= y -> Rmin z x <= Rmin z y.
Proof.
  intros x y z hxy.
  apply Rmin_case_strong.
  {
    intro hzx. apply Rmin_case_strong.
    {
      intro hzy. right. reflexivity.
    }
    {
      intro hyz. apply Rle_trans with x. exact hzx. exact hxy.
    }
  }
  {
    intro hxz. apply Rmin_case_strong.
    {
      intro hzy. exact hxz.
    }
    {
      intro hyz. exact hxy.
    }
  }
Qed.

Lemma Rmin_comm : forall x y:R, Rmin x y = Rmin y x.
Proof.
  intros x y.
  apply Rmin_case_strong.
  {
    intro hxy. apply Rmin_case_strong.
    {
      intro hyx. apply Rle_antisym. exact hxy. exact hyx.
    }
    {
      intro hxy'. reflexivity.
    }
  }
  {
    intro hyx. apply Rmin_case_strong.
    {
      intro hyx'. reflexivity.
    }
    {
      intro hxy. apply Rle_antisym. exact hyx. exact hxy.
    }
  }
Qed.

Lemma Rmin_stable_in_posreal : forall x y:posreal, R0 < Rmin x y.
Proof.
  intros x y.
  apply Rmin_case.
  apply cond_pos.
  apply cond_pos.
Qed.

Lemma Rmin_pos : forall x y:R, R0 < x -> R0 < y -> R0 < Rmin x y.
Proof.
  intros x y hx hy.
  apply Rmin_case.
  exact hx.
  exact hy.
Qed.

Lemma Rmin_glb : forall x y z:R, z <= x -> z <= y -> z <= Rmin x y.
Proof.
  intros x y z hzx hzy.
  apply Rmin_case.
  exact hzx.
  exact hzy.
Qed.

Lemma Rmin_glb_lt : forall x y z:R, z < x -> z < y -> z < Rmin x y.
Proof.
  intros x y z hzx hzy.
  apply Rmin_case.
  exact hzx. exact hzy.
Qed.

Definition Rmax (x y:R) : R :=
  match Rle_dec x y with
    | left _ => y
    | right _ => x
  end.

Lemma Rmax_case : forall r1 r2 (P:R -> Type), P r1 -> P r2 -> P (Rmax r1 r2).
Proof.
  intros x y p px py.
  unfold Rmax. destruct (Rle_dec x y) as [ h | h ].
  exact py. exact px.
Qed.

Lemma Rmax_case_strong : forall r1 r2 (P:R -> Type),
  (r2 <= r1 -> P r1) -> (r1 <= r2 -> P r2) -> P (Rmax r1 r2).
Proof.
  intros x y p px py.
  unfold Rmax. destruct (Rle_dec x y) as [ h | h ].
  apply py. exact h.
  apply px.
  apply Rlt_le. apply Rnot_le_lt. exact h.
Qed.

Lemma Rmax_Rle : forall r1 r2 r, r <= Rmax r1 r2 <-> r <= r1 \/ r <= r2.
Proof.
  intros x y z.
  split.
  {
    intro h. unfold Rmax in h. destruct (Rle_dec x y) as [ h' | h' ].
    right. exact h.
    left. exact h.
  }
  {
    intros [ hzx | hzy ].
    apply Rmax_case_strong.
    {
      intro hyx. exact hzx.
    }
    {
      intro hxy. apply Rle_trans with x. exact hzx. exact hxy.
    }
    apply Rmax_case_strong.
    { intro yx. apply Rle_trans with y. exact hzy. exact yx. }
    { intro hxy. exact hzy. }
  }
Qed.

Lemma Rmax_comm : forall x y:R, Rmax x y = Rmax y x.
Proof.
  intros x y.
  apply Rmax_case_strong;apply Rmax_case_strong;intros.
  apply Rle_antisym;assumption.
  reflexivity.
  reflexivity.
  apply Rle_antisym;assumption.
Qed.

Notation RmaxSym := Rmax_comm (only parsing).

Lemma Rmax_l : forall x y:R, x <= Rmax x y.
Proof.
  intros x y.
  apply Rmax_case_strong.
  intro. right. reflexivity.
  intro;assumption.
Qed.

Lemma Rmax_r : forall x y:R, y <= Rmax x y.
Proof.
  intros x y.
  apply Rmax_case_strong.
  intro;assumption.
  intro. right. reflexivity.
Qed.

Notation RmaxLess1 := Rmax_l (only parsing).
Notation RmaxLess2 := Rmax_r (only parsing).

Lemma Rmax_left : forall x y, y <= x -> Rmax x y = x.
Proof.
  intros x y h.
  apply Rmax_case_strong.
  intro;reflexivity.
  intro h'. apply Rle_antisym;assumption.
Qed.

Lemma Rmax_right : forall x y, x <= y -> Rmax x y = y.
Proof.
  intros x y h.
  apply Rmax_case_strong.
  intro h'. apply Rle_antisym;assumption.
  reflexivity.
Qed.

Lemma Rle_max_compat_r : forall x y z, x <= y -> Rmax x z <= Rmax y z.
Proof.
  intros x y z hxy.
  apply Rmax_case_strong;apply Rmax_case_strong.
  intros hzy hzx. exact hxy.
  intros hyz hzx. apply Rle_trans with y;assumption.
  intros hzy hxz. exact hzy.
  intros hyz hxz. right. reflexivity.
Qed.

Lemma Rle_max_compat_l : forall x y z, x <= y -> Rmax z x <= Rmax z y.
Proof.
  intros x y z hxy.
  apply Rmax_case_strong;apply Rmax_case_strong.
  intros;right;reflexivity.
  intros;assumption.
  intros hyz hzx. apply Rle_trans with y;assumption.
  intros;assumption.
Qed.

Lemma RmaxRmult :
  forall (p q:R) r, R0 <= r -> Rmax (r * p) (r * q) = r * Rmax p q.
Proof.
  intros x y z h.
  apply Rmax_case_strong;apply Rmax_case_strong.
  { intros;reflexivity. }
  {
    intros hxy hyx.
    apply Rle_antisym.
    apply Rmult_le_compat_l.
    exact h. exact hxy. exact hyx.
  }
  {
    intros hyx hxy.
    apply Rle_antisym.
    apply Rmult_le_compat_l.
    exact h. exact hyx. exact hxy.
  }
  { intros;reflexivity. }
Qed.


Lemma Rmax_stable_in_negreal : forall x y:negreal, Rmax x y < R0.
Proof.
  intros x y.
  apply Rmax_case.
  apply cond_neg.
  apply cond_neg.
Qed.

Lemma Rmax_lub : forall x y z:R, x <= z -> y <= z -> Rmax x y <= z.
Proof.
  intros x y z hxz hyz.
  apply Rmax_case;assumption.
Qed.

Lemma Rmax_lub_lt : forall x y z:R, x < z -> y < z -> Rmax x y < z.
Proof.
  intros x y z hxz hyz.
  apply Rmax_case;assumption.
Qed.

Lemma Rmax_Rlt : forall x y z, 
  Rmax x y < z <-> x < z /\ y < z.
Proof.
  intros x y z.
  apply Rmax_case_strong.
  {
    intro hyx. split.
    {
      intro hxz. split.
      { exact hxz. }
      {
        destruct hyx as [ hyx | hyx ].
        apply Rlt_trans with x;assumption.
        subst y. exact hxz.
      }
    }
    {
      intros [ hxz hyz ].
      exact hxz.
    }
  }
  {
    intro hxy.
    split.    
    {
      intro hyz. split.
      {
        destruct hxy as [ hlt | heq ].
        apply Rlt_trans with y;assumption.
        subst y. assumption.
      }
      { assumption. }
    }
    { intros [ hxz hyz ] ; assumption. }
  }
Qed.

Lemma Rmax_neg : forall x y:R, x < R0 -> y < R0 -> Rmax x y < R0.
Proof.
  intros x y hx hy.
  apply Rmax_case;assumption.
Qed.

Lemma Rcase_abs : forall r, {r < R0} + {R0 <= r}.
Proof.
  intro x.
  destruct (total_order_T x R0) as [ [ hlt | heq ] | hgt ].
  left. assumption.
  subst x. right. right. reflexivity.
  right;left;assumption.
Qed.

Definition Rabs r : R :=
  match Rcase_abs r with
    | left _ => - r
    | right _ => r
  end.

Lemma Rabs_R0 : Rabs R0 = R0.
Proof.
  unfold Rabs.
  destruct (Rcase_abs R0).
  rewrite Ropp_0. reflexivity.
  reflexivity.
Qed.

Lemma Rabs_R1 : Rabs R1 = R1.
Proof.
  unfold Rabs.
  destruct (Rcase_abs R1).
  exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with R1. apply Rlt_0_1. assumption.
  reflexivity.
Qed.

Lemma Rabs_no_R0 : forall r, r <> R0 -> Rabs r <> R0.
Proof.
  intros x h eq.
  apply h.
  unfold Rabs in eq.
  destruct (Rcase_abs x).
  apply Rplus_eq_reg_l with (-x).
  rewrite Rplus_opp_l.
  rewrite eq.
  rewrite Rplus_0_l.
  reflexivity.
  exact eq.
Qed.

Lemma Rabs_left : forall r, r < R0 -> Rabs r = - r.
Proof.
  intros x h.
  unfold Rabs. destruct (Rcase_abs x).
  reflexivity.
  destruct r.
  exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x;assumption.
  subst x. rewrite Ropp_0. reflexivity.
Qed.

Lemma Rabs_right : forall r, R0 <= r -> Rabs r = r.
Proof.
  intros x h.
  destruct h as [ h | h ].
  unfold Rabs. destruct (Rcase_abs x).
  exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x;assumption.
  reflexivity.
  subst x.
  exact Rabs_R0.
Qed.

Lemma Rabs_left1 : forall a:R, a <= R0 -> Rabs a = - a.
Proof.
  intros x h.
  destruct h as [ lt | eq ].
  {
    unfold Rabs. destruct (Rcase_abs x).
    reflexivity.
    destruct r as [ lt' | eq' ].
    exfalso. apply Rlt_irrefl with x. apply Rlt_trans with R0;assumption.
    subst x. rewrite Ropp_0. reflexivity.
  }
  subst x. rewrite Ropp_0. exact Rabs_R0.
Qed.

Lemma Rabs_pos : forall x:R, R0 <= Rabs x.
Proof.
  intros x.
  unfold Rabs. destruct (Rcase_abs x).
  left. apply Rplus_lt_reg_l with x. rewrite Rplus_0_r.
  rewrite Rplus_opp_r. exact r.
  exact r.
Qed.

Lemma Rle_abs : forall x:R, x <= Rabs x.
Proof.
  intros x.
  unfold Rabs. destruct (Rcase_abs x).
  left. apply Rlt_trans with R0. exact r.
  apply Rplus_lt_reg_l with x. rewrite Rplus_0_r. rewrite Rplus_opp_r.
  exact r.
  right. reflexivity.
Qed.

Definition RRle_abs := Rle_abs.

Lemma Rabs_le : forall a b, -b <= a <= b -> Rabs a <= b.
Proof.
  intros x y [ hyx hxy ].
  unfold Rabs. destruct (Rcase_abs x).
  apply Rplus_le_reg_r with x.
  rewrite Rplus_opp_l.
  apply Rplus_le_reg_l with (-y).
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  rewrite Rplus_0_r.
  exact hyx.
  exact hxy.
Qed.

Lemma Rabs_pos_eq : forall x:R, R0 <= x -> Rabs x = x.
Proof.
  intros x h.
  destruct h as [ lt | eq ].
  unfold Rabs. destruct (Rcase_abs x).
  exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x;assumption.
  reflexivity.
  subst x. exact Rabs_R0.
Qed.

Lemma Rabs_Rabsolu : forall x:R, Rabs (Rabs x) = Rabs x.
Proof.
  intro x.
  unfold Rabs.
  destruct (Rcase_abs x).
  destruct (Rcase_abs (-x)).
  exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x.
  apply Rplus_lt_reg_l with (-x). rewrite Rplus_opp_l.
  rewrite Rplus_0_r. exact r0. exact r.
  reflexivity.
  destruct (Rcase_abs x).
  destruct r.
  exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x;assumption.
  subst x. rewrite Ropp_0. reflexivity.
  reflexivity.
Qed.

Lemma Rabs_pos_lt : forall x:R, x <> R0 -> R0 < Rabs x.
Proof.
  intros x h.
  unfold Rabs. destruct (Rcase_abs x).
  apply Rplus_lt_reg_l with x.
  rewrite Rplus_0_r.
  rewrite Rplus_opp_r.
  exact r.
  destruct r.
  exact H.
  subst x. exfalso.
  apply h. reflexivity.
Qed.

Lemma Rabs_minus_sym : forall x y:R, Rabs (x - y) = Rabs (y - x).
Proof.
  intros x y.
  unfold Rabs.
  destruct (Rcase_abs (x-y));destruct (Rcase_abs (y-x));
  unfold Rminus;
  repeat (rewrite Ropp_plus_distr);
  repeat (rewrite Ropp_involutive).
  {
    exfalso.
    unfold Rminus in r, r0.
    apply (Rplus_lt_compat_r y) in r.
    rewrite Rplus_assoc in r.
    rewrite Rplus_opp_l in r.
    rewrite Rplus_0_r in r.
    rewrite Rplus_0_l in r.
    apply (Rplus_lt_compat_r x) in r0.
    rewrite Rplus_assoc in r0.
    rewrite Rplus_opp_l in r0.
    rewrite Rplus_0_l in r0.
    rewrite Rplus_0_r in r0.
    apply Rlt_irrefl with x.
    apply Rlt_trans with y;assumption.
  }
  {
    rewrite (Rplus_comm _ y).
    reflexivity.
  }
  {
    rewrite Rplus_comm.
    reflexivity.
  }
  {
    destruct r.
    {
      destruct r0.
      {
        exfalso.
        unfold Rminus in H.
        unfold Rminus in H0.
        apply (Rplus_lt_compat_r y) in H.
        apply (Rplus_lt_compat_r x) in H0.
        repeat (rewrite Rplus_assoc in H, H0).
        rewrite Rplus_opp_l in H, H0.
        rewrite Rplus_0_l in H, H0.
        rewrite Rplus_0_r in H, H0.
        apply Rlt_irrefl with x.
        apply Rlt_trans with y;assumption.
    }
    unfold Rminus in *.
    apply (Rplus_eq_compat_r x) in H0.
    rewrite Rplus_assoc in H0.
    rewrite Rplus_opp_l in H0.
    rewrite Rplus_0_l in H0.
    rewrite Rplus_0_r in H0.
    subst y.
    rewrite Rplus_comm. reflexivity.
  }
  apply (Rplus_eq_compat_r y) in H.
  unfold Rminus in H.
  rewrite Rplus_assoc in H.
  rewrite Rplus_opp_l in H.
  rewrite Rplus_0_r in H.
  rewrite Rplus_0_l in H.
  subst y.
  reflexivity.
  }
Qed.

Lemma Rabs_mult : forall x y:R, Rabs (x * y) = Rabs x * Rabs y.
Proof.
  intros x y.
  unfold Rabs.
  destruct (Rcase_abs x);
  destruct (Rcase_abs y);
  destruct (Rcase_abs (x*y)).
  {
    exfalso.
    apply Rlt_irrefl with (x*y).
    apply Rlt_trans with R0.
    assumption.
    rewrite <- Ropp_involutive with (x*y).
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_mult_distr_r.
    apply Rmult_lt_0_compat.
    apply Rplus_lt_reg_l with x.
    rewrite Rplus_0_r.
    rewrite Rplus_opp_r.
    assumption.
    apply Rplus_lt_reg_l with y.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    assumption.
  }
  {
    rewrite <- Ropp_mult_distr_l.
    rewrite <- Ropp_mult_distr_r.
    rewrite Ropp_involutive.
    reflexivity.
  }
  {
    rewrite Ropp_mult_distr_l.
    reflexivity.
  }
  {
    destruct r1.
    destruct r0.
    exfalso.
    apply Rlt_irrefl with (x*y).
    apply Rlt_trans with R0.
    apply Rplus_lt_reg_l with (- (x*y)).
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    rewrite Ropp_mult_distr_l.
    apply Rmult_lt_0_compat.
    apply Rplus_lt_reg_l with x.
    rewrite Rplus_0_r.
    rewrite Rplus_opp_r.
    assumption.
    assumption.
    assumption.
    subst y. do 2 rewrite Rmult_0_r. reflexivity.
    rewrite <- H. rewrite <- Ropp_mult_distr_l.
    rewrite <- H. rewrite Ropp_0. reflexivity.
  }
  {
    rewrite Ropp_mult_distr_r.
    reflexivity.
  }
  {
    destruct r1.
    destruct r.
    exfalso. apply Rlt_irrefl with (x*y).
    apply Rlt_trans with R0.
    apply Rplus_lt_reg_l with (- (x*y)).
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    rewrite Ropp_mult_distr_r.
    apply Rmult_lt_0_compat.
    assumption.
    apply Rplus_lt_reg_l with y.
    rewrite Rplus_0_r.
    rewrite Rplus_opp_r.
    assumption.
    assumption.
    subst x. do 2 rewrite Rmult_0_l. reflexivity.
    rewrite <- H. rewrite <- Ropp_mult_distr_r.
    rewrite <- H. rewrite Ropp_0. reflexivity.
  }
  {
    destruct r. destruct r0.
    exfalso. apply Rlt_irrefl with (x*y).
    apply Rlt_trans with R0.
    assumption.
    apply Rmult_lt_0_compat.
    assumption.
    assumption.
    subst y. rewrite Rmult_0_r. rewrite Ropp_0. reflexivity.
    subst x. rewrite Rmult_0_l. rewrite Ropp_0. reflexivity.
  }
  { reflexivity. }
Qed.

Lemma Rabs_Rinv : forall r, r <> R0 -> Rabs (/ r) = / Rabs r.
Proof.
  intros x h.
  unfold Rabs.
  destruct (Rcase_abs x);destruct (Rcase_abs (/ x)).
  {
    rewrite Ropp_inv_permute.
    reflexivity.
    assumption.
  }
  {
    destruct r0.
    exfalso.
    apply Rinv_lt_0_compat in r.
    apply Rlt_irrefl with R0.
    apply Rlt_trans with (/ x);assumption.
    rewrite <- H.
    rewrite <- Ropp_inv_permute.
    rewrite <- H.
    rewrite Ropp_0. reflexivity. assumption.
  }
  {
    destruct r.
    exfalso.
    apply Rlt_irrefl with R0.
    apply Rlt_trans with x.
    assumption.
    apply Rinv_lt_0_compat in r0.
    rewrite Rinv_involutive in r0.
    assumption. assumption.
    subst x. exfalso. apply h. reflexivity.
  }
  {
    reflexivity.
  }
Qed.

Lemma Rabs_Ropp : forall x:R, Rabs (- x) = Rabs x.
Proof.
  intro x.
  unfold Rabs.
  destruct (Rcase_abs (-x));
  destruct (Rcase_abs x).
  {
    exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x.
    apply Rplus_lt_reg_l with (-x).
    rewrite Rplus_0_r. rewrite Rplus_opp_l. assumption.
    assumption.
  }
  {
    rewrite Ropp_involutive.
    reflexivity.
  }
  {
    reflexivity.
  }
  {
    destruct r.
    destruct r0.
    exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x.
    assumption.
    apply Rplus_lt_reg_l with (-x). rewrite Rplus_0_r.
    rewrite Rplus_opp_l. assumption.
    subst x. rewrite Ropp_0. reflexivity.
    rewrite <- H. rewrite <- Ropp_involutive with x. rewrite <- H.
    rewrite Ropp_0. reflexivity.
  }
Qed.

Lemma Rabs_triang : forall a b:R, Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  intros x y.
  unfold Rabs.
  destruct (Rcase_abs x);
  destruct (Rcase_abs y);
  destruct (Rcase_abs (x+y)).
  {
    rewrite Ropp_plus_distr. right. reflexivity.
  }
  {
    destruct r1.
    exfalso.
    apply Rlt_irrefl with R0.
    apply Rlt_trans with (x+y).
    assumption.
    rewrite <- Rplus_0_l with R0.
    apply Rplus_lt_compat. assumption. assumption.
    rewrite <- H. rewrite <- Ropp_plus_distr. rewrite <- H.
    rewrite Ropp_0. right. reflexivity.
  }
  {
    rewrite Ropp_plus_distr.
    apply Rplus_le_compat_l.
    apply Rplus_le_reg_r with y.
    rewrite Rplus_opp_l.
    apply Rle_trans with y.
    assumption.
    pattern y at 1;rewrite <- Rplus_0_l with y.
    apply Rplus_le_compat_r. assumption.
  }
  {
    apply Rplus_le_compat_r.
    left.
    apply Rlt_trans with R0. assumption.
    apply Rplus_lt_reg_l with x. rewrite Rplus_opp_r. rewrite Rplus_0_r.
    assumption.
  }
  {
    rewrite Ropp_plus_distr.
    apply Rplus_le_compat_r.
    apply Rle_trans with R0.
    apply Rplus_le_reg_l with x.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    assumption.
    assumption.
  }
  {
    apply Rplus_le_compat_l.
    apply Rle_trans with R0.
    left. assumption.
    left. apply Rplus_lt_reg_r with y.
    rewrite Rplus_0_l. rewrite Rplus_opp_l. assumption.
  }
  {
    rewrite Ropp_plus_distr.
    apply Rplus_le_compat.
    apply Rle_trans with R0.
    apply Rplus_le_reg_l with x.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    assumption.
    assumption.
    apply Rle_trans with R0.
    apply Rplus_le_reg_l with y.
    rewrite Rplus_0_r.
    rewrite Rplus_opp_r.
    assumption.
    assumption.
  }
  {
    right. reflexivity.
  }
Qed.

Lemma Rabs_triang_inv : forall a b:R, Rabs a - Rabs b <= Rabs (a - b).
Proof.
  intros a b.
  unfold Rabs.
  destruct (Rcase_abs a);
  destruct (Rcase_abs b);
  destruct (Rcase_abs (a-b));
  unfold Rminus in *;
  try(rewrite Ropp_plus_distr in *);
  try(rewrite Ropp_involutive in *).
  {
    right. reflexivity.
  }
  {
    destruct r1.
    left. apply Rlt_trans with R0.
    apply Rplus_lt_reg_l with a.
    rewrite <- Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    rewrite Rplus_0_l.
    apply Rplus_lt_reg_r with (-b).
    rewrite Rplus_opp_r. assumption. assumption.
    rewrite <- H. right.
    apply Rplus_eq_reg_l with a.
    apply Rplus_eq_reg_r with (-b).
    repeat (rewrite Rplus_assoc).
    rewrite Rplus_opp_r.
    repeat (rewrite <- Rplus_assoc).
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    rewrite Rplus_0_r.
    rewrite <- H. reflexivity.
  }
  {
    apply Rplus_le_compat_l.
    apply Rle_trans with R0.
    apply Rplus_le_reg_r with b.
    rewrite Rplus_opp_l. rewrite Rplus_0_l. assumption. assumption.
  }
  {
    apply Rplus_le_compat_r.
    destruct r0.
    destruct r1.
    exfalso.
    apply (Rplus_lt_compat_r b) in H0.
    rewrite Rplus_0_l in H0.
    rewrite Rplus_assoc in H0.
    rewrite Rplus_opp_l in H0.
    rewrite Rplus_0_r in H0.
    apply Rlt_irrefl with R0.
    apply Rlt_trans with b.
    assumption. apply Rlt_trans with a.
    assumption. assumption.
    apply (Rplus_eq_compat_r b) in H0.
    rewrite Rplus_assoc in H0.
    rewrite Rplus_opp_l in H0.
    rewrite Rplus_0_r in H0.
    rewrite Rplus_0_l in H0.
    subst b.
    exfalso. apply Rlt_irrefl with R0.
    apply Rlt_trans with a; assumption.
    subst b.
    rewrite Ropp_0 in r1.
    rewrite Rplus_0_r in r1.
    destruct r1.
    exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with a;assumption.
    subst a. exfalso. apply Rlt_irrefl with R0;assumption.
  }
  {
    apply Rplus_le_compat_r.
    apply (Rplus_lt_compat_r b) in r1.
    rewrite Rplus_assoc in r1.
    rewrite Rplus_opp_l in r1.
    rewrite Rplus_0_r in r1.
    rewrite Rplus_0_l in r1.
    destruct r.
    exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with a. assumption.
    apply Rlt_trans with b. assumption. assumption.
    subst a. exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with b;assumption.
  }
  {
    apply Rplus_le_compat_l.
    left. apply Rlt_trans with R0. assumption.
    apply Rplus_lt_reg_l with b. rewrite Rplus_0_r.
    rewrite Rplus_opp_r. assumption.
  }
  {
    destruct r.
    destruct r0.
    apply (Rplus_lt_compat_r b) in r1.
    rewrite Rplus_assoc in r1.
    rewrite Rplus_opp_l in r1.
    rewrite Rplus_0_r in r1.
    rewrite Rplus_0_l in r1.
    left.
    apply Rplus_lt_reg_l with a.
    repeat (rewrite <- Rplus_assoc).
    rewrite Rplus_opp_r. rewrite Rplus_0_l.
    apply Rplus_lt_reg_r with b.
    repeat (rewrite Rplus_assoc).
    rewrite Rplus_opp_l. rewrite Rplus_0_r.
    apply Rplus_lt_compat. assumption. assumption.
    subst b. rewrite Ropp_0 in *. rewrite Rplus_0_r in *.
    exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with a;assumption.
    subst a. rewrite Ropp_0 in *. rewrite Rplus_0_l in *.
    rewrite Rplus_0_l. left.
    apply Rlt_trans with R0. assumption.
    apply Rplus_lt_reg_l with (-b). rewrite Rplus_0_r.
    rewrite Rplus_opp_l. assumption.
  }
  { right. reflexivity. }
Qed.

Lemma Rabs_case : forall x:R, Rabs x = x /\ R0 <= x \/ Rabs x = -x /\ x < R0.
  intro x.
  unfold Rabs. destruct (Rcase_abs x).
  right. split. reflexivity. assumption.
  left. split. reflexivity. assumption.
Qed.

Lemma Rabs_triang_inv2 : forall a b:R, Rabs (Rabs a - Rabs b) <= Rabs (a - b).
Proof.
  intros x y.
  unfold Rminus.
  destruct (Rabs_case x) as [ [ eqx hx ] | [ eqx hx ] ];
  destruct (Rabs_case y) as [ [ eqy hy ] | [ eqy hy ] ].
  {
    rewrite eqx. rewrite eqy.
    right. reflexivity.
  }
  {
    rewrite eqx. rewrite eqy.
    rewrite Ropp_involutive.
    destruct (Rabs_case (x+y)) as [ [ eqxy hxy ] | [ eqxy hxy ] ];
    destruct (Rabs_case (x+-y)) as [ [ eqxym hxym ] | [ eqxym hxym ] ].
    {
      rewrite eqxy. rewrite eqxym.
      apply Rplus_le_compat_l.
      left. apply Rlt_trans with R0. assumption.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      assumption.
    }
    {
      rewrite eqxy;rewrite eqxym.
      rewrite Ropp_plus_distr. rewrite Ropp_involutive.
      apply Rplus_le_compat_r.
      clear eqx eqy eqxy eqxym.
      destruct hx as [ lt | eq ].
      exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x.
      assumption. apply Rlt_trans with y.
      apply Rplus_lt_reg_r with (-y).
      rewrite Rplus_opp_r. assumption.
      assumption.
      subst x. right. rewrite Ropp_0. reflexivity.
    }
    {
      rewrite eqxy;rewrite eqxym.
      rewrite Ropp_plus_distr.
      apply Rplus_le_compat_r.
      apply Rle_trans with R0.
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      assumption. assumption.
    }
    {
      rewrite eqxy;rewrite eqxym.
      rewrite Ropp_plus_distr.
      rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      apply Rplus_le_compat_l.
      clear eqx eqy eqxy eqxym.
      destruct hx as [ hx | hx ].
      exfalso. apply Rlt_irrefl with R0.
      apply Rlt_trans with x. assumption.
      apply Rlt_trans with y.
      apply Rplus_lt_reg_r with (-y).
      rewrite Rplus_opp_r.
      assumption.
      assumption.
      subst x. rewrite Rplus_0_l in *.
      exfalso. apply Rlt_irrefl with y. apply Rlt_trans with R0.
      assumption.
      apply Ropp_lt_cancel.
      rewrite Ropp_0. assumption.
    }
  }
  {
    destruct hy as [ hy | hy ].
    {
      rewrite eqx;rewrite eqy.
      rewrite <- Ropp_plus_distr.
      rewrite Rabs_Ropp.
      destruct (Rabs_case (x+y)) as [ [ eqxy hxy ] | [ eqxy hxy ] ];
      destruct (Rabs_case (x+-y)) as [ [ eqxym hxym ] | [ eqxym hxym ] ].
      {
        rewrite eqxy. rewrite eqxym.
        apply Rplus_le_compat_l.
        clear eqx eqy eqxy eqxym.
        destruct hxym.
        {
          exfalso.
          apply Rlt_irrefl with R0.
          apply Rlt_trans with y.
          assumption.
          apply Rlt_trans with x.
          apply Rplus_lt_reg_r with (-y).
          rewrite Rplus_opp_r. assumption.
          assumption.
        }
        {
          apply (Rplus_eq_compat_r y) in H.
          rewrite Rplus_assoc in H.
          rewrite Rplus_opp_l in H.
          rewrite Rplus_0_l in H.
          rewrite Rplus_0_r in H.
          subst y. exfalso. apply Rlt_irrefl with R0.
          apply Rlt_trans with x;assumption.
        }
      }
      {
        rewrite eqxy;rewrite eqxym.
        rewrite Ropp_plus_distr. rewrite Ropp_involutive.
        apply Rplus_le_compat_r.
        left. apply Rlt_trans with R0.
        assumption. rewrite <- Ropp_0.
        apply Ropp_lt_contravar. assumption.
      }
      {
        rewrite eqxy;rewrite eqxym.
        rewrite Ropp_plus_distr.
        apply Rplus_le_compat_r.
        destruct hxym.
        exfalso. apply Rlt_irrefl with R0.
        apply Rlt_trans with y.
        assumption.
        apply Rlt_trans with x.
        apply Rplus_lt_reg_r with (-y).
        rewrite Rplus_opp_r. assumption.
        assumption.
        apply (Rplus_eq_compat_r y) in H.
        rewrite Rplus_assoc in H.
        rewrite Rplus_opp_l in H.
        rewrite Rplus_0_r in H.
        rewrite Rplus_0_l in H.
        subst x. exfalso. apply Rlt_irrefl with R0.
        apply Rlt_trans with y.
        assumption.
        apply Rlt_trans with (y+y).
        apply Rplus_lt_reg_l with (-y).
        rewrite <- Rplus_assoc.
        rewrite Rplus_opp_l.
        rewrite Rplus_0_l. assumption. assumption.
      }
      {
        rewrite eqxy;rewrite eqxym.
        rewrite Ropp_plus_distr.
        rewrite Ropp_plus_distr.
        rewrite Ropp_involutive.
        apply Rplus_le_compat_l.
        left. apply Rlt_trans with R0.
        rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
        assumption.
      }
    }
    {
      subst y.
      rewrite eqx. rewrite eqy.
      rewrite Ropp_0.
      rewrite Rplus_0_r.
      rewrite Rplus_0_r.
      rewrite Rabs_Ropp.
      right. reflexivity.
    }
  }
  {
    rewrite eqx. rewrite eqy.
    rewrite <- Ropp_plus_distr.
    rewrite Rabs_Ropp.
    right. reflexivity.
  }
Qed.

Lemma Rabs_def1 : forall x a:R, x < a -> - a < x -> Rabs x < a.
Proof.
  intros x a hu hl.
  unfold Rabs. destruct (Rcase_abs x).
  apply Ropp_lt_cancel. rewrite Ropp_involutive. assumption.
  assumption.
Qed.

Lemma Rabs_def2 : forall x a:R, Rabs x < a -> x < a /\ - a < x.
Proof.
  intros x a.
  split.
  unfold Rabs in H. destruct (Rcase_abs x).
  apply Rlt_trans with R0. assumption.
  apply Rlt_trans with (-x).
  apply Ropp_lt_cancel. rewrite Ropp_involutive. rewrite Ropp_0.
  assumption. assumption.
  assumption.
  unfold Rabs in H. destruct (Rcase_abs x).
  apply Ropp_lt_cancel. rewrite Ropp_involutive. assumption.
  destruct r.
  apply Rlt_trans with R0.
  apply Ropp_lt_cancel. rewrite Ropp_involutive. rewrite Ropp_0.
  apply Rlt_trans with x. assumption. assumption. assumption.
  subst x. apply Ropp_lt_cancel. rewrite Ropp_involutive. rewrite Ropp_0.
  assumption.
Qed.

Lemma RmaxAbs :
  forall (p q:R) r, p <= q -> q <= r -> Rabs q <= Rmax (Rabs p) (Rabs r).
Proof.
  intros x y z.
  intros hxy hyz.
  unfold Rabs, Rmax.
  destruct (Rcase_abs y) as [ hy | hy ];
  destruct (Rcase_abs x) as [ hx | hx ];
  destruct (Rcase_abs z) as [ hz | hz ].
  {
    destruct (Rle_dec (-x) (-z)) as [ hxz | hxz ].
    {
      apply Ropp_le_cancel in hxz.
      assert (eq:z=x).
      {
        apply Rle_antisym.
        { assumption. }
        { apply Rle_trans with y;assumption. }
      }
      subst z.
      assert (eq:x=y).
      {
        apply Rle_antisym;assumption.
      }
      subst y.
      right. reflexivity.
    }
    {
      apply Rnot_le_lt in hxz.
      apply Ropp_le_contravar.
      assumption.
    }
  }
  {
    destruct (Rle_dec (-x) z) as [ hxz | hxz ].
    {
      apply Rle_trans with (-x).
      { apply Ropp_le_contravar. assumption. }
      { assumption. }
    }
    {
      apply Rnot_le_lt in hxz.
      apply Ropp_le_contravar.
      assumption.
    }
  }
  {
    destruct (Rle_dec x (-z)) as [ hxz | hxz ].
    {
      apply Ropp_le_contravar.
      apply Rle_trans with x.
      2:assumption.
      apply Rle_trans with (-x).
      { apply Ropp_le_cancel. rewrite Ropp_involutive. assumption. }
      {
        apply Rle_trans with R0.
        2:assumption.
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        assumption.
      }
    }
    {
      apply Rnot_le_lt in hxz.
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rlt_trans with z.
      2:exact hz. clear hz.
      apply Rlt_trans with (-x).
      2:{
        apply Ropp_lt_cancel.
        rewrite Ropp_involutive.
        exact hxz.
      }
      clear hxz.
      apply Ropp_lt_cancel.
      rewrite Ropp_involutive.
      rewrite Ropp_0.
      apply Rle_lt_trans with y.
      { exact hxy. }
      { exact hy. }
    }
  }
  {
    exfalso.
    apply Rlt_irrefl with x.
    apply Rle_lt_trans with y.
    exact hxy.
    clear hxy.
    apply Rlt_le_trans with R0.
    exact hy.
    exact hx.
  }
  {
    destruct (Rle_dec (-x) (-z)) as [ hxz | hxz ].
    {
      apply Ropp_le_cancel in hxz.
      assert (eq : z = x).
      {
        apply Rle_antisym;try assumption.
        apply Rle_trans with y;assumption.
      }
      subst z.
      assert (eq : x = y).
      { apply Rle_antisym; assumption. }
      subst y.
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with x;assumption.
    }
    {
      apply Rnot_le_lt in hxz.
      apply Ropp_lt_cancel in hxz.
      clear hxy.
      clear hx.
      clear hxz.
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with z;try assumption.
      apply Rle_trans with y;assumption.
    }
  }
  {
    destruct (Rle_dec (-x) z) as [ hxz | hxz ].
    { assumption. }
    {
      apply Rnot_le_lt in hxz.
      apply Rle_trans with z.
      exact hyz.
      clear hyz.
      left. exact hxz.
    }
  }
  {
    exfalso.
    apply Rlt_irrefl with R0.
    apply Rle_lt_trans with z.
    2:exact hz.
    clear hz.
    apply Rle_trans with y; assumption.
  }
  {
    destruct (Rle_dec x z) as [ hxz | hxz ].
    { assumption. }
    {
      apply Rnot_le_lt in hxz.
      exfalso.
      apply Rlt_irrefl with z.
      apply Rlt_le_trans with x; try assumption.
      apply Rle_trans with y;assumption.
    }
  }
Qed.

Lemma abs_IZR : forall z, IZR (Z.abs z) = Rabs (IZR z).
Proof.
  intro z.
  unfold Rabs.
  destruct (Rcase_abs (IZR z)) as [ h | h ].
  {
    unfold Z.abs.
    destruct z.
    { change (IZR 0) with R0. rewrite Ropp_0. reflexivity. }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rlt_trans with (IZR (Z.pos p)).
      {
        change R0 with (IZR 0).
        apply IZR_lt.
        apply Pos2Z.pos_is_pos.
      }
      { assumption. }
    }
    {
      rewrite <- opp_IZR.
      rewrite Pos2Z.opp_neg.
      reflexivity.
    }
  }
  {
    unfold Z.abs.
    destruct z.
    { reflexivity. }
    { reflexivity. }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with (IZR (Z.neg p)).
      { assumption. }
      {
        change R0 with (IZR 0).
        apply IZR_lt.
        apply Pos2Z.neg_is_neg.
      }
    }
  }
Qed.

Lemma Rabs_Zabs : forall z:Z, Rabs (IZR z) = IZR (Z.abs z).
Proof.
  intro z.
  symmetry.
  apply abs_IZR.
Qed.

Lemma Ropp_Rmax : forall x y, - Rmax x y = Rmin (-x) (-y).
Proof.
  intros x y.
  unfold Rmax, Rmin.
  destruct (Rle_dec x y) as [ hxy | hxy ];
  destruct (Rle_dec (-x) (-y)) as [ hxy' | hxy' ].
  {
    apply Rle_antisym.
    apply Ropp_le_contravar. assumption.
    assumption.
  }
  { reflexivity. }
  { reflexivity. }
  {
    apply Rnot_le_lt in hxy.
    apply Rnot_le_lt in hxy'.
    apply Rle_antisym.
    left. apply Ropp_lt_contravar. assumption.
    left. assumption.
  }
Qed.

Lemma Ropp_Rmin : forall x y, - Rmin x y = Rmax (-x) (-y).
Proof.
intros x y.
unfold Rmax.
unfold Rmin.
destruct (Rle_dec x y) as [ hmin | hmin ];
destruct (Rle_dec (-x) (-y)) as [ hmax | hmax ].
{
  apply Rle_antisym.
  assumption.
  apply Ropp_le_contravar.
  assumption.
}
{ reflexivity. }
{ reflexivity. }
{
  apply Rnot_le_lt in hmin.
  apply Rnot_le_lt in hmax.
  apply Rle_antisym.
  left. assumption.
  left. apply Ropp_lt_contravar. assumption.
}
Qed.

Lemma Rmax_assoc : forall x y z, Rmax x (Rmax y z) = Rmax (Rmax x y) z.
Proof.
intros x y z.
unfold Rmax.
destruct (Rle_dec y z) as [ hyz | hyz ] eqn:eqyz.
{
  destruct (Rle_dec x y) as [ hxy | hxy ] eqn:eqxy.
  {
    destruct (Rle_dec x z) as [ hxz | hxz ] eqn:eqxz.
    {
      rewrite eqyz. reflexivity.
    }
    {
      rewrite eqyz. apply Rle_antisym.
      apply Rle_trans with y;assumption.
      clear eqxz.
      apply Rnot_le_lt in hxz.
      left. assumption.
    }
  }
  {
    destruct (Rle_dec x z) as [ hxz | hxz ] eqn:eqxz.
    { reflexivity. }
    { reflexivity. }
  }
}
{
  destruct (Rle_dec x y) as [ hxy | hxy ] eqn:eqxy.
  {
    rewrite eqyz. reflexivity.
  }
  {
    destruct (Rle_dec x z) as [ hxz | hxz ] eqn:eqxz.
    {
      apply Rle_antisym.
      assumption.
      left.
      clear eqyz. apply Rnot_le_lt in hyz.
      clear eqxy. apply Rnot_le_lt in hxy.
      apply Rlt_trans with y;assumption.
    }
    { reflexivity. }
  }
}
Qed.

Lemma Rminmax : forall a b, Rmin a b <= Rmax a b.
Proof.
  intros x y.
  unfold Rmin, Rmax.
  destruct (Rle_dec x y) as [ hxy | hxy ].
  { assumption. }
  {
    apply Rnot_le_lt in hxy.
    left. assumption.
  }
Qed.

Lemma Rmin_assoc : forall x y z, Rmin x (Rmin y z) =
  Rmin (Rmin x y) z.
Proof.
intros x y z.
unfold Rmin.
destruct (Rle_dec y z) as [ hyz | hyz ] eqn:eqyz.
{
  destruct (Rle_dec x y) as [ hxy | hxy ] eqn:eqxy.
  {
    destruct (Rle_dec x z) as [ hxz | hxz ] eqn:eqxz.
    { reflexivity. }
    {
      apply Rle_antisym.
      apply Rle_trans with y;assumption.
      clear eqxz; apply Rnot_le_lt in hxz.
      left.
      assumption.
    }
  }
  { rewrite eqyz. reflexivity. }
}
{
  destruct (Rle_dec x y) as [ hxy | hxy ] eqn:eqxy.
  {
    destruct (Rle_dec x z) as [ hxz | hxz ] eqn:eqxz.
    { reflexivity. }
    { reflexivity. }
  }
  {
    destruct (Rle_dec x z) as [ hxz | hxz ] eqn:eqxz.
    {
      rewrite eqyz.
      apply Rle_antisym.
      assumption.
      left.
      clear eqxy. apply Rnot_le_lt in hxy.
      clear eqyz. apply Rnot_le_lt in hyz.
      apply Rlt_trans with y;assumption.
    }
    { rewrite eqyz. reflexivity. }
  }
}
Qed.
(*
completeness
     : forall E : R -> Prop, bound E -> (exists x : R, E x) -> {m : R | is_lub E m}
*)

Definition tada x s := s * s <= x.

Definition tada' x s := s * s = x \/ s * s = R0.

Lemma Rsqr_le_1 : forall x, R0 < x -> x <= R1 -> x * x <= x.
Proof.
  intros x hl hr .
  destruct hr as [ hr | hr ].
  {
    left.
    pattern x at 3;rewrite <- Rmult_1_r.
    apply Rmult_lt_compat_l.
    exact hl.
    exact hr.
  }
  {
    subst x.
    rewrite Rmult_1_l.
    right.
    reflexivity.
  }
Qed.

Lemma Rsqr_le_0 : forall x, Rsqr x <= R0 -> x = R0.
Proof.
  intros x h.
  destruct h as [ h | h ].
  {
    exfalso.
    apply Rlt_irrefl with R0.
    apply Rle_lt_trans with (Rsqr x).
    { apply Rle_0_sqr. }
    { exact h. }
  }
  {
    unfold Rsqr in h.
    apply Rmult_integral in h.
    destruct h as [ h | h ].
    { exact h. }
    { exact h. }
  }
Qed.

Lemma tada_bound : forall x, R0 <= x -> bound (tada x).
Proof.
  intros x hx.
  unfold bound.
  unfold is_upper_bound.
  unfold tada.
  destruct hx as [ hx | hx ].
  {
    destruct (Rtotal_order x R1) as [ ho | [ ho | ho ] ].
    {
      exists R1.
      intros y hy.
      destruct (Rtotal_order y R0) as [ hoy | [ hoy | hoy ] ].
      {
        destruct (Rtotal_order y (-R1)) as [ hoy' | [ hoy' | hoy' ] ].
        {
          apply Rle_trans with (-R1).
          left. exact hoy'.
          apply Rle_trans with R0.
          rewrite <- Ropp_0. apply Ropp_le_contravar. left. exact Rlt_0_1.
          left. exact Rlt_0_1.
        }
        {
          subst y.
          apply Rle_trans with R0.
          { rewrite <- Ropp_0. apply Ropp_le_contravar. left. exact Rlt_0_1. }
          { left. exact Rlt_0_1. }
        }
        {
          apply Rle_trans with R0.
          left. exact hoy.
          left. exact Rlt_0_1.
        }
      }
      {
        subst y.
        left.
        exact Rlt_0_1.
      }
      {
        destruct (Rtotal_order y R1) as [ hoy' | [ hoy' | hoy' ] ].
        {
          left.
          exact hoy'.
        }
        {
          subst y.
          right.
          reflexivity.
        }
        {
          exfalso.
          eapply Rlt_irrefl.
          eapply Rlt_le_trans.
          { exact hoy'. }
          {
            eapply Rle_trans.
            2:{
              left.
              exact ho.
            }
            {
              clear ho.
              apply Rmult_le_reg_r with y.
              { exact hoy. }
              {
                eapply Rle_trans.
                { exact hy. }
                {
                  pattern x at 1;rewrite <- Rmult_1_r.
                  apply Rmult_le_compat_l.
                  { left. exact hx. }
                  { left. exact hoy'. }
                }
              }
            }
          }
        }
      }
    }
    {
      subst x.
      exists R1.
      intros y hy.
      destruct (Rtotal_order y R0) as [ hoy | [ hoy | hoy ] ].
      {
        apply Rle_trans with R0.
        left. exact hoy.
        left. exact Rlt_0_1.
      }
      {
        subst y.
        left.
        exact Rlt_0_1.
      }
      {
        destruct (Rtotal_order y R1) as [ hoy' | [ hoy' | hoy' ] ].
        { left. exact hoy'. }
        { subst y. right. reflexivity. }
        {
          exfalso.
          eapply Rlt_irrefl.
          eapply Rle_lt_trans.
          { apply hy. }
          {
            pattern R1;rewrite <- Rmult_1_r.
            apply Rmult_gt_0_lt_compat.
            { exact Rlt_0_1. }
            { exact hoy. }
            { exact hoy'. }
            { exact hoy'. }
          }
        }
      }
    }
    {
      exists x.
      intros y hy.
      destruct (Rtotal_order y R0) as [ hoy | [ hoy | hoy ] ].
      {
        left.
        apply Rlt_trans with R0.
        exact hoy.
        exact hx.
      }
      {
        subst y.
        left.
        exact hx.
      }
      {
        destruct (Rtotal_order y R1) as [ hoy' | [ hoy' | hoy' ] ].
        {
          left.
          apply Rlt_trans with R1.
          exact hoy'.
          exact ho.
        }
        {
          subst y .
          left.
          exact ho.
        }
        {
          apply Rmult_le_reg_r with y.
          exact hoy.
          apply Rle_trans with x.
          exact hy.
          pattern x at 1;rewrite <- Rmult_1_r.
          apply Rmult_le_compat_l.
          left. exact hx.
          left. exact hoy'.
        }
      }
    }
  }
  {
    subst x.
    exists R0.
    intros x hx.
    apply Rsqr_le_0 in hx.
    right.
    exact hx.
  }
Qed.
