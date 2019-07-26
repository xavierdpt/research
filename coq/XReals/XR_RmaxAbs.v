Require Import XR_Rabs.
Require Import XR_Rmax.
Require Import XR_Rcase_abs.
Require Import XR_Rle_dec.
Require Import XR_Rle_trans.
Require Import XR_Rle_lt_trans.
Require Import XR_Rlt_le_trans.
Require Import XR_Ropp_le_contravar.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma RmaxAbs :
  forall (p q:R) r, p <= q -> q <= r -> Rabs q <= Rmax (Rabs p) (Rabs r).
Proof.
  intros x y z.
  intros hxy hyz.
  unfold Rmax.
  destruct (Rle_dec (Rabs x) (Rabs z)) as [ hm | hm ].
  {
    unfold Rabs in hm ; unfold Rabs.
    destruct (Rcase_abs x) as [ hx | hx ] ;
    destruct (Rcase_abs y) as [ hy | hy ] ;
    destruct (Rcase_abs z) as [ hz | hz ].
    {
      apply Rle_trans with (-x).
      {
        apply Ropp_le_contravar.
        exact hxy.
      }
      { exact hm. }
    }
    {
      apply Rle_trans with (-x).
      {
        apply Ropp_le_contravar.
        exact hxy.
      }
      { exact hm. }
    }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      {
        apply Rle_lt_trans with z.
        {
          apply Rle_trans with y.
          { exact hy. }
          { exact hyz. }
        }
        { exact hz. }
      }
    }
    { exact hyz. }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with y.
      {
        apply Rle_trans with x.
        { exact hx. }
        { exact hxy. }
      }
      { exact hy. }
    }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with y.
      {
        apply Rle_trans with x.
        { exact hx. }
        { exact hxy. }
      }
      { exact hy. }
    }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with z.
      {
        apply Rle_trans with y.
        { exact hy. }
        { exact hyz. }
      }
      { exact hz. }
    }
    { exact hyz. }
  }
  {
    unfold Rabs in hm ; unfold Rabs.
    destruct (Rcase_abs x) as [ hx | hx ] ;
    destruct (Rcase_abs y) as [ hy | hy ] ;
    destruct (Rcase_abs z) as [ hz | hz ].
    {
      apply Ropp_le_contravar.
      exact hxy.
    }
    {
      apply Ropp_le_contravar.
      exact hxy.
    }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with z.
      {
        apply Rle_trans with y.
        { exact hy. }
        { exact hyz. }
      }
      { exact hz. }
    }
    {
      assert (hzx : z < -x).
      {
        apply Rnot_le_lt.
        exact hm.
      }
      apply Rle_trans with z.
      { exact hyz. }
      {
        left.
        exact hzx.
      }
    }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with y.
      {
        apply Rle_trans with x.
        { exact hx. }
        { exact hxy. }
      }
      { exact hy. }
    }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with y.
      {
        apply Rle_trans with x.
        { exact hx. }
        { exact hxy. }
      }
      { exact hy. }
    }
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rle_lt_trans with z.
      {
        apply Rle_trans with y.
        { exact hy. }
        { exact hyz. }
      }
      { exact hz. }
    }
    {
      assert (hzx : z < x).
      {
        apply Rnot_le_lt.
        exact hm.
      }
      exfalso.
      apply Rlt_irrefl with z.
      apply Rlt_le_trans with x.
      { exact hzx. }
      {
        apply Rle_trans with y.
        { exact hxy. }
        { exact hyz. }
      }
    }
  }
Qed.

