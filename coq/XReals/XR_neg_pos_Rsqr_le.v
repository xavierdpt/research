Require Import XR_Rsqr.
Require Import XR_Ropp_0.
Require Import XR_Rle_or_lt.
Require Import XR_Rsqr_neg_pos_le_1.
Require Import XR_Rlt_irrefl.
Require Import XR_Rlt_le_trans.
Require Import XR_Rle_trans.
Require Import XR_Ropp_le_contravar.

Local Open Scope R_scope.

Lemma neg_pos_Rsqr_le : forall x y:R, - y <= x -> x <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y.
  intros hyx hxy.
  destruct (Rle_or_lt R0 y) as [ hy | hy ].
  {
    apply Rsqr_neg_pos_le_1.
    { exact hyx. }
    { exact hxy. }
    { exact hy. }
  }
  {
    exfalso.
    apply Rlt_irrefl with y.
    apply Rlt_le_trans with R0.
    { exact hy. }
    {
      apply Rle_trans with x.
      {
        apply Rle_trans with (-y).
        {
          rewrite <- Ropp_0.
          apply Ropp_le_contravar.
          left.
          exact hy.
        }
        { exact hyx. }
      }
      { exact hxy. }
    }
  }
Qed.
