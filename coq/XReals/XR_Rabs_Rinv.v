Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rlt_irrefl.
Require Import XR_Rle_lt_trans.
Require Import XR_Ropp_inv_permute.
Require Import XR_Rinv_lt_0_compat.
Require Import XR_Rinv_neq_0_compat.

Local Open Scope R_scope.

Lemma Rabs_Rinv : forall r, r <> R0 -> Rabs (/ r) = / Rabs r.
Proof.
  intros x h.
  unfold Rabs.
  destruct (Rcase_abs x) as [ hl | hr ] ;
  destruct (Rcase_abs (/x)) as [ hil | hir ].
  {
    rewrite Ropp_inv_permute.
    { reflexivity. }
    { exact h. }
  }
  {
    exfalso.
    apply Rlt_irrefl with (/x).
    apply Rle_lt_trans with R0.
    {
      left.
      apply Rinv_lt_0_compat.
      exact hl.
    }
    {
      destruct hir as [ hir | hir ].
      { exact hir. }
      {
        exfalso.
        apply Rinv_neq_0_compat with x.
        { exact h. }
        {
          symmetry.
          exact hir.
        }
      }
    }
  }
  {
    exfalso.
    apply Rlt_irrefl with (/x).
    apply Rle_lt_trans with R0.
    {
      left.
      exact hil.
    }
    {
      destruct hr as [ hr | hr ].
      {
        apply Rinv_0_lt_compat.
        exact hr.
      }
      {
        subst x.
        exfalso.
        apply h.
        reflexivity.
      }
    }
  }
  { reflexivity. }
Qed.
