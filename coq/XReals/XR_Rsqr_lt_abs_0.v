Require Import XR_R.
Require Import XR_Rlt.
Require Import XR_Rlt_irrefl.
Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rsqr.
Require Import XR_Rsqr_neg.
Require Import XR_Rsqr_le_abs_0.

Local Open Scope R_scope.

Lemma Rsqr_lt_abs_0 : forall x y:R, Rsqr x < Rsqr y -> Rabs x < Rabs y.
Proof.
  intros x y h.
  assert (th:=Rsqr_le_abs_0).
  specialize (th x y).
  destruct th as [ th | th ].
  {
    left.
    exact h.
  }
  { exact th. }
  {
    exfalso.
    apply Rlt_irrefl with (Rsqr x).
    unfold Rabs in th.
    destruct (Rcase_abs x) as [ hx | hx ] ;
    destruct (Rcase_abs y) as [ hy | hy ].
    {
      pattern x at 1 ; rewrite (Rsqr_neg x).
      rewrite th.
      rewrite <- Rsqr_neg.
      exact h.
    }
    {
      pattern x at 1 ; rewrite (Rsqr_neg x).
      rewrite th.
      exact h.
    }
    {
      pattern x at 2 ; rewrite th.
      rewrite <- Rsqr_neg.
      exact h.
    }
    {
      pattern x at 2 ; rewrite th.
      exact h.
    }
  }
Qed.