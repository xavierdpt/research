Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rle.
Require Import XR_Ropp_0.
Require Import XR_Ropp_le_contravar.


Local Open Scope R_scope.

Lemma Rabs_pos : forall x:R, R0 <= Rabs x.
Proof.
  intros x.
  unfold Rabs.
  destruct (Rcase_abs x) as [ h | h ].
  {
    rewrite <- Ropp_0.
    apply Ropp_le_contravar.
    left.
    exact h.
  }
  { exact h. }
Qed.
