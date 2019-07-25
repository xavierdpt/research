Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Ropp_le_cancel.

Local Open Scope R_scope.

Lemma Rabs_le : forall a b, -b <= a <= b -> Rabs a <= b.
Proof.
  intros x y [hl hr].
  unfold Rabs.
  destruct (Rcase_abs x) as [ h | h ].
  {
    apply Ropp_le_cancel.
    rewrite Ropp_involutive.
    exact hl.
  }
  { exact hr. }
Qed.