Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Ropp_lt_cancel.

Local Open Scope R_scope.

Lemma Rabs_def1 : forall x a:R, x < a -> - a < x -> Rabs x < a.
Proof.
  intros x y.
  intros h hm.
  unfold Rabs.
  destruct (Rcase_abs x) as [ hx | hx ].
  {
    apply Ropp_lt_cancel.
    rewrite Ropp_involutive.
    exact hm.
  }
  { exact h. }
Qed.