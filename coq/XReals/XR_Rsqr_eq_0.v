Require Import XR_Rsqr.
Require Import XR_Rmult_integral.

Local Open Scope R_scope.

Lemma Rsqr_eq_0 : forall x:R, Rsqr x = R0 -> x = R0.
Proof.
  intros x h.
  unfold Rsqr in h.
  apply Rmult_integral in h.
  destruct h as [ h | h ].
  { exact h. }
  { exact h. }
Qed.