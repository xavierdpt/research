Require Export XR_R.
Require Export XR_Ropp.
Require Export XR_Rplus_eq_reg_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_involutive : forall r, - - r = r.
Proof.
  intro x.
  apply Rplus_eq_reg_r with (-x).
  rewrite Rplus_opp_r.
  rewrite Rplus_opp_l.
  reflexivity.
Qed.
