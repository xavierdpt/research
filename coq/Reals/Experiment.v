Require Import Reals.
Open Scope R_scope.

Lemma lema : 0 <> / 0.
intro eq.



Lemma lema : 0 = / 0.
apply (Rplus_eq_reg_r (/ 0)).
rewrite Rplus_0_l.
pattern (/ 0) at 2; rewrite <- Rmult_1_l.
pattern (/ 0) at 3; rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
pattern (/ 0) at 1; rewrite <- Rmult_1_l.
apply Rmult_eq_compat_r.
pattern 1 at 1;rewrite <- Rplus_0_l.
apply Rplus_eq_compat_r.
