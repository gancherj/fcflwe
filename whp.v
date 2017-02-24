Add LoadPath "~/fcf/src/FCF".
Require Import FCF.
Require Import Asymptotic.
Require Import Vector.
Require Import Bvector.
Check Bvector.

(* first attempt : if distributions are always {0,1}^n, use FCF's native reasoning. ie, WHProps are of the form {0,1}^n :=> P, where P is a determinstic property on random inputs *)

Infix "-" := ratSubtract : rat_scope.

Section whps.



Definition Prob (n : nat) (P : forall n, Bvector n -> bool) := Pr[x <-$ {0,1}^n; ret P _ x].


Definition wlp (P : forall n, Bvector n -> bool) := negligible (fun n => Prob n P). 
Definition whp (P : forall n, Bvector n -> bool) := negligible (fun n => (1 - Prob n P)%rat).

Definition wp_impl (P Q : forall n, Bvector n -> bool) := forall (n : nat) (x : Bvector n), P _ x = true -> Q _ x = true.

Theorem prob_le : forall P Q n, wp_impl P Q -> Prob n P <= Prob n Q.
intuition.
unfold Prob.
unfold wp_impl in H.
comp_skip.
dist_compute.
pose (H n x e).
exfalso.
intuition.

unfold leRat.
unfold rat0.
unfold rat1.
unfold bleRat.
simpl.
auto.
Qed.



Theorem prob_opple : forall P Q n, wp_impl P Q -> 1 - Prob n Q <= 1 - Prob n P.
intuition.
pose (prob_le P Q n H).
apply ratSubtract_leRat_r.
intuition.
Qed.

Theorem whp_impl : forall P Q, whp P -> wp_impl P Q -> whp Q.
intuition.
unfold whp in *.

unfold negligible in *.
intuition.
destruct (H c).
exists x.
intuition.
pose (H1 x0 pf_nz H2).
pose (prob_opple P Q x0 H0).
pose (leRat_trans H3 l).
intuition.
Qed.

Theorem wlp_impl : forall P Q, wlp P -> wp_impl Q P -> wlp Q.
intuition.
unfold wlp in *.

unfold negligible in *.
intuition.
destruct (H c).
exists x.
intuition.
pose (H1 x0 pf_nz H2).
pose (prob_le Q P x0 H0).
pose (leRat_trans H3 l).
intuition.
Qed.



