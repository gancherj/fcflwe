Add LoadPath "~/fcf/src/FCF".
Require Import FCF.
Require Import Asymptotic.
Require Import Vector.
Require Import Bvector.
Check Bvector.

(* first attempt : if distributions are always {0,1}^n, use FCF's native reasoning. ie, WHProps are of the form {0,1}^n :=> P, where P is a determinstic property on random inputs *)

Infix "-" := ratSubtract : rat_scope.

Section whps.



Definition Prob {A : nat -> Set}   (D : forall n, Comp (A n)) (P : forall n, A n -> bool) := fun n => Pr[x <-$ D n; ret P _ x].


Definition wlp {A : nat -> Set} (D : forall n, Comp (A n)) (P : forall n, A n -> bool) := negligible (fun n => Prob D P n). 
Definition whp {A : nat -> Set} (D : forall n, Comp (A n)) (P : forall n, A n -> bool) := negligible (fun n => (1 - Prob D P n)%rat).

Definition wp_impl {A : nat -> Set} (P Q : forall n, A n -> bool) := forall (n : nat) (x : A n), P n x = true -> Q n x = true.

Theorem prob_le : forall A (D : forall n, Comp (A n)) P Q n, wp_impl P Q -> Prob D P n <= Prob D Q n.
intuition.
unfold Prob.
unfold wp_impl in H.
comp_skip.
dist_compute.
exfalso.
pose (H n x e).
intuition.

unfold leRat.
unfold bleRat.
simpl.
auto.
Qed.

Theorem prob_opple : forall A (D : forall n, Comp (A n)) P Q n, wp_impl P Q -> 1 - Prob D Q n <= 1 - Prob D P n.
intuition.
pose (prob_le A D P Q n H).
apply ratSubtract_leRat_r.
intuition.
Qed.


Theorem whp_impl : forall A (D : forall n, Comp (A n)) P Q, whp D P -> wp_impl P Q -> whp D Q.
intuition.
unfold whp in *.

unfold negligible in *.
intuition.
destruct (H c).
exists x.
intuition.
pose (H1 x0 pf_nz H2).
pose (prob_opple A D P Q x0 H0).
pose (leRat_trans H3 l).
intuition.
Qed.

Theorem wlp_impl : forall A (D : forall n, Comp (A n)) P Q, wlp D P -> wp_impl Q P -> wlp D Q.
intuition.
unfold wlp in *.

unfold negligible in *.
intuition.
destruct (H c).
exists x.
intuition.
pose (H1 x0 pf_nz H2).
pose (prob_le A D Q P x0 H0).
pose (leRat_trans H3 l).
intuition.
Qed.

Definition Prob_bv := Prob (fun n => x <-$ {0,1}^n; ret x).
Definition wlp_bv := wlp (fun n => x <-$ {0,1}^n; ret x).
Definition whp_bv := whp (fun n => x <-$ {0,1}^n; ret x).

End whps.

