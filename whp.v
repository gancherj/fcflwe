Add LoadPath "~/fcf/fcf/src/FCF".
Require Import FCF.
Require Import Asymptotic.
Require Import Vector.
Require Import Bvector.
Check Bvector.

(* first attempt : distributions are parametrized by some n. properties are deterministic functions to bool on these distributions. *)

Infix "-" := ratSubtract : rat_scope.

Section whps.



Definition Prob {A : nat -> Set}   (D : forall n, Comp (A n)) (P : forall n, A n -> bool) := fun n => Pr[x <-$ D n; ret P _ x].


Definition wlp {A : nat -> Set} (D : forall n, Comp (A n)) (P : forall n, A n -> bool) := negligible (fun n => Prob D P n). 
Definition whp {A : nat -> Set} (D : forall n, Comp (A n)) (P : forall n, A n -> bool) := negligible (fun n => (1 - Prob D P n)%rat).

Notation "D ⊨ P 'w/hp'" := (whp D P) (at level 99).
Notation "D ⊨ P 'w/lp'" := (wlp D P) (at level 99).

Definition wp_impl {A : nat -> Set} (P Q : forall n, A n -> bool) := forall (n : nat) (x : A n), P n x = true -> Q n x = true.

Notation "P ~> Q" := (wp_impl P Q) (at level 99).

Theorem prob_le : forall A (D : forall n, Comp (A n)) P Q n, P ~> Q -> Prob D P n <= Prob D Q n.
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

Theorem prob_opple : forall A (D : forall n, Comp (A n)) P Q n, P ~> Q -> 1 - Prob D Q n <= 1 - Prob D P n.
intuition.
pose (prob_le A D P Q n H).
apply ratSubtract_leRat_r.
intuition.
Qed.


Theorem whp_impl : forall A (D : forall n, Comp (A n)) P Q, D ⊨ P w/hp -> wp_impl P Q -> D ⊨ Q w/hp.
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

Theorem wlp_impl : forall A (D : forall n, Comp (A n)) P Q, D ⊨ P w/lp -> Q ~> P -> D ⊨ Q w/lp.
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

Theorem union_bound : forall A (D : forall n, Comp (A n)) P Q n, Prob D (fun n x => P n x && Q n x) n <= Prob D P n + Prob D Q n.
Abort.
(* is the above right to prove the below? *)


Theorem whp_and : forall A (D : forall n, Comp (A n)) P Q, D ⊨ P w/hp -> D ⊨ Q w/hp -> D ⊨ (fun n x => andb (P n x) (Q n x)) w/hp.
intuition.
unfold whp in *.
unfold negligible in *.
intuition.
destruct (H c).
destruct (H0 c).
exists (Nat.max x x0).
intuition.
unfold gt in H3.
apply Nat.max_lub_lt_iff in H3.
destruct H3.
unfold gt in H1.
pose (H1 x1 pf_nz H3).
unfold gt in H2.
pose (H2 x1 pf_nz H5).

unfold Prob in *.

assert (Pr [x <-$ D x1; ret P x1 x && Q x1 x ] <= Pr [x <-$ D x1; ret P x1 x ] + Pr [x <-$ D x1; ret Q x1 x ]). (* union bound *)
comp_skip.
simpl.






Definition Prob_bv := Prob (fun n => x <-$ {0,1}^n; ret x).
Definition wlp_bv := wlp (fun n => x <-$ {0,1}^n; ret x).
Definition whp_bv := whp (fun n => x <-$ {0,1}^n; ret x).

End whps.

