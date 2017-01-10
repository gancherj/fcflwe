(* Adapted from https://github.com/Eelis/hybrid (although the construction is standard) *)

Add LoadPath "~/research/MP-FCF/".
Add LoadPath "~/fcf/src/FCF".
Add LoadPath "~/code/fcf/src/FCF".
Add LoadPath "~/research/MP-FCF/hybrid".
Require Import Vector.
Require Import FCF.

Set Implicit Arguments.


Inductive bnat: nat -> Set :=
  | bO n: bnat (S n)
  | bS n: bnat n -> bnat (S n).

Fixpoint to_nat n (b: bnat n): nat :=
  match b with
  | bO _ => 0%nat
  | bS x => S (to_nat x)
  end.

(* stolen from coq-ext-lib *)

Fixpoint bnat_from_nat_raw (m n : nat) {struct m} : n < m -> bnat m :=
match n as n, m as m return n < m -> bnat m with
 | 0, 0 => fun pf => @False_rect _ (lt_eq_false pf)
 | 0, S m => fun _ => bO m
 | S n, 0 => fun pf => @False_rect _ (lt_n_0 _ pf)
 | S n, S m => fun pf => bS (@bnat_from_nat_raw m n (lt_S_n _ _ pf))
end.

Definition bnat_mod_nat (N n : nat) :=
let pfz := not_eq_sym (O_S N) in
@bnat_from_nat_raw (S N) (n mod (S N)) (Nat.mod_upper_bound n (S N) pfz).

Section alt_rect.

  Variables
    (P: forall n: nat, bnat (S n) -> Type)
    (Pz: forall p, P (bO p))
    (Ps: forall n (b: bnat (S n)), P b -> P (bS b)).

  Let R (n: nat): bnat n -> Type :=
    match n with
    | O => fun _ => False
    | S _ => @P _
    end.

  Fixpoint RS (n : nat): forall (b : bnat n), R b -> R (bS b) :=
    match n return forall (b : bnat n), R b -> R (bS b) with
    | O => fun x f => False_rect _ f
    | S n' => fun x f => Ps f
    end.

  Definition bnat_Srect (n: nat) (nb: bnat (S n)): P nb
    := bnat_rect R Pz RS nb.

End alt_rect.

Lemma bnat_cases n (x: bnat (S n)): { p | x = bS p } + { x = bO n }.
  revert n x.
  apply bnat_Srect; [right | left; exists b]; reflexivity.
Defined.

Lemma bnat_0: bnat 0 -> False.
Proof with auto.
  cut (forall n, bnat n -> n <> 0%nat).
    intros H H0. apply (H _ H0)...
  induction 1; intro; discriminate.
Qed.

Require Import List.

Definition bnat_bound n (b: bnat n): nat := n.

Lemma bnat_bound_lt n (b : bnat n) : @to_nat n b < @bnat_bound n b.
induction n.
exfalso.
apply bnat_0; auto.

dependent inversion b; subst.
unfold to_nat, bnat_bound.
apply lt_0_Sn.

simpl.
unfold bnat_bound.
apply lt_n_S.
apply IHn.
Qed.




Definition pred n (b: bnat n): option (bnat (Peano.pred (bnat_bound b))) :=
  match b return option (bnat (Peano.pred (bnat_bound b))) with
  | bO _ => None
  | bS y => Some y
  end.

Require Import util.

Lemma eq_bS_inv n (x y: bnat n): bS x = bS y -> x = y.
Proof with auto.
  intros.
  apply option_eq_inv.
  replace (Some x) with (pred (bS x))...
  replace (Some y) with (pred (bS y))...
  rewrite H...
Qed.


Definition all_bnats := fix F (n: nat): list (bnat n) :=
  match n with
  | O => nil
  | S m => bO m :: map (@bS m) (F m)
  end.

Global Instance bnats n: ExhaustiveList (bnat n) := { exhaustive_list := all_bnats n }.
Proof with auto.
  dependent induction n; intro x.
    elimtype False. apply bnat_0...
  destruct (bnat_cases x) as [[p e] | e]; subst; [right | left]...
Defined.

Lemma tonat_sound {N : nat} (o1 o2 : bnat N) : to_nat o1 = to_nat o2 -> o1 = o2.
intros.
dependent induction o1.
dependent destruction o2.
auto.
discriminate.
dependent destruction o2.
discriminate.
inversion H.
apply IHo1 in H1.
subst.
auto.
Qed.

Definition eqb_bnat {N : nat} (o1 o2 : bnat N) := eqb (to_nat o1) (to_nat o2).

Lemma eqb_bnat_refl {N : nat} (o : bnat N) : eqb_bnat o o = true.
unfold eqb_bnat.
apply eqb_leibniz.
auto.
Qed.

Lemma eqb_bnat_sound {N : nat} (o1 o2 : bnat N) : eqb_bnat o1 o2 = true -> o1 = o2.
intuition.
unfold eqb_bnat in H.
rewrite eqb_leibniz in H.
apply tonat_sound.
auto.
Qed.

Instance bnat_eqdec {N : nat} : EqDec (bnat N) := {eqb := eqb_bnat}.
intuition.
apply eqb_bnat_sound.
auto.

subst.
apply eqb_bnat_refl.
Qed.

(* arithmetic *)
Definition bnat_add {N : nat} (a b : bnat (S N)) := bnat_mod_nat N ((to_nat a) + (to_nat b)).
Definition bnat_mult {N : nat} (a b : bnat (S N)) := bnat_mod_nat N ((to_nat a) * (to_nat b)).

Definition bd_vec (n q : nat) := Vector.t (bnat q) n.

Fixpoint dot_prod {n q : nat} (v w : bd_vec n (S q)) := 
Vector.fold_left2 (fun (acc a b : bnat (S q)) => bnat_add acc (bnat_mult a b)) (bO q) v w.

Global Instance eqbv : forall {n q : nat}, EqDec (bd_vec n q).
unfold bd_vec.
intros.
apply Vector_EqDec.
apply bnat_eqdec.
Defined.

Check dot_prod.

