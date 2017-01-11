Require Import bnat.
Require Import FCF.
Require Import EqDec.

Check 0.

Definition ratRound01 (r : Rat) :=
if bleRat (ratDistance r 0) (ratDistance r 1) then false else true.

Fixpoint Sample_N {A : Set} {eqa : EqDec A} {eqva : forall n, EqDec (Vector.t A n)} (c : Comp A) (n : nat) : Comp (Vector.t A n) :=
match n with
| 0 => ret (Vector.nil A)
| S m => x <-$ c;
         tl <-$ Sample_N c m;
         ret (Vector.cons _ x _ tl)
end.

Definition Uniform_bnat (N : nat) :=
x <-$ [0..N);
ret bnat_mod_nat N x.

Section LWE_Defs.
Context (q n : nat).
Definition LWEVec := bd_vec n (S q).

Definition Uniform_LWEVec := Sample_N (Uniform_bnat q) n. (* computes x <-$ Z_(q+1)^n *)
Definition Uniform_q := Uniform_bnat q. (* computes x <-$ Z_(q+1) *)
Context (chi : Comp (bnat (S q))).

Definition LWE_UniformDist (st input : unit) :=
a <-$ Uniform_LWEVec;
b <-$ Uniform_q;
ret ((a, b), tt).

Definition LWE_RealDist (s : LWEVec) (st input : unit) :=
a <-$ Uniform_LWEVec;
e <-$ chi;
ret ((a, bnat_add e (bnv_dot a s)), tt).


Variable D : OracleComp unit (bd_vec n (S q) * bnat (S q)) bool.
Definition LWE_Fake :=
[b, _] <-$2 D _ _ LWE_UniformDist tt;
ret b.

Definition LWE_Real (s : LWEVec) :=
[b, _] <-$2 D _ _ (LWE_RealDist s) tt;
ret b.

Definition LWE_Advantage (s : LWEVec) := |Pr[LWE_Fake] - Pr[LWE_Real s]|. (* this is a concrete rational number *)
End LWE_Defs.

(* should be able to say IND-CPA experiment for Regev LWE PKE is such that for all s,
|Regev_Advantage - LWE_Advantage| < negl(n) *)

Section Regev_PKE.
Context (q n m : nat).
Context (chi : Comp (bnat (S q))).
Check Uniform_LWEVec.
Definition Sample_SK := Uniform_LWEVec q n.
Check Sample_SK.
Definition Regev_SecretKey := (Vector.t (bnat (S q)) n).

Definition Sample_PK (s : LWEVec q n) := Sample_N
([a, b, _] <-$3 LWE_RealDist q n chi s tt tt;
 ret (a, b)) 
m.

Check Sample_PK.
Definition Regev_PublicKey := (Vector.t (Vector.t (bnat (S q)) n * bnat (S q)) m).

Definition Generate_SelectVector := Sample_N ({0,1}) m.
Definition SelectVector := Vector.t bool m.

Definition SubsetSum (pk: Regev_PublicKey) (sel : SelectVector) :=
Vector.fold_left2 (fun acc p (b : bool) => if b then 
                   match p, acc with
                   | (a, b), (aa, ab) => (bnv_add a aa, bnat_add b ab)
                   end
                    else acc)
                   (bd_vec_zeroes n q, bO q) pk sel.

Check div.

Check bnat_mod_nat.

Definition Regev_PKEnc (pk: Regev_PublicKey) (m : bool) :=
sel <-$ Generate_SelectVector;
[a, b] <-2 SubsetSum pk sel;
b <- if m then
      bnat_add b (bnat_mod_nat q (div (S q) 2))
      else b;
ret (a, b).

Check Regev_PKEnc.

Check le.

Check ltb.

Definition nat_dist (a b : nat) := max (a - b) (b - a).


Definition Regev_Ciphertext := (bd_vec n (S q) * bnat (S q))%type.


Definition Regev_PKDec (s : Regev_SecretKey) (c : Regev_Ciphertext) := match c with
| (a, b) => let r := ((to_nat b) - (to_nat (bnv_dot a s))) / 1 in
            ratRound01 (r * (2 / 1) * (1 / (S q)))
end.

Check Vector.fold_left.

Definition admissible_chi (k : nat) :=
es <-$ Sample_N chi k;
sum <- Vector.fold_left (fun a b => bnat_add a b)%nat (bO q) es;
ret (leb (to_nat sum) (div (S q) 4)).

Lemma correct_decrypt (delta : Rat) (s : Regev_SecretKey) (pk: Regev_PublicKey) (c : Regev_Ciphertext) (msg : bool) :
In pk (getSupport (Sample_PK s)) ->
In c (getSupport (Regev_PKEnc pk msg)) ->
(forall k : nat, k < m -> Pr[admissible_chi k] <= delta) ->
Regev_PKDec s c = msg.
Abort.

            

