Require Import bnat.
Require Import FCF.
Require Import EqDec.
Set Implicit Arguments.
Check 0.


Definition vec_dotmod {n : nat} (q : nat) (a b : Vector.t nat n) :=
Vector.fold_left2 (fun acc v w => acc + (v * w) mod q)%nat 0%nat a b.

Check Vector.map2.

Definition vec_addmod {n : nat} (q : nat) (a b : Vector.t nat n) :=
Vector.map2 (fun x y => x + y mod q)%nat a b.

Definition ratRound01 (r : Rat) :=
if bleRat (ratDistance r 0) (ratDistance r 1) then false else true.

Fixpoint Sample_N {A : Set} {eqa : EqDec A} {eqva : forall n, EqDec (Vector.t A n)} (c : Comp A) (n : nat) : Comp (Vector.t A n) :=
match n with
| 0 => ret (Vector.nil A)
| S m => x <-$ c;
         tl <-$ Sample_N c m;
         ret (Vector.cons _ x _ tl)
end.

Definition Uniform_nat (N : nat) :=
x <-$ [0..N);
ret x.

Section LWE_Defs.
Context (q n : nat).
Context (posq : nz q).
Locate nz.
Definition LWEVec := Vector.t nat n.

Check Vector.fold_left2.



Definition Uniform_LWEVec := Sample_N (Uniform_nat q) n. (* computes x <-$ Z_q^n *)
Definition Uniform_q := Uniform_nat q. (* computes x <-$ Z_q *)
Context (chi : Comp (bnat q)).

Definition LWE_UniformDist (st input : unit) :=
a <-$ Uniform_LWEVec;
b <-$ Uniform_q;
ret ((a, b), tt).

Definition LWE_RealDist (s : LWEVec) (st input : unit) :=
a <-$ Uniform_LWEVec;
e <-$ chi;
ret ((a, (to_nat e) + (vec_dotmod q a s))%nat, tt).


Check LWE_RealDist.

Variable D : OracleComp unit (Vector.t nat n * nat) bool.

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
Context (posq : nz q).
Context (chi : Comp (bnat q)).
Check Uniform_LWEVec.
Definition Sample_SK := Uniform_LWEVec q n.
Check Sample_SK.
Definition Regev_SecretKey := (Vector.t nat n).

Check LWEVec.

Check LWE_RealDist.

Definition Sample_PK (s : LWEVec n) := Sample_N
([a, b, _] <-$3 LWE_RealDist chi s tt tt;
 ret (a, b)) 
m.

Check Sample_PK.
Definition Regev_PublicKey := (Vector.t (Vector.t nat n * nat) m).

Definition Generate_SelectVector := Sample_N ({0,1}) m.
Definition SelectVector := Vector.t bool m.

Check Vector.const.

Check vec_addmod.

Definition SubsetSum (pk: Regev_PublicKey) (sel : SelectVector) :=
Vector.fold_left2 (fun acc p (b : bool) => if b then 
                   match p, acc with
                   | (a, b), (aa, ab) => (vec_addmod q a aa, b + ab mod q)%nat 
                   end
                    else acc)
                   (Vector.const 0%nat n, 0%nat) pk sel.

Check SubsetSum.

Check div.

Check bnat_mod_nat.

Definition Regev_PKEnc (pk: Regev_PublicKey) (m : bool) :=
sel <-$ Generate_SelectVector;
[a, b] <-2 SubsetSum pk sel;
b <- if m then
      (b + (div q 2) mod q)%nat
      else b;
ret (a, b).



Definition Regev_Ciphertext := (Vector.t nat n * nat)%type.


Definition Regev_PKDec (s : Regev_SecretKey) (c : Regev_Ciphertext) := match c with
| (a, b) => let r := (b - (vec_dotmod q a s)) in
            ratRound01 ( (r/1) * (2 / 1) * (1 / q))%rat
end.

Check Vector.fold_left.

Definition admissible_chi (k : nat) :=
es <-$ Sample_N chi k;
sum <- Vector.fold_left (fun a b => a + (to_nat b))%nat (0%nat) es;
ret (leb sum (div q 4)).

Lemma correct_decrypt (delta : Rat) (s : Regev_SecretKey) (pk: Regev_PublicKey) (c : Regev_Ciphertext) (msg : bool) :
In pk (getSupport (Sample_PK s)) ->
In c (getSupport (Regev_PKEnc pk msg)) ->
(forall k : nat, k < m -> Pr[admissible_chi k] <= delta) ->
Regev_PKDec s c = msg.
Abort.

            

