Require Import bnat.
Require Import FCF.

Definition Uniform_bnat (N : nat) :=
x <-$ [0..N);
ret bnat_mod_nat N x.

Section LWE_Defs.
Context (q n : nat).
Definition LWEVec := bd_vec n (S q).
Fixpoint Uniform_bd_vec (n : nat) : Comp (bd_vec n (S q)) := 
match n with
| 0 => ret (Vector.nil (bnat (S q)))
| S m => b <-$ Uniform_bnat q;
         tl <-$ Uniform_bd_vec m;
         ret (Vector.cons _ b _ tl)
end.

Definition Uniform_LWEVec := Uniform_bd_vec n. (* computes x <-$ Z_(q+1)^n *)
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

 