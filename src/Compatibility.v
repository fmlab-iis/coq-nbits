
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect.

(*
 * Before Coq 8.14, this lemma is:
 * Lemma Z_div_nz_opp_full : forall a b:Z, a mod b <> 0 -> (-a)/b = -(a/b)-1.
 *)
Lemma Z_div_nz_opp_full (a b : Z) :
  b <> 0%Z -> (a mod b)%Z <> 0%Z -> (- a / b)%Z = (- (a / b) - 1)%Z.
Proof. move=> *; by apply: Z_div_nz_opp_full. Qed.

(*
 * Before Coq 8.14, this lemma is:
 * Lemma Z_div_nz_opp_r : forall a b:Z, a mod b <> 0 -> a/(-b) = -(a/b)-1.
 *)
Lemma Z_div_nz_opp_r (a b : Z):
  b <> 0%Z -> (a mod b)%Z <> 0%Z -> (a / - b)%Z = (- (a / b) - 1)%Z.
Proof. move=> *; by apply: Z_div_nz_opp_r. Qed.

(*
 * After Coq 8.14, this lemma (in the module Z2N) is:
 * Lemma inj_mod n m : 0<=n -> 0<=m -> Z.to_N (n mod m) = ((Z.to_N n) mod (Z.to_N m))%N.
 *)
Lemma Z2N_inj_mod (n m : Z) :
  (0<=n)%Z -> (0<m)%Z -> Z.to_N (n mod m) = ((Z.to_N n) mod (Z.to_N m))%N.
Proof.
  move=> H0n H0m. move: (Z.lt_le_incl _ _ H0m) => H0m'.
  by apply: Z2N.inj_mod.
Qed.
