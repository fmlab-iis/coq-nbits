
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

(*
 * Nnat.N2Nat.inj_div is available since Coq 8.14
 *)
Lemma N2Nat_inj_div n m :
  N.to_nat (n / m) = N.to_nat n / N.to_nat m.
Proof.
  destruct m as [|m]; [now destruct n|].
  apply Nat.div_unique with (N.to_nat (n mod (N.pos m))).
  - apply Nat.compare_lt_iff. rewrite <- Nnat.N2Nat.inj_compare.
    now apply N.mod_lt.
  - now rewrite <- Nnat.N2Nat.inj_mul, <- Nnat.N2Nat.inj_add, <- N.div_mod.
Qed.

(*
 * Nnat.Nat2N.inj_div is available since Coq 8.14
 *)
Lemma Nat2N_inj_div n n' :
  N.of_nat (n / n') = (N.of_nat n / N.of_nat n')%N.
Proof.
  apply Nnat.N2Nat.inj; rewrite N2Nat_inj_div;
  now autorewrite with Nnat.
Qed.

(*
 * Nnat.N2Nat.inj_mod is available since Coq 8.14.
 * Before Coq 8.14, [a' <> 0] is required.
 *)
Lemma N2Nat_inj_mod a a' :
  (a' <> 0)%N ->
  N.to_nat (a mod a') = N.to_nat a mod N.to_nat a'.
Proof.
  destruct a' as [|a']; [now destruct a|]. intro.
  apply Nat.mod_unique with (N.to_nat (a / (N.pos a'))).
  - apply Nat.compare_lt_iff. rewrite <- Nnat.N2Nat.inj_compare.
    now apply N.mod_lt.
  - now rewrite <- Nnat.N2Nat.inj_mul, <- Nnat.N2Nat.inj_add, <- N.div_mod.
Qed.

(*
 * Pnat.Pos2Nat.inj_pow is available since Coq 8.14.
 *)
Theorem Pos2Nat_inj_pow (p q : positive) :
  Pos.to_nat (p ^ q) = Pos.to_nat p ^ Pos.to_nat q.
Proof.
 induction q as [|q IHq] using Pos.peano_ind.
 - now rewrite Pos.pow_1_r Pnat.Pos2Nat.inj_1 Nat.pow_1_r.
 - unfold Pos.pow. rewrite Pnat.Pos2Nat.inj_succ Pos.iter_succ Pnat.Pos2Nat.inj_mul.
   fold (Pos.pow p q). now rewrite IHq.
Qed.

(*
 * Nnat.N2Nat.inj_0 is available since Coq 8.14.
 *)
Lemma N2Nat_inj_0 : N.to_nat 0 = 0.
Proof. reflexivity. Qed.

(*
 * Nnat.N2Nat.inj_pow is available since Coq 8.14.
 *)
Lemma N2Nat_inj_pow a a' :
  N.to_nat (a ^ a') = N.to_nat a ^ N.to_nat a'.
Proof.
  destruct a, a'; [easy| |easy|apply Pos2Nat_inj_pow].
  rewrite N.pow_0_l; last by easy.
  rewrite Nat.pow_0_l; first exact: N2Nat_inj_0.
  rewrite positive_N_nat => H. move: (Pos2Nat.is_pos p).
  rewrite H. exact: (Nat.lt_irrefl 0).
Qed.

(*
 * Nnat.Nat2N.inj_pow is available since Coq 8.14.
 *)
Lemma Nat2N_inj_pow n n' :
  N.of_nat (n ^ n') = (N.of_nat n ^ N.of_nat n')%N.
Proof.
  apply Nnat.N2Nat.inj; rewrite N2Nat_inj_pow;
  now autorewrite with Nnat.
Qed.
