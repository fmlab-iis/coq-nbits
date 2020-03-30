
From Coq Require Import ZArith Arith Nat List.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma nat_of_bool_inj b1 b2 : nat_of_bool b1 = nat_of_bool b2 -> b1 = b2.
Proof. by case: b1; case: b2. Qed.

Lemma nat_of_bool0 b : (nat_of_bool b == 0) = (b == false).
Proof. by case: b. Qed.

Lemma nat_of_bool1 b : (nat_of_bool b == 1) = (b == true).
Proof. by case: b. Qed.

Lemma nat_of_bool_is_b2n b : nat_of_bool b = Nat.b2n b.
Proof. reflexivity. Qed.


Lemma negb_eq_negb (b1 b2 : bool) : (~~ b1 = ~~ b2) -> (b1 = b2).
Proof. by case: b1; case: b2. Qed.


Lemma expn_pow n m : n ^ m = Nat.pow n m.
Proof.
  elim: m.
  - reflexivity.
  - move=> m IH. rewrite expnS (Nat.pow_succ_r _ _ (Nat.le_0_l m)) IH.
    reflexivity.
Qed.

Lemma exp2n_gt0 n : (0 < 2 ^ n).
Proof.
  elim: n => [| n IH] //=. rewrite -(addn1 n) expnD expn1.
  apply: (ltn_trans IH). apply: (ltn_Pmulr _ IH). done.
Qed.

Lemma Nat2Z_inj_pow (n m : nat) :
  Z.of_nat (Nat.pow n m) = Z.pow (Z.of_nat n) (Z.of_nat m).
Proof.
  elim: m n.
  - reflexivity.
  - move=> n IH m. rewrite Nat2Z.inj_mul IH -!Zpower_nat_Z -Zpower_nat_succ_r.
    reflexivity.
Qed.

Lemma ltn_geq_total n m : (n < m) || (m <= n).
Proof.
  case/orP: (leq_total n m).
  - rewrite leq_eqVlt. case/orP.
    + move/eqP=> ->. rewrite leqnn orbT. reflexivity.
    + move=> ->. rewrite orTb. reflexivity.
  - move=> ->. rewrite orbT. reflexivity.
Qed.

Lemma leq_gtn_total n m : (n <= m) || (m < n).
Proof.
  move: (ltn_geq_total m n). by case/orP => ->; [rewrite orbT | rewrite orTb].
Qed.

Lemma ltn_leq_trans n m p : m < n -> n <= p -> m < p.
Proof.
  move=> Hmn Hnp. move/ltP: Hmn => Hmn. move/leP: Hnp => Hnp. apply/ltP.
  exact: (Lt.lt_le_trans _ _ _ Hmn Hnp).
Qed.

Lemma sub_diff_add_rdiff m n : n - (n - m) + (m - n) = m.
Proof.
  case/orP: (leq_total n m) => H.
  - rewrite -subn_eq0 in H. rewrite (eqP H) subn0. rewrite subn_eq0 in H.
    exact: (subnKC H).
  - rewrite -subn_eq0 in H. rewrite (eqP H) addn0. rewrite subn_eq0 in H.
    exact: (subKn H).
Qed.



Lemma b2n_cons (b1 : bool) (n1 : nat) (b2 : bool) (n2 : nat) :
  (b1 + n1.*2 == b2 + n2.*2) = (b1 == b2) && (n1 == n2).
Proof.
  case H: (b1 + n1.*2 == b2 + n2.*2).
  - have: (b1 + n1.*2)./2 = (b2 + n2.*2)./2 by rewrite (eqP H).
    rewrite 2!half_bit_double => Hn. rewrite Hn eqn_add2r in H.
    move/eqP/nat_of_bool_inj: H => H. by rewrite Hn H !eqxx.
  - symmetry. apply/negP => /andP [Hb Hn]. rewrite (eqP Hb) (eqP Hn) eqxx in H.
    discriminate.
Qed.

Lemma b2n_eq0 (b : bool) (n : nat) : (b + n * 2 = 0) -> (nat_of_bool b = 0) /\ n = 0.
Proof.
  rewrite /nat_of_bool. case: b.
  - move=> H. apply: False_ind.
    have: (odd (1 + n * 2) = odd 0)%Z by rewrite H.
    rewrite odd_add. rewrite muln2 odd_double /=. discriminate.
  - rewrite add0n => /eqP H. rewrite muln_eq0 in H. by case/orP: H => /eqP H.
Qed.

Lemma b2z_cons (b1 : bool) (n1 : Z) (b2 : bool) (n2 : Z) :
  (Z.b2z b1 + n1 * 2 = Z.b2z b2 + n2 * 2)%Z -> (b1 = b2) /\ (n1 = n2).
Proof.
  move=> H. have: ((Z.b2z b1 + n1 * 2) / 2 = (Z.b2z b2 + n2 * 2) / 2)%Z by rewrite H.
  rewrite Z_div_plus; last by done. rewrite Z_div_plus; last by done.
  have: (Z.even (Z.b2z b1 + n1 * 2)%Z = Z.even (Z.b2z b2 + n2 * 2)%Z) by rewrite H.
  clear H. rewrite (Z.mul_comm n1) (Z.mul_comm n2). rewrite 2!Z.even_add_mul_2. 
  by case: b1; case: b2.
Qed.

Lemma b2z_eq0 (b : bool) (n : Z) :
  (Z.b2z b + n * 2 = 0)%Z -> (Z.b2z b = 0 /\ n = 0)%Z.
Proof.
  rewrite /Z.b2z. case: b.
  - move=> H. apply: False_ind.
    have: (Z.even (1 + n * 2) = Z.even 0)%Z by rewrite H.
    rewrite Z.mul_comm Z.even_add_mul_2. discriminate.
  - rewrite Z.add_0_l => H. by case: (Zmult_integral _ _ H).
Qed.

Lemma double_gt1 (n : nat) : 0 < n -> 1 < n.*2.
Proof. by elim: n. Qed.

Lemma bool_ltn_double (b : bool) (n : nat) : 0 < n -> b < n.*2.
Proof.
  move=> H. apply: (@leq_ltn_trans 1); last exact: (double_gt1 H). by case: b.
Qed.

Lemma b2n_high_ltn (b1 : bool) (n1 : nat) (b2 : bool) (n2 : nat) :
  n1 < n2 -> (b1 + n1.*2 < b2 + n2.*2).
Proof.
  move=> H. rewrite -(subnK (ltnW H)). rewrite doubleD addnA.
  rewrite ltn_add2r. rewrite ltn_addl; first reflexivity.
  apply: bool_ltn_double. rewrite subn_gt0. assumption.
Qed.

Lemma b2n_high_gtn_nltn (b1 : bool) (n1 : nat) (b2 : bool) (n2 : nat) :
  n2 < n1 -> (b1 + n1.*2 < b2 + n2.*2) = false.
Proof.
  move=> H. move: (b2n_high_ltn b2 b1 H) => H1.
  apply/negP => H2. move: (ltn_trans H1 H2). rewrite ltnn. discriminate.
Qed.

Lemma b2n_high_leq (b1 : bool) (n1 : nat) (b2 : bool) (n2 : nat) :
  n1 <= n2 -> ~~ b1 -> b2 -> (b1 + n1.*2 < b2 + n2.*2).
Proof.
  move=> Hn Hb1 Hb2. rewrite leq_eqVlt in Hn. case/orP: Hn => Hn.
  - rewrite (eqP Hn). rewrite ltn_add2r. move/negPf: Hb1 => ->. rewrite Hb2.
    reflexivity.
  - exact: (b2n_high_ltn b1 b2 Hn).
Qed.

Lemma b2n_high_geq_nltn1 (b1 : bool) (n1 : nat) (b2 : bool) (n2 : nat) :
  n2 <= n1 -> b1 -> (b1 + n1.*2 < b2 + n2.*2) = false.
Proof.
  move=> Hn ->. apply/negP/negP. rewrite -leqNgt. apply: leq_add.
  - by case: b2.
  - rewrite leq_double. exact: Hn.
Qed.

Lemma b2n_high_geq_nltn2 (b1 : bool) (n1 : nat) (b2 : bool) (n2 : nat) :
  n2 <= n1 -> ~~ b2 -> (b1 + n1.*2 < b2 + n2.*2) = false.
Proof.
  move=> Hn /negPf ->. apply/negP/negP. rewrite -leqNgt. apply:leq_add.
  - by case: b1.
  - rewrite leq_double. exact: Hn.
Qed.

Lemma b2n_cons_ltn (b1 : bool) (n1 : nat) (b2 : bool) (n2 : nat) :
  (b1 + n1.*2 < b2 + n2.*2) = ((n1 == n2) && ~~ b1 && b2 || (n1 < n2)).
Proof.
  case H: ((n1 == n2) && ~~ b1 && b2 || (n1 < n2)).
  - case/orP: H.
    + move=> /andP [/andP [Hn Hb1] Hb2]. move/negPf: Hb1 => Hb1.
      rewrite (eqP Hn) Hb1 Hb2 /=. rewrite ltn_add2r. reflexivity.
    + move=> Hn. exact: (b2n_high_ltn b1 b2 Hn).
  - move/Bool.orb_false_elim: H => [H1 H2]. case/Bool.andb_false_elim: H1 => H1.
    + case/Bool.andb_false_elim: H1 => H1.
      * move: (leq_eqVlt n1 n2). rewrite H1 H2 /=. move/negP/negP. rewrite -ltnNge.
        move=> {H1 H2} H. exact: (b2n_high_gtn_nltn b1 b2 H).
      * move/negPn: H1 => H1. move/negP/negP: H2. rewrite -leqNgt => H2.
        exact: (b2n_high_geq_nltn1 _ H2 H1).
    + move/negP/negP: H1 => H1. move/negP/negP: H2. rewrite -leqNgt => H2.
      exact: (b2n_high_geq_nltn2 _ H2 H1).
Qed.
