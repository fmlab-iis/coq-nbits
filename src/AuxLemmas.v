
From Coq Require Import ZArith Arith List.
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
