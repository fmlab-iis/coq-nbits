
From Coq Require Import ZArith Arith List Ascii String.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq.
From nbits Require Import AuxLemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Definitions.

  (* A bit-vector with LSB at the head and MSB at the last *)
  Definition bits : Set := bitseq.

  Definition b0 : bool := false.
  Definition b1 : bool := true.

  (* Size of bits *)

  Notation size := (@size bool).

  (* Concate two bit-vectors *)

  Notation cat := (@cat bool).

  Notation "lo ++# hi" := (cat lo hi) (at level 60, right associativity).

  (* Generating bits *)

  Definition copy (n : nat) (b : bool) : bits := nseq n b.
  Definition zeros (n : nat) : bits := copy n b0.
  Definition ones (n : nat) : bits := copy n b1.

  (* LSB and MSB *)

  Definition splitlsb (bs : bits) : (bool * bits) := (head b0 bs, behead bs).
  Definition splitmsb (bs : bits) : (bits * bool) :=
    match bs with
    | [::] => ([::], b0)
    | hd::tl => (belast hd tl, last hd bs)
    end.
  Definition droplsb (bs : bits) : bits := (splitlsb bs).2.
  Definition dropmsb (bs : bits) : bits := (splitmsb bs).1.
  Definition joinlsb (lsb : bool) (bs : bits) := lsb::bs.
  Definition joinmsb (bs : bits) (msb : bool) := rcons bs msb.
  Definition lsb (bs : bits) : bool := (splitlsb bs).1.
  Definition msb (bs : bits) : bool := (splitmsb bs).2.

  (* High and low *)

  Definition high (n : nat) (bs : bits) : bits := drop (size bs - n) bs.
  Definition low (n : nat) (bs : bits) : bits := take n bs.

  (* Extract a bit sequence from i to j where i >= j *)

  Definition extract (i j : nat) (bs : bits) : bits := high (i - j + 1) (low (i + 1) bs).

  (* Zero extension and sign extension *)

  Definition zext (n : nat) (bs : bits) : bits := bs ++# zeros n.
  Definition sext (n : nat) (bs : bits) : bits := bs ++# copy n (msb bs).

  (* Conversion from bits to nat, N, and Z. *)

  Definition N_of_bool (b : bool) : N := if b then Npos xH
                                         else N0.
  Definition Z_of_bool (b : bool) : Z := if b then Zpos xH
                                         else Z0.
  Coercion N_of_bool : bool >-> N.
  Coercion Z_of_bool : bool >-> Z.

  Definition to_nat (bs : bits) : nat :=
    foldr (fun b res => nat_of_bool b + res.*2) 0 bs.
  Fixpoint from_nat (n : nat) (x : nat) : bits :=
    match n with
    | O => [::]
    | S m => joinlsb (odd x) (from_nat m x./2)
    end.
  Definition to_N (bs : bits) : N :=
    foldr (fun b res => (N_of_bool b + res * 2)%num) 0%num bs.
  Fixpoint from_N (n : nat) (x : N) : bits :=
    match n with
    | O => [::]
    | S m => joinlsb (N.odd x) (from_N m (N.div x 2))
    end.
  Definition to_Zpos (bs : bits) : Z :=
    foldr (fun b res => (Z_of_bool b + res * 2)%Z) 0%Z bs.
  Definition to_Zneg (bs : bits) : Z :=
    foldr (fun b res => (Z_of_bool (~~b) + res * 2)%Z) 0%Z bs.
  (* Convert a signed bit-vector to Z *)
  Definition to_Z (bs : bits) : Z :=
    match splitmsb bs with
    | (bs, false) => to_Zpos bs
    | (bs, true) => Z.opp (Z.succ (to_Zneg bs))
    end.
  Fixpoint from_Zpos (n : nat) (x : Z) : bits :=
    match n with
    | O => [::]
    | S m => joinlsb (Z.odd x) (from_Zpos m (Z.div2 x))
    end.
  Fixpoint from_Zneg (n : nat) (x : Z) : bits :=
    match n with
    | O => [::]
    | S m => joinlsb (Z.even x) (from_Zneg m (Z.div2 x))
    end.
  Definition from_Z (n : nat) (x : Z) : bits :=
    match x with
    | Zpos _ => from_Zpos n x
    | Zneg _ => from_Zneg n (Z.pred (Z.opp x))
    | _ => zeros n
    end.
  Arguments from_nat n x : simpl never.
  Arguments from_N n x : simpl never.
  Arguments from_Zpos n x : simpl never.
  Arguments from_Zneg n x : simpl never.
  Arguments from_Z n x : simpl never.

  (* Conversion from/to string *)

  Definition char_to_nibble c : bits :=
    from_nat 4 (findex 0 (String c EmptyString) "0123456789ABCDEF0123456789abcdef").
  Definition char_to_bit c : bool := ascii_dec c "1".
  Fixpoint from_bin (s : string) : bits :=
    match s with
    | EmptyString => [::]
    | String c s => joinmsb (from_bin s) (char_to_bit c)
    end.
  Fixpoint from_hex (s : string) : bits :=
    match s with
    | EmptyString => [::]
    | String c s => (char_to_nibble c) ++# (from_hex s)
    end.
  Fixpoint from_string (s : string) : bits :=
    match s with
    | EmptyString => [::]
    | String c s => from_string s ++# (from_nat 8 (nat_of_ascii c))
    end.
  Definition nibble_to_char (n : bits) :=
    match String.get (to_nat n) "0123456789ABCDEF" with
    | None => " "%char
    | Some c => c
    end.
  Definition append_nibble_on_string (n : bits) (s : string) : string :=
    (s ++ String (nibble_to_char n) EmptyString)%string.
  Fixpoint to_hex (bs : bits) : string :=
    match bs with
    | [::] => EmptyString
    | b1::[::] => append_nibble_on_string (zeros 3 ++# bs) EmptyString
    | b1::b2::[::] => append_nibble_on_string (zeros 2 ++# bs) EmptyString
    | b1::b2::b3::[::] => append_nibble_on_string (zeros 1 ++# bs) EmptyString
    | b1::b2::b3::b4::tl => append_nibble_on_string (b1::b2::b3::b4::[::]) (@to_hex tl)
    end.

End Definitions.

Delimit Scope bits_scope with bits.

Notation "lo ++# hi" := (cat lo hi) (at level 60, right associativity) : bits_scope.
Notation "n '-bits' 'of' m" := (from_nat n m) (at level 0) : bits_scope.
Notation "n '-bits' 'of' 'N' m" := (from_N n m) (at level 0) : bits_scope.
Notation "n '-bits' 'of' 'Z' m" := (from_Z n m) (at level 0) : bits_scope.

Section Lemmas.

  Local Open Scope bits_scope.

  Notation size := (@size bool).

  (* Lemmas about size *)

  Lemma size_cat lo hi : size (cat lo hi) = size lo + size hi.
  Proof. rewrite size_cat. reflexivity. Qed.

  Lemma size_copy n b : size (copy n b) = n.
  Proof. exact: size_nseq. Qed.

  Lemma size_zeros n : size (zeros n) = n.
  Proof. exact: size_nseq. Qed.

  Lemma size_ones n : size (ones n) = n.
  Proof. exact: size_nseq. Qed.

  Lemma size_splitlsb bs : size (splitlsb bs).2 = size bs - 1.
  Proof.
    destruct bs => /=.
    - reflexivity.
    - rewrite subn1 -pred_Sn. reflexivity.
  Qed.

  Lemma size_splitmsb bs : size (splitmsb bs).1 = size bs - 1.
  Proof.
    destruct bs => /=.
    - reflexivity.
    - rewrite subn1 -pred_Sn. rewrite size_belast. reflexivity.
  Qed.

  Lemma size_droplsb bs : size (droplsb bs) = size bs - 1.
  Proof. exact: size_splitlsb. Qed.

  Lemma size_dropmsb bs : size (dropmsb bs) = size bs - 1.
  Proof. exact: size_splitmsb. Qed.

  Lemma size_high bs n : n <= size bs -> size (high n bs) = n.
  Proof.
    move=> H. rewrite /high size_drop. rewrite (subKn H). reflexivity.
  Qed.

  Lemma size_low bs n : n <= size bs -> size (low n bs) = n.
  Proof.
    move=> H. rewrite /low size_take. rewrite leq_eqVlt in H. case/orP: H.
    - move/eqP => <-. rewrite ltnn. reflexivity.
    - move=> ->. reflexivity.
  Qed.

  Lemma size_extract bs i j :
    j <= i -> i < size bs -> size (extract i j bs) = i - j + 1.
  Proof.
    rewrite /extract => Hj Hi. rewrite size_high; first by reflexivity.
    rewrite size_low.
    - rewrite (addnBAC _ Hj). exact: leq_subr.
    - rewrite leqNgt. apply/negP => H. rewrite addn1 ltnS in H.
      move: (ltn_leq_trans Hi H). rewrite ltnn => Hfalse. discriminate.
  Qed.

  Lemma size_zext bs n : size (zext n bs) = size bs + n.
  Proof.
    rewrite /zext size_cat size_zeros. reflexivity.
  Qed.

  Lemma size_sext bs n : size (sext n bs) = size bs + n.
  Proof.
    rewrite /sext size_cat size_copy. reflexivity.
  Qed.

  Lemma size_from_nat n x : size (from_nat n x) = n.
  Proof.
    elim: n x => /=.
    - move=> _. reflexivity.
    - move=> n IH x. rewrite -/from_nat. rewrite IH. reflexivity.
  Qed.

  Lemma size_from_N n x : size (from_N n x) = n.
  Proof.
    elim: n x => /=.
    - move=> _. reflexivity.
    - move=> n IH x. rewrite -/from_N. rewrite IH. reflexivity.
  Qed.

  Lemma size_from_Zpos n x : size (from_Zpos n x) = n.
  Proof.
    elim: n x => /=.
    - move=> _. reflexivity.
    - move=> n IH x. rewrite -/from_Zpos. rewrite IH. reflexivity.
  Qed.

  Lemma size_from_Zneg n x : size (from_Zneg n x) = n.
  Proof.
    elim: n x => /=.
    - move=> _. reflexivity.
    - move=> n IH x. rewrite -/from_Zneg. rewrite IH. reflexivity.
  Qed.

  Lemma size_from_Z n x : size (from_Z n x) = n.
  Proof.
    case: x => /=.
    - rewrite /from_Z size_zeros. reflexivity.
    - move=> p. rewrite /from_Z size_from_Zpos. reflexivity.
    - move=> p. rewrite /from_Z size_from_Zneg. reflexivity.
  Qed.

  Lemma size_zext_mkss bs1 bs2 :
    size (zext (size bs2 - size bs1) bs1) =
    size (zext (size bs1 - size bs2) bs2).
  Proof.
    rewrite !size_zext. case/orP: (ltn_geq_total (size bs1) (size bs2)) => H.
    - move: (ltnW H) => Hle. rewrite -subn_eq0 in Hle. rewrite (eqP Hle) addn0.
      exact: (subnKC (ltnW H)).
    - rewrite (subnKC H). rewrite -subn_eq0 in H. rewrite (eqP H) addn0. reflexivity.
  Qed.

  (* Lemmas about zeros and ones *)

  Lemma zeros0 : zeros 0 = [::].
  Proof. reflexivity. Qed.

  Lemma ones0 : ones 0 = [::].
  Proof. reflexivity. Qed.

  Lemma zeros_cons n : b0::zeros n = zeros n.+1.
  Proof. reflexivity. Qed.

  Lemma ones_cons n : b1::ones n = ones n.+1.
  Proof. reflexivity. Qed.

  Lemma zeros_rcons n : rcons (zeros n) b0 = zeros n.+1.
  Proof. elim: n => [| n IHn] //=. rewrite zeros_cons IHn. reflexivity. Qed.

  Lemma ones_rcons n : rcons (ones n) b1 = ones n.+1.
  Proof. elim: n => [| n IHn] //=. rewrite ones_cons IHn. reflexivity. Qed.

  Lemma to_nat_zeros n : to_nat (zeros n) = 0.
  Proof. elim: n => //=. move=> n ->. reflexivity. Qed.

  Lemma to_nat_ones n : to_nat (ones n) = 2^n - 1.
  Proof.
    elim: n => //=. move=> n ->. rewrite doubleB addnBA.
    - rewrite addnC -subnBA; last by done. rewrite expnSr muln2. reflexivity.
    - rewrite leq_double expn_gt0. done.
  Qed.

  (* Lemmas about zext *)

  Lemma zext_nil n : zext n [::] = zeros n.
  Proof. by elim: n. Qed.

  Lemma zext0 bs : zext 0 bs = bs.
  Proof. rewrite /zext. rewrite cats0. reflexivity. Qed.

  Lemma zext_Sn n bs : zext n.+1 bs = zext n bs ++ [:: b0].
  Proof.
    elim: n => [| n IHn].
    - rewrite zext0. reflexivity.
    - rewrite IHn /zext. rewrite -catA -catA. rewrite (catA (zeros n)).
      rewrite (cats1 (zeros n)) zeros_rcons. rewrite cats1 zeros_rcons. reflexivity.
  Qed.

  Lemma zext_Sn_nil n : zext n.+1 [::] = b0::zext n [::].
  Proof. reflexivity. Qed.

  Lemma zext_cons n hd tl : zext n (hd::tl) = hd::(zext n tl).
  Proof. reflexivity. Qed.

  Lemma zext_rcons0 n bs : zext n (rcons bs b0) = rcons (zext n bs) b0.
  Proof.
    elim: n => [| n IHn] /=.
    - rewrite !zext0. reflexivity.
    - rewrite zext_Sn IHn. rewrite -cats1 -zext_Sn.
      rewrite cats1. reflexivity.
  Qed.

  Lemma zext_zext n m bs : zext n (zext m bs) = zext (n + m) bs.
  Proof.
    elim: n m bs => [| n IHn] m bs.
    - rewrite zext0 add0n. reflexivity.
    - rewrite zext_Sn IHn -zext_Sn. rewrite -addn1 -addnA (addnC m) addnA addn1.
      reflexivity.
  Qed.

  (* Lemmas about from_nat and to_nat *)

  Lemma to_nat_nil : to_nat [::] = 0.
  Proof. reflexivity. Qed.

  Lemma from_nat_to_nat bs : from_nat (size bs) (to_nat bs) = bs.
  Proof.
    elim: bs => /=.
    - reflexivity.
    - move=> hd tl IH. rewrite /from_nat -/from_nat. rewrite half_bit_double.
      rewrite IH. rewrite odd_add odd_double. by case hd.
  Qed.

  Lemma to_nat_bounded bs : to_nat bs < 2 ^ (size bs).
  Proof.
    elim: bs => /=.
    - done.
    - move=> hd tl. rewrite expnS mul2n. case: hd.
      + rewrite ltn_Sdouble. by apply.
      + rewrite ltn_double. by apply.
  Qed.

  Lemma to_nat_cat lo hi : to_nat (lo ++# hi) = to_nat lo + to_nat hi * 2 ^ (size lo).
  Proof.
    elim: lo => /=.
    - rewrite add0n expn0 muln1. reflexivity.
    - move=> hd tl IH. rewrite IH. rewrite expnS -!muln2. ring.
  Qed.

  Lemma to_nat_zero bs : (to_nat bs == 0) = (bs == zeros (size bs)).
  Proof.
    elim: bs => //=. move=> hd tl IH. case H: (to_nat tl).
    - move/eqP: H. rewrite IH => /eqP <-. rewrite -muln2 mul0n addn0. case: hd.
      + reflexivity.
      + rewrite 2!eqxx. reflexivity.
    - rewrite -addn1 -muln2 mulnDl addnA addn_eq0 andbF. symmetry.
      apply/negP => /eqP Hcons. case: Hcons => Hhd /eqP Htl. rewrite -IH in Htl.
      rewrite (eqP Htl) in H. discriminate.
  Qed.

  Lemma to_nat_inj bs1 bs2 :
    (to_nat bs1 == to_nat bs2) =
    (zext (size bs2 - size bs1) bs1 == zext (size bs1 - size bs2) bs2).
  Proof.
    elim: bs1 bs2 => [|hd1 tl1 IH1] [|hd2 tl2] //=.
    - rewrite zext_nil /=. rewrite sub0n zext0.
      rewrite eq_sym addn_eq0 double_eq0 to_nat_zero. rewrite nat_of_bool0.
      rewrite (eq_sym hd2) (eq_sym tl2). reflexivity.
    - rewrite zext_nil /=. rewrite sub0n zext0.
      rewrite addn_eq0 double_eq0 to_nat_zero. rewrite nat_of_bool0. reflexivity.
    - rewrite b2n_cons. rewrite 2!zext_cons.
      rewrite -(addn1 (size tl1)) -(addn1 (size tl2)) 2!subnDr.
      rewrite (IH1 tl2). reflexivity.
  Qed.

  Lemma to_nat_inj_ss bs1 bs2 :
    size bs1 = size bs2 -> (to_nat bs1 == to_nat bs2) = (bs1 == bs2).
  Proof. move=> Hs. rewrite to_nat_inj Hs subnn 2!zext0. reflexivity. Qed.

  Lemma to_nat_inj_rl bs1 bs2 :
    size bs1 <= size bs2 ->
    (to_nat bs1 == to_nat bs2) = (zext (size bs2 - size bs1) bs1 == bs2).
  Proof.
    move=> Hs. rewrite to_nat_inj. rewrite -subn_eq0 in Hs. rewrite (eqP Hs).
    rewrite zext0. reflexivity.
  Qed.

  Lemma to_nat_inj_ll bs1 bs2 :
    size bs2 <= size bs1 ->
    (to_nat bs1 == to_nat bs2) = (bs1 == zext (size bs1 - size bs2) bs2).
  Proof.
    move=> Hs. rewrite eq_sym. rewrite (to_nat_inj_rl Hs). rewrite eq_sym.
    reflexivity.
  Qed.

  Lemma to_nat_cons hd tl : to_nat (hd::tl) = hd + (to_nat tl).*2.
  Proof. reflexivity. Qed.

  Lemma to_nat_rcons bs la : to_nat (rcons bs la) = to_nat bs + la * 2^(size bs).
  Proof.
    elim: bs la => [|hd tl IH] la /=.
    - rewrite double0 expn0 muln1 add0n addn0. reflexivity.
    - rewrite IH. rewrite doubleD addnA. rewrite doubleMr.
      rewrite -(muln2 (2^size tl)) -expnSr. reflexivity.
  Qed.

  Lemma to_nat_zext n bs : to_nat (zext n bs) = to_nat bs.
  Proof.
    elim: n bs => [| n IHn] bs /=.
    - rewrite zext0. reflexivity.
    - rewrite zext_Sn cats1. rewrite to_nat_rcons IHn. rewrite mul0n addn0.
      reflexivity.
  Qed.

End Lemmas.
