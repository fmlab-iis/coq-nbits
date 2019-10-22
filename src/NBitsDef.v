
From Coq Require Import ZArith Arith List Ascii String.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq.
From nbits Require Import AuxLemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section Split.

  Context (A : Type).
  Context (d : A).

  Definition split_head (ls : seq A) : (A * seq A) := (head d ls, behead ls).
  Definition lastd (ls : seq A) :=
    match ls with
    | [::] => d
    | hd::tl => last hd tl
    end.
  Definition belastd (ls : seq A) :=
    match ls with
    | [::] => [::]
    | hd::tl => belast hd tl
    end.
  Definition split_last (ls : seq A) : (seq A * A) := (belastd ls, lastd ls).

  Lemma split_head_cons (l : A) (ls : seq A) : split_head (cons l ls) = (l, ls).
  Proof. reflexivity. Qed.

  Lemma lastd_rcons ls l : lastd (rcons ls l) = l.
  Proof. case: ls => [| hd tl] //=. by rewrite last_rcons. Qed.

  Lemma belastd_rcons ls l : belastd (rcons ls l) = ls.
  Proof. case: ls => [| hd tl] //=. by rewrite belast_rcons. Qed.

  Lemma split_last_rcons ls l : split_last (rcons ls l) = (ls, l).
  Proof. rewrite /split_last. by rewrite lastd_rcons belastd_rcons. Qed.

  Lemma split_last_nonempty (ls : seq A) :
    0 < size ls ->
    split_last ls = (belast (split_head ls).1 (split_head ls).2,
                     last (split_head ls).1 ls).
  Proof. by case: ls. Qed.

End Split.



Section Definitions.

  (* A bit-vector with LSB at the head and MSB at the last *)
  Definition bits : Set := bitseq.

  Definition b0 : bool := false.
  Definition b1 : bool := true.

  (* Size of bits *)

  Notation size := (@size bool).

  (* Generating bits *)

  Notation copy := nseq.
  Definition zeros (n : nat) : bits := copy n b0.
  Definition ones (n : nat) : bits := copy n b1.

  (* LSB and MSB *)

  Definition splitlsb (bs : bits) : (bool * bits) := split_head b0 bs.
  Definition splitmsb (bs : bits) : (bits * bool) := split_last b0 bs.
  Definition droplsb (bs : bits) : bits := (splitlsb bs).2.
  Definition dropmsb (bs : bits) : bits := (splitmsb bs).1.
  Definition joinlsb := @cons.
  Definition joinmsb := @rcons.
  Definition lsb (bs : bits) : bool := (splitlsb bs).1.
  Definition msb (bs : bits) : bool := (splitmsb bs).2.

  (* High and low *)

  Definition high (n : nat) (bs : bits) : bits :=
    drop (size bs - n) bs ++ zeros (n - size bs).
  Definition low (n : nat) (bs : bits) : bits :=
    take n bs ++ zeros (n - size bs).

  (* Extract a bit sequence from i to j where i >= j *)

  Definition extract (i j : nat) (bs : bits) : bits :=
    high (i - j + 1) (low (i + 1) bs).

  (* Slice m bits from a bit sequence from i *)

  Definition slice (i m : nat) (bs : bits) : bits :=
    extract i (i + m - 1) bs .

  (* Zero extension and sign extension *)

  Definition zext (n : nat) (bs : bits) : bits := bs ++ zeros n.
  Definition sext (n : nat) (bs : bits) : bits := bs ++ copy n (msb bs).

  (* All bits are 0 *)

  Definition is_zero (bs : bits) : bool := all (fun b => b == false) bs.

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
    | String c s => (char_to_nibble c) ++ (from_hex s)
    end.
  Fixpoint from_string (s : string) : bits :=
    match s with
    | EmptyString => [::]
    | String c s => from_string s ++ (from_nat 8 (nat_of_ascii c))
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
    | b1::[::] => append_nibble_on_string (zeros 3 ++ bs) EmptyString
    | b1::b2::[::] => append_nibble_on_string (zeros 2 ++ bs) EmptyString
    | b1::b2::b3::[::] => append_nibble_on_string (zeros 1 ++ bs) EmptyString
    | b1::b2::b3::b4::tl => append_nibble_on_string (b1::b2::b3::b4::[::]) (@to_hex tl)
    end.

End Definitions.

Delimit Scope bits_scope with bits.

Notation copy := nseq.
Notation "n '-bits' 'of' m" := (from_nat n m) (at level 0) : bits_scope.
Notation "n '-bits' 'of' 'N' m" := (from_N n m) (at level 0) : bits_scope.
Notation "n '-bits' 'of' 'Z' m" := (from_Z n m) (at level 0) : bits_scope.
Notation eta_expand x := (fst x, snd x).

Section Lemmas.

  Local Open Scope bits_scope.

  (* generalize type lemmas *)
  Lemma size_belastd T1 T2 (ls1: seq T1) (ls2:seq T2):
    size ls1 == size ls2 ->
    size (belastd ls1) == size (belastd ls2).
  Proof.
    elim: ls1 ls2 => [| ls_hd ls_tl IH] //=.
    - move=> ls2 Hsz0.
      move/eqP: Hsz0 => Hsz0.
      symmetry in Hsz0.
        by rewrite (size0nil Hsz0).
    - case => [| ls2_hd ls2_tl] //=.
        by rewrite !size_belast.
  Qed.

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

  Lemma size_high n bs : size (high n bs) = n.
  Proof. by rewrite /high size_cat size_drop size_zeros sub_diff_add_rdiff. Qed.

  Lemma size_low n bs : size (low n bs) = n.
  Proof.
    rewrite /low size_cat size_take size_zeros.
    case/orP: (ltn_geq_total n (size bs)) => H.
    - rewrite H. move: (ltnW H) => {H} H. rewrite -subn_eq0 in H.
      by rewrite (eqP H) addn0.
    - rewrite (leq_gtF H). by rewrite (subnKC H).
  Qed.

  Lemma size_extract i j bs : size (extract i j bs) = i - j + 1.
  Proof. by rewrite /extract size_high. Qed.

  Lemma size_zext n bs : size (zext n bs) = size bs + n.
  Proof. rewrite /zext size_cat size_zeros. reflexivity. Qed.

  Lemma size_sext n bs : size (sext n bs) = size bs + n.
  Proof. rewrite /sext size_cat size_copy. reflexivity. Qed.

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

  (* Lemmas about splitlsb, lsb, droplsb, splitmsb, msb, and dropmsb *)

  Lemma splitlsb_joinlsb b bs : splitlsb (joinlsb b bs) = (b, bs).
  Proof. exact: split_head_cons. Qed.

  Lemma splitmsb_joinmsb bs b : splitmsb (joinmsb bs b) = (bs, b).
  Proof. exact: split_last_rcons. Qed.

  Lemma splitmsb_rcons bs b : splitmsb (rcons bs b) = (bs, b).
  Proof. exact: split_last_rcons. Qed.

  Lemma droplsb_joinlsb b bs : droplsb (joinlsb b bs) = bs.
  Proof. reflexivity. Qed.

  Lemma dropmsb_joinmsb bs b : dropmsb (joinmsb bs b) = bs.
  Proof. by rewrite /dropmsb splitmsb_joinmsb. Qed.

  Lemma lsb_joinlsb b bs : lsb (joinlsb b bs) = b.
  Proof. reflexivity. Qed.

  Lemma msb_joinmsb bs b : msb (joinmsb bs b) = b.
  Proof. by rewrite /msb splitmsb_joinmsb. Qed.

  Lemma joinlsb_splitlsb bs :
    0 < size bs ->
    joinlsb (splitlsb bs).1 (splitlsb bs).2 = bs.
  Proof. by case: bs => //=. Qed.

  Lemma joinmsb_splitmsb bs :
    0 < size bs ->
    joinmsb (splitmsb bs).1 (splitmsb bs).2 = bs.
  Proof.
    case: bs => //=. move=> hd tl _. rewrite /joinmsb. rewrite -lastI. reflexivity.
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

  (* to_Zpos is always non-negative *)

  Lemma to_Zpos_ge0 bs : (0 <= to_Zpos bs)%Z.
  Proof.
    elim: bs => [| hd tl IH] //=. apply: Z.add_nonneg_nonneg.
    - by case: hd.
    - by apply: Z.mul_nonneg_nonneg.
  Qed.

  (* Relate to_nat, to_N, and to_PosZ *)

  Lemma to_nat_N bs : to_nat bs = N.to_nat (to_N bs).
  Proof.
    elim: bs => [| hd tl IH] //=. rewrite Nnat.N2Nat.inj_add  Nnat.N2Nat.inj_mul.
    rewrite -IH. replace (N.to_nat 2) with 2%N by reflexivity. rewrite -muln2.
    by case: hd.
  Qed.

  Lemma to_N_nat bs : to_N bs = N.of_nat (to_nat bs).
  Proof.
    elim: bs => [| hd tl IH] //=. rewrite Nnat.Nat2N.inj_add -muln2 Nnat.Nat2N.inj_mul.
    rewrite -IH. replace (N.of_nat 2) with 2%num by reflexivity. by case: hd.
  Qed.

  Lemma to_N_Zpos bs : to_N bs = Z.to_N (to_Zpos bs).
  Proof.
    elim: bs => [| hd tl IH] //=. have Hhd: (0 <= hd)%Z by case: hd.
    move: (@to_Zpos_ge0 tl) => Htl.
    have Htl2: (0 <= to_Zpos tl * 2)%Z by apply: (Z.mul_nonneg_nonneg _ _ Htl).
    rewrite (Z2N.inj_add _ _ Hhd Htl2). rewrite (Z2N.inj_mul _ _ Htl); [| by done].
    rewrite -IH /=. clear Hhd. by case: hd.
  Qed.

  Lemma to_Zpos_N bs : to_Zpos bs = Z.of_N (to_N bs).
  Proof.
    elim: bs => [| hd tl IH] //=. rewrite N2Z.inj_add N2Z.inj_mul -IH /=. by case: hd.
  Qed.

  Lemma to_nat_Zpos bs : to_nat bs = Z.to_nat (to_Zpos bs).
  Proof. by rewrite to_nat_N to_N_Zpos Z_N_nat. Qed.

  Lemma to_Zpos_nat bs : to_Zpos bs = Z.of_nat (to_nat bs).
  Proof. by rewrite to_Zpos_N to_N_nat nat_N_Z. Qed.

  (* Lemmas about is_zero *)

  Lemma is_zero_cons b bs : is_zero (b::bs) = ((b == false) && is_zero bs).
  Proof. reflexivity. Qed.

  Lemma is_zero_cat bs1 bs2 : is_zero (bs1 ++ bs2) = is_zero bs1 && is_zero bs2.
  Proof. by rewrite /is_zero all_cat. Qed.

  Lemma is_zero_rcons bs b : is_zero (rcons bs b) = (is_zero bs && (b == false)).
  Proof. by rewrite /is_zero all_rcons Bool.andb_comm. Qed.

  Lemma is_zero_to_nat bs : is_zero bs -> to_nat bs = 0.
  Proof.
    elim: bs => [| hd tl IH] //=. move/andP=> [H1 H2]. by rewrite (eqP H1) (IH H2).
  Qed.

  Lemma is_zero_to_N bs : is_zero bs -> to_N bs = 0%num.
  Proof. rewrite to_N_nat => H. by rewrite (is_zero_to_nat H). Qed.

  Lemma is_zero_to_Zpos bs : is_zero bs -> to_Zpos bs = 0%Z.
  Proof. rewrite to_Zpos_N => H. by rewrite (is_zero_to_N H). Qed.

  Lemma is_zero_to_Z bs : is_zero bs -> to_Z bs = 0%Z.
  Proof.
    case: (lastP bs) => {bs} [| bs b IH] //=. rewrite /to_Z splitmsb_rcons.
    rewrite is_zero_rcons in IH. move/andP: IH => [Hbs Hb]. rewrite (eqP Hb).
    exact: (is_zero_to_Zpos Hbs).
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

  Lemma from_natn0 n : from_nat n 0  = zeros n.
  Proof. elim: n => [| n IH] //=. by rewrite IH. Qed.

  Lemma from_nat0n n : from_nat 0 n = [::].
  Proof. reflexivity. Qed.

  Lemma to_nat_bounded bs : to_nat bs < 2 ^ (size bs).
  Proof.
    elim: bs => /=.
    - done.
    - move=> hd tl. rewrite expnS mul2n. case: hd.
      + rewrite ltn_Sdouble. by apply.
      + rewrite ltn_double. by apply.
  Qed.

  Lemma to_nat_cat lo hi : to_nat (lo ++ hi) = to_nat lo + to_nat hi * 2 ^ (size lo).
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
