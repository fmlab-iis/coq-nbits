
From Coq Require Import ZArith Arith List Ascii String.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq div.
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
    zeros (n - size bs) ++ drop (size bs - n) bs.
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

  (* Bit-wise negation *)

  Definition invB (bs : bits) : bits := map (fun b => ~~ b) bs.

  (* All bits are 0 *)

  Definition is_zero (bs : bits) : bool := all (fun b => b == false) bs.

  (* Conversion from bits to nat, N, and Z. *)

  Notation N_of_bool := N.b2n.
  Notation Z_of_bool := Z.b2z.

  Coercion N_of_bool : bool >-> N.
  Coercion Z_of_bool : bool >-> Z.

  Definition to_nat (bs : bits) : nat :=
    foldr (fun b res => nat_of_bool b + res.*2) 0 bs.
  Fixpoint from_nat (n : nat) (x : nat) : bits :=
    match n with
    | O => [::]
    | S m => joinlsb (odd x) (from_nat m x./2)
    end.
  Definition from_bool (n : nat) (b : bool) : bits := from_nat n b.
  Definition to_bool (bs : bits) : bool := ~~ is_zero bs.
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
  Arguments from_bool n b : simpl never.
  Arguments from_nat n x : simpl never.
  Arguments from_N n x : simpl never.
  Arguments from_Zpos n x : simpl never.
  Arguments from_Zneg n x : simpl never.
  Arguments from_Z n x : simpl never.

  (* Conversion from/to string *)

  Definition char_to_nibble c : bits :=
    from_nat 4 (findex 0 (String c EmptyString) "0123456789ABCDEF0123456789abcdef").
  Definition char_to_bit c : bool := ascii_dec c "1".
  (* Convert from binary string *)
  Fixpoint from_bin (s : string) : bits :=
    match s with
    | EmptyString => [::]
    | String c s => joinmsb (from_bin s) (char_to_bit c)
    end.
  (* Convert from HEX string *)
  Fixpoint from_hex (s : string) : bits :=
    match s with
    | EmptyString => [::]
    | String c s => (from_hex s) ++ (char_to_nibble c)
    end.
  Fixpoint Zpos_of_num_string_rec (res : Z) (s : string) : Z :=
    match s with
    | EmptyString => res
    | String c s =>
      Zpos_of_num_string_rec
        (res * 10 + Z.of_nat (nat_of_ascii c - nat_of_ascii "0"))%Z s
    end.
  Definition Zpos_of_num_string (s : string) : Z := Zpos_of_num_string_rec 0%Z s.
  (* Convert from (positive) number string *)
  Definition from_string (s : string) : bits :=
    let n := Zpos_of_num_string s in
    from_Z (Z.to_nat (Z.log2 n) + 1) n.
  Definition nibble_to_char (n : bits) :=
    match String.get (to_nat n) "0123456789ABCDEF" with
    | None => " "%char
    | Some c => c
    end.
  Definition append_nibble_on_string (n : bits) (s : string) : string :=
    (s ++ String (nibble_to_char n) EmptyString)%string.
  (* Convert to HEX string *)
  Fixpoint to_hex (bs : bits) : string :=
    match bs with
    | [::] => EmptyString
    | b1::[::] => append_nibble_on_string (bs ++ zeros 3) EmptyString
    | b1::b2::[::] => append_nibble_on_string (bs ++ zeros 2) EmptyString
    | b1::b2::b3::[::] => append_nibble_on_string (bs ++ zeros 1) EmptyString
    | b1::b2::b3::b4::tl => append_nibble_on_string (b1::b2::b3::b4::[::]) (@to_hex tl)
    end.
  (* Convert to binary string *)
  Fixpoint to_bin (bs : bits) : string :=
    match bs with
    | [::] => EmptyString
    | b::bs => to_bin bs ++ (if b then "1"%string else "0"%string)
    end.

End Definitions.

Delimit Scope bits_scope with bits.

Notation copy := nseq.
Notation "n '-bits' 'of' 'bool' b" := (from_bool n b) (at level 0) : bits_scope.
Notation "n '-bits' 'of' 'nat' m" := (from_nat n m) (at level 0) : bits_scope.
Notation "n '-bits' 'of' 'N' m" := (from_N n m) (at level 0) : bits_scope.
Notation "n '-bits' 'of' 'Z' m" := (from_Z n m) (at level 0) : bits_scope.
Notation "n '-bits' 'of' m" := (from_nat n m) (at level 0) : bits_scope.
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

  Lemma size0 (bs : bitseq) :
    size bs = 0 -> bs == [::] .
  Proof .
    case : bs; done .
  Qed .

  Lemma size1 (bs : bitseq) :
    size bs = 1 -> ((bs == [:: false]) + (bs == [:: true])) .
  Proof .
    case : bs .
    - done .
    - move => b bs /eqP Heq /= .
      move : Heq .
      rewrite eqSS => Hs0 .
      move : (size0 (eqP Hs0)) => Hbs .
      rewrite (eqP Hbs) .
      case : b; [right | left]; done .
  Qed .

  Lemma size_cat lo hi : size (cat lo hi) = size lo + size hi.
  Proof. rewrite size_cat. reflexivity. Qed.

  Lemma size_copy n b : size (copy n b) = n.
  Proof. exact: size_nseq. Qed.

  Lemma size_zeros n : size (zeros n) = n.
  Proof. exact: size_nseq. Qed.

  Lemma size_ones n : size (ones n) = n.
  Proof. exact: size_nseq. Qed.

  Lemma size_splitlsb bs : size (splitlsb bs).2 = size bs - 1.
  Proof. rewrite /splitlsb /=. rewrite size_behead. by rewrite subn1. Qed.

  Lemma size_splitmsb bs : size (splitmsb bs).1 = size bs - 1.
  Proof.
    destruct bs => /=.
    - reflexivity.
    - rewrite subn1 -pred_Sn. rewrite size_belast. reflexivity.
  Qed.

  Lemma size_joinlsb b bs : size (joinlsb b bs) = size bs + 1.
  Proof. rewrite /joinlsb /=. by rewrite addn1. Qed.

  Lemma size_joinmsb bs b : size (joinmsb bs b) = size bs + 1.
  Proof. rewrite /joinmsb. rewrite size_rcons. by rewrite addn1. Qed.

  Lemma size_droplsb bs : size (droplsb bs) = size bs - 1.
  Proof. exact: size_splitlsb. Qed.

  Lemma size_dropmsb bs : size (dropmsb bs) = size bs - 1.
  Proof. exact: size_splitmsb. Qed.

  Lemma size_high n bs : size (high n bs) = n.
  Proof.
      by rewrite /high size_cat size_drop size_zeros addnC sub_diff_add_rdiff.
  Qed.

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

  Lemma size_invB bs : size (invB bs) = size bs.
  Proof. elim: bs => [| b bs IH] //=. by rewrite IH. Qed.

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

  Lemma msb_rcons bs b : msb (rcons bs b) = b.
  Proof. by rewrite /msb splitmsb_rcons. Qed.

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

  Lemma size1_lsb bs : size bs = 1 -> bs = [:: lsb bs].
  Proof. case: bs => [| b bs] //=. by case: bs => //=. Qed.

  Lemma size1_msb bs : size bs = 1 -> bs = [:: msb bs].
  Proof. by case: bs => [| b [| b' bs]]. Qed.

  Lemma droplsb_joinmsb bs b : 
    0 < size bs -> droplsb (joinmsb bs b) = joinmsb (droplsb bs) b.
  Proof. case: bs => [| a bs] //=. Qed.

  Lemma droplsb_dropmsb bs : droplsb (dropmsb bs) = dropmsb (droplsb bs).
  Proof.
    case: bs => [| b bs] //=. case: (lastP bs) => {bs} [| bs b'] //=.
    by rewrite {2}/droplsb /= -{1}rcons_cons /dropmsb !splitmsb_rcons /droplsb. 
  Qed.

  Lemma dropmsb_cons n b bs :
    size bs = n.+1 ->
    dropmsb (b::bs) == b::(dropmsb bs) .
  Proof .
    case bs; first done .
    move => c cs Hsz .
    by rewrite {1}/dropmsb /splitmsb /split_last /= .
  Qed .

  Lemma droplsb_cat bs1 bs2 : 
    0 < size bs1 -> droplsb (bs1 ++ bs2) = droplsb bs1 ++ bs2.
  Proof. by case: bs1. Qed.

  Lemma dropmsb_cat bs1 bs2 : 
    0 < size bs2 -> dropmsb (bs1 ++ bs2) = bs1 ++ dropmsb bs2.
  Proof. 
    elim: bs1 => [| b bs1 IH] //=. move=> Hsz. 
    have H : size (bs1 ++ bs2) = (size (bs1 ++ bs2)).-1.+1.
    { apply S_pred_pos. apply/ltP. rewrite size_cat. by apply ltn_addl. }
    by rewrite (eqP (dropmsb_cons _ H)) (IH Hsz).
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

  Lemma copy_addn A n1 n2 (x : A) :
    copy (n1 + n2) x = copy n1 x ++ copy n2 x.
  Proof. by rewrite cat_nseq /nseq /ncons iter_add. Qed.

  Lemma zeros_addn n m : zeros (n + m) = zeros n ++ zeros m.
  Proof. rewrite /zeros. exact: copy_addn. Qed.

  Lemma zeros_cats : forall m n, zeros m ++ zeros n = zeros (m + n).
  Proof. elim => [|m IH] n. done. by rewrite addSn -!zeros_cons cat_cons -IH. Qed.

  Lemma ones_addn n m : ones (n + m) = ones n ++ ones m.
  Proof. rewrite /ones. exact: copy_addn. Qed.

  Lemma to_nat_zeros n : to_nat (zeros n) = 0.
  Proof. elim: n => //=. move=> n ->. reflexivity. Qed.

  Lemma to_nat_ones n : to_nat (ones n) = 2^n - 1.
  Proof.
    elim: n => //=. move=> n ->. rewrite doubleB addnBA.
    - rewrite addnC -subnBA; last by done. rewrite expnSr muln2. reflexivity.
    - rewrite leq_double expn_gt0. done.
  Qed.

  Lemma zeros_from_nat n : zeros n = from_nat n b0.
  Proof. elim: n => [| n IH] //=. rewrite -IH. reflexivity. Qed.

  Lemma zeros_from_bool n : zeros n = from_bool n b0.
  Proof. exact: zeros_from_nat. Qed.

  Lemma zeros_from_N n : zeros n = from_N n 0%num.
  Proof. elim: n => [| n IH] //=. rewrite -IH. reflexivity. Qed.

  Lemma zeros_from_Z n : zeros n = from_Z n 0%Z.
  Proof. by elim: n => [| n IH] //=. Qed.

  Lemma zeros_from_Zpos n : zeros n = from_Zpos n 0%Z.
  Proof. elim: n => [| n IH] //=. rewrite -IH. reflexivity. Qed.

  Lemma msb_zeros n : msb (zeros n) = b0.
  Proof.
    elim: n => [| n IH] //=. rewrite zeros_cons -zeros_rcons. exact: msb_joinmsb.
  Qed.

  Lemma msb_ones n : 0 < n -> msb (ones n) = b1.
  Proof.
    case: n => [| n] //=. rewrite ones_cons -ones_rcons. move=> _.
    exact: msb_joinmsb.
  Qed.

  Lemma lsb_zeros n : lsb (zeros n) = b0.
  Proof. by case: n. Qed.

  Lemma lsb_ones n : 0 < n -> lsb (ones n) = b1.
  Proof. by case: n. Qed.

  Lemma drop_zeros n m : drop n (zeros m) = zeros (m - n).
  Proof. rewrite /zeros. rewrite drop_nseq. reflexivity. Qed.

  Lemma drop_ones n m : drop n (ones m) = ones (m - n).
  Proof. rewrite /ones. rewrite drop_nseq. reflexivity. Qed.

  Lemma take_zeros n m : take n (zeros m) = zeros (minn n m).
  Proof. rewrite /zeros. rewrite take_nseq. reflexivity. Qed.

  Lemma take_ones n m : take n (ones m) = ones (minn n m).
  Proof. rewrite /ones. rewrite take_nseq. reflexivity. Qed.

  Lemma joinlsb_false_zeros : forall n, joinlsb false (zeros n) = zeros n.+1.
  Proof. elim; done. Qed.


  (* Lemmas about copy *)

  Lemma copy_cons (b : bool) n : b::copy n b = copy (n.+1) b.
  Proof. reflexivity. Qed.

  Lemma copy_rcons (b : bool) n : rcons (copy n b) b = copy (n.+1) b.
  Proof.
    elim: n => [| n IH] //=. rewrite IH. rewrite copy_cons. reflexivity.
  Qed.

  Lemma rev_copy : forall n (b: bool), rev (copy n b) = copy n b.
  Proof.
    elim => [| ns IH] b. done.
    rewrite/=-{1}(IH b) rev_cons revK.
    case b. by rewrite-/b1 ones_rcons. by rewrite-/b0 zeros_rcons. 
  Qed.


  (* from_bool and to_bool *)

  Lemma from_bool_cat n b : from_bool n b = drop (n - 1) (copy n b) ++ zeros (n - 1).
  Proof.
    case: n => [| n] //=. rewrite subn1 -pred_Sn /from_bool.
    rewrite /from_nat -/from_nat /joinlsb. have ->: (b./2 = 0) by case: b.
    have ->: odd b = b by case: b. elim: n => [| n IH] //=.
    rewrite zeros_cons -zeros_rcons -cats1 catA -IH. rewrite -zeros_from_nat /joinlsb.
    rewrite zeros_cons -zeros_rcons -cats1 cat_cons. reflexivity.
  Qed.

  Lemma from_bool_bit b : from_bool 1 b = [:: b].
  Proof. by case: b. Qed.

  Lemma to_bool_bit b : to_bool [:: b] = b.
  Proof. by case: b. Qed.


  (* Lemmas about invB *)

  Lemma invB_zeros n : invB (zeros n) = ones n.
  Proof.
    elim: n => // n IH. by rewrite -zeros_cons -ones_cons /= IH.
  Qed.

  Lemma invB_ones n : invB (ones n) = zeros n.
  Proof.
    elim: n => // n IH. by rewrite -zeros_cons -ones_cons /= IH.
  Qed.

  Lemma invB_involutive bs : invB (invB bs) = bs.
  Proof.
    elim: bs => [| b bs IH] //=. rewrite IH. rewrite Bool.negb_involutive.
    reflexivity.
  Qed.

  Lemma invB_cat bs1 bs2 : invB (bs1 ++ bs2) = invB bs1 ++ invB bs2.
  Proof. rewrite /invB. rewrite map_cat. reflexivity. Qed.

  Lemma invB_cons b bs : invB (b::bs) = ~~b :: (invB bs).
  Proof. reflexivity. Qed.

  Lemma invB_rcons bs b : invB (rcons bs b) = rcons (invB bs) (~~b).
  Proof. rewrite /invB map_rcons. reflexivity. Qed.


  (* Lemmas about low and high *)

  Lemma cat_low_high bs n m :
    n + m = size bs -> low n bs ++ high m bs = bs.
  Proof.
    move=> H. rewrite /low /high. rewrite -H.
    rewrite -{2}(addn0 n) subnDl sub0n zeros0 cats0.
    rewrite -{1}(add0n m) subnDr sub0n zeros0 cat0s.
    rewrite -{2}(add0n m) subnDr subn0.
    rewrite cat_take_drop. reflexivity.
  Qed.

  Lemma high0 bs : high 0 bs = [::].
  Proof.
    rewrite /high. rewrite subn0 sub0n. rewrite drop_size zeros0. reflexivity.
  Qed.

  Lemma low0 bs : low 0 bs = [::].
  Proof.
    rewrite /low. rewrite sub0n. rewrite take0 zeros0. reflexivity.
  Qed.

  Lemma high_nil n : high n [::] = zeros n.
  Proof.
    rewrite /high. rewrite sub0n subn0 drop0 cats0. reflexivity.
  Qed.

  Lemma low_nil n : low n [::] = zeros n.
  Proof.
    rewrite /low. rewrite subn0 /take /=. reflexivity.
  Qed.

  Lemma high_rcons bs b n : high (n.+1) (rcons bs b) = rcons (high n bs) b.
  Proof.
    rewrite /high. rewrite size_rcons !subSS. case Hn: (n <= size bs).
    - rewrite -subn_eq0 in Hn. rewrite (eqP Hn) zeros0 /=.
      rewrite (drop_rcons (leq_subr _ _)). reflexivity.
    - move/idP/negP: Hn. rewrite -ltnNge => Hn. move: (ltnW Hn).
      rewrite -subn_eq0 => Hs. rewrite (eqP Hs) !drop0.
      rewrite rcons_cat. reflexivity.
  Qed.

  Lemma low_cons b bs n : low (n.+1) (b::bs) = b::(low n bs).
  Proof.
    rewrite /low. rewrite take_cons /=. rewrite subSS. reflexivity.
  Qed.

  Lemma high1_rcons bs b : high 1 (rcons bs b) = [::b].
  Proof.
    rewrite high_rcons. rewrite high0. reflexivity.
  Qed.

  Lemma low1_cons b bs : low 1 (b::bs) = [::b].
  Proof.
    rewrite /low /=. rewrite take0 /=. reflexivity.
  Qed.

  Lemma high1_joinmsb b bs : high 1 (joinmsb bs b) = [:: b].
  Proof. exact: high1_rcons. Qed.

  Lemma low_joinmsb b bs : low (size bs) (joinmsb bs b) = bs.
  Proof.
    elim: bs => [| c cs IH] //=. rewrite low_cons. rewrite IH. reflexivity.
  Qed.

  Lemma high_size bs : high (size bs) bs = bs.
  Proof.
    rewrite /high. rewrite subnn drop0 zeros0 cat0s. reflexivity.
  Qed.

  Lemma low_size bs : low (size bs) bs = bs.
  Proof.
    rewrite /low. rewrite take_size subnn zeros0 cats0. reflexivity.
  Qed.

  Lemma high_oversize bs n : size bs <= n -> high n bs = zeros (n - size bs) ++ bs.
  Proof.
    rewrite /high => H. rewrite -subn_eq0 in H. rewrite (eqP H) drop0.
    reflexivity.
  Qed.

  Lemma low_oversize bs n : size bs <= n -> low n bs = bs ++ zeros (n - size bs).
  Proof.
    rewrite /low => H. rewrite (take_oversize H). reflexivity.
  Qed.

  Lemma high_size_cat n bs1 bs2 : size bs2 = n -> high n (bs1 ++ bs2) = bs2.
  Proof.
    rewrite /high => <-. rewrite size_cat {2}addnC.
    rewrite addnC subnDA subnn sub0n zeros0 cat0s.
    rewrite -(addnBAC _ (leqnn (size bs2))) subnn add0n.
    rewrite (drop_size_cat _ (Logic.eq_refl (size bs1))). reflexivity.
  Qed.

  Lemma low_size_cat n bs1 bs2 : size bs1 = n -> low n (bs1 ++ bs2) = bs1.
  Proof.
    rewrite /low => <-. rewrite size_cat subnDA subnn sub0n cats0.
    rewrite (take_size_cat _ (Logic.eq_refl (size bs1))). reflexivity.
  Qed.

  Lemma high1_msb bs : high 1 bs = [:: msb bs].
  Proof.
    move: (lastP bs). case=> {bs} //=. move=> bs b.
    rewrite high_rcons. rewrite msb_joinmsb high0 /=. reflexivity.
  Qed.

  Lemma low1_lsb bs : low 1 bs = [:: lsb bs].
  Proof.
    case: bs => [| b bs] //=. rewrite lsb_joinlsb. rewrite /low /=.
    rewrite take0 cats0. reflexivity.
  Qed.

  Lemma msb_high bs n : 0 < n -> msb (high n bs) = msb bs.
  Proof.
    elim: n bs => [| n IHn] bs Hn //=. move: (lastP bs) Hn. case=> {bs} /=.
    - rewrite high_nil msb_zeros. reflexivity.
    - move=> bs b Hn. rewrite high_rcons. rewrite !msb_joinmsb. reflexivity.
  Qed.

  Lemma lsb_low bs n : 0 < n -> lsb (low n bs) = lsb bs.
  Proof.
    case: n => //=. move=> n _. by case: bs.
  Qed.

  Lemma high_zeros n m : high n (zeros m) = zeros n.
  Proof.
    case Hs: (size (zeros m) <= n).
    - rewrite (high_oversize Hs). rewrite -zeros_addn size_zeros.
      rewrite size_zeros in Hs. rewrite (subnK Hs). reflexivity.
    - rewrite size_zeros in Hs. move/idP/negP: Hs. rewrite -ltnNge => Hs.
      move: (subnK (ltnW Hs)) => Hm. rewrite -Hm zeros_addn.
      apply: high_size_cat. by rewrite size_zeros.
  Qed.

  Lemma low_zeros n m : low n (zeros m) = zeros n.
  Proof.
    case Hs: (size (zeros m) <= n).
    - rewrite (low_oversize Hs). rewrite -zeros_addn size_zeros.
      rewrite size_zeros in Hs. rewrite (subnKC Hs). reflexivity.
    - rewrite size_zeros in Hs. move/idP/negP: Hs. rewrite -ltnNge => Hs.
      move: (subnKC (ltnW Hs)) => Hm. rewrite -Hm zeros_addn.
      apply: low_size_cat. by rewrite size_zeros.
  Qed.

  Lemma highn_high1 bs n h : 0 < n -> high n bs = h -> high 1 bs = [:: msb h].
  Proof.
    move=> H1 H2. rewrite high1_msb. rewrite <- H2.
    rewrite (msb_high _ H1). reflexivity.
  Qed.

  Lemma lown_low1 bs n h : 0 < n -> low n bs = h -> low 1 bs = [:: lsb h].
  Proof.
    case: n => [| n] //=. move=> _. move=> <-. case: bs => [| b bs] //=.
    rewrite low_cons low0 low_cons lsb_joinlsb. reflexivity.
  Qed.

  Lemma highn_zeros_high1 bs n : 0 < n -> high n bs = zeros n -> high 1 bs = [:: b0].
  Proof.
    move=> Hn Hh. rewrite (highn_high1 Hn Hh). rewrite msb_zeros. reflexivity.
  Qed.

  Lemma high_low bs n m :
    n <= m -> m <= size bs ->
    high n (low m bs) = low n (high (size bs - m + n) bs).
  Proof.
    move=> Hn Hm. rewrite leq_eqVlt in Hm. case/orP: Hm => Hm.
    - rewrite (eqP Hm). rewrite low_size subnn add0n.
      have H: (n = size (high n bs)) by rewrite size_high.
      rewrite {2}H. rewrite low_size. reflexivity.
    - rewrite /high /low. rewrite !size_cat size_take size_drop !size_zeros.
      rewrite Hm. move: (ltnW Hm). rewrite -subn_eq0. move/eqP=> Hms. rewrite Hms /=.
      rewrite addn0 cats0. rewrite subnDA (subKn (ltnW Hm)).
      move: (subn_addn_leq Hn (ltnW Hm)) => H. rewrite -subn_eq0 in H.
      rewrite (eqP H). rewrite zeros0 cat0s add0n => {H}.
      have Hmn: m - n <= size bs.
      { rewrite -(subn0 (size bs)). apply: (leq_sub (ltnW Hm)). done. }
      rewrite (subnBA _ Hmn). rewrite (subnKC Hn). rewrite Hms cats0.
      move: (Hn). rewrite -subn_eq0. move/eqP=> Hnm. rewrite Hnm cat0s.
      exact: (drop_take Hn Hm).
  Qed.

  Lemma low_high bs n m :
    n <= m -> m <= size bs ->
    low n (high m bs) = high n (low (size bs - m + n) bs).
  Proof.
    move=> Hn Hm. move: (leq_addl (size bs - m) n) => H1.
    move: (subn_addn_leq Hn Hm) => H2. rewrite (high_low H1 H2).
    rewrite subnDA. rewrite (subKn Hm). rewrite (subnK Hn). reflexivity.
  Qed.

  Lemma high_high bs n m : n <= m -> high n (high m bs) = high n bs.
  Proof.
    elim: n m bs => [| n IHn] m bs /=.
    - move=> _. rewrite !high0. reflexivity.
    - move=> Hnm. rewrite -(ltn_predK Hnm). move: (lastP bs). case=> {bs} /=.
      + rewrite !high_nil. rewrite high_zeros. reflexivity.
      + move=> bs b. rewrite !high_rcons. rewrite IHn; first by reflexivity.
        rewrite -ltnS. rewrite (ltn_predK Hnm). assumption.
  Qed.

  Lemma low_low bs n m : n <= m -> low n (low m bs) = low n bs.
  Proof.
    elim: n m bs => [| n IHn] m bs /=.
    - rewrite !low0. reflexivity.
    - move=> Hnm. rewrite -(ltn_predK Hnm). case: bs => [| b bs] /=.
      + rewrite !low_nil. rewrite low_zeros. reflexivity.
      + rewrite !low_cons. rewrite IHn; first by reflexivity.
        rewrite -ltnS. rewrite (ltn_predK Hnm). assumption.
  Qed.

  Lemma high_zeros_le bs n m :
    m <= n -> high n bs = zeros n -> high m bs = zeros m.
  Proof.
    move=> Hnm Hn. have: (high m (high n bs) = high m (zeros n)) by rewrite Hn.
    rewrite (high_high _ Hnm) high_zeros. by apply.
  Qed.

  Lemma low_zeros_le bs n m :
    m <= n -> low n bs = zeros n -> low m bs = zeros m.
  Proof.
    move=> Hnm Hn. have: (low m (low n bs) = low m (zeros n)) by rewrite Hn.
    rewrite (low_low _ Hnm) low_zeros. by apply.
  Qed.

  Lemma high_cons bs b n : n <= size bs -> high n (b :: bs) = high n bs.
  Proof.
    move=> Hn. rewrite /high. 
    have Hn' : (n <= size (b :: bs)) by rewrite /=; apply (leq_trans Hn).
    rewrite (eqP Hn) (eqP Hn') zeros0 /=.
    by rewrite -addn1 -(addnBAC _ Hn) addn1.
  Qed.

  Lemma low_rcons bs b n : n <= size bs -> low n (rcons bs b) = low n bs.
  Proof.
    move=> Hn. rewrite /low.
    have Hn' : (n <= size (rcons bs b)) by rewrite size_rcons; apply (leq_trans Hn).
    rewrite (eqP Hn) (eqP Hn') zeros0 !cats0 -cats1 (takel_cat _ Hn). reflexivity.
  Qed.

  Lemma high_droplsb bs n : n < size bs -> high n (droplsb bs) = high n bs.
  Proof.
    case: bs => [| b bs] //=.
    move=> Hn. by rewrite /droplsb /= high_cons.
  Qed.

  Lemma low_dropmsb bs n : n < size bs -> low n (dropmsb bs) = low n bs.
  Proof.
    case: (lastP bs) => {bs} [| bs b] //=.
    rewrite size_rcons => Hn. by rewrite /dropmsb splitmsb_rcons low_rcons. 
  Qed.

  Lemma droplsb_high bs n : droplsb (high n.+1 bs) = high n bs.
  Proof.
    rewrite /high. case Hn : (n.+1 - size bs) => [| m].
    - rewrite zeros0 /= /droplsb /splitlsb /split_head /=.
      rewrite !drop_behead. move/eqP in Hn; rewrite subn_eq0 in Hn.
      move: (ltnW Hn); rewrite -subn_eq0 => /eqP -> /=.
      rewrite -(@subnSK n _ Hn). reflexivity.
    - rewrite droplsb_cat; last trivial. rewrite -Hn.
      have Hsz : 0 < n.+1 - size bs by rewrite Hn.
      rewrite subn_gt0 /leq subSS in Hsz. 
      rewrite subnS (eqP Hsz) (subSn Hsz) /droplsb /=. reflexivity.
  Qed.

  Lemma dropmsb_low bs n : dropmsb (low n.+1 bs) = low n bs.
  Proof.
    rewrite /low. case/orP: (leq_gtn_total n.+1 (size bs)) => Hn.
    - rewrite -subn_eq0 in Hn. rewrite (eqP Hn) zeros0 cats0.
      move: (ltnW Hn); rewrite -subn_eq0 => /eqP -> /=. rewrite cats0.
      rewrite (take_nth b0 Hn) /dropmsb splitmsb_rcons /=. reflexivity.
    - rewrite dropmsb_cat; last by rewrite size_zeros subn_gt0.
      rewrite subSn; last done. rewrite -zeros_rcons /dropmsb splitmsb_rcons /=.
      rewrite take_oversize; last exact: ltnW. 
      rewrite take_oversize; done.
  Qed.

  Lemma high_oversize_zeros bs n :
    size bs <= n -> high n bs = zeros n -> bs = zeros (size bs).
  Proof.
    move=> Hsz Hzeros. apply (f_equal (high (size bs))) in Hzeros.
    by rewrite (high_high _ Hsz) high_size high_zeros in Hzeros.
  Qed.

  Lemma high_ones_le_size bs n : high n bs == ones n -> n <= size bs.
  Proof.
    case/orP: (ltn_geq_total (size bs) n) => Hsz.
    - rewrite (high_oversize (ltnW Hsz)). move: Hsz; case: n => [| n] //= Hsz.
      rewrite -addn1 -(addnBAC) // addn1 //.
    - by trivial.
  Qed.

  (* to_Zpos and to_Zneg is always non-negative *)

  Lemma to_Zpos_ge0 bs : (0 <= to_Zpos bs)%Z.
  Proof.
    elim: bs => [| hd tl IH] //=. apply: Z.add_nonneg_nonneg.
    - by case: hd.
    - by apply: Z.mul_nonneg_nonneg.
  Qed.

  Lemma to_Zneg_ge0 bs : (0 <= to_Zneg bs)%Z.
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

  Lemma is_zero_singleton b : is_zero [:: b] = ~~ b.
  Proof. by case: b. Qed.

  Lemma not_is_zero_singleton b : ~~ is_zero [::b] = b.
  Proof. by case: b. Qed.

  Lemma zeros_is_zero n : is_zero (zeros n).
  Proof. by elim: n. Qed.

  Lemma is_zero_zeros bs : is_zero bs -> bs = zeros (size bs).
  Proof.
    elim: bs => [| b bs IH] //=. move/andP=> [H1 H2]. rewrite (eqP H1).
    rewrite (IH H2). rewrite size_zeros. reflexivity.
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

  Lemma msb_zext n bs : 0 < n -> msb (zext n bs) = b0.
  Proof.
    case: n => [| n] //=. move=> _. rewrite zext_Sn. rewrite cats1.
    exact: msb_joinmsb.
  Qed.

  Lemma zext_zext n m bs : zext n (zext m bs) = zext (n + m) bs.
  Proof.
    elim: n m bs => [| n IHn] m bs.
    - rewrite zext0 add0n. reflexivity.
    - rewrite zext_Sn IHn -zext_Sn. rewrite -addn1 -addnA (addnC m) addnA addn1.
      reflexivity.
  Qed.

  Lemma low_zext : forall n p, low (size p) (zext n p) = p.
  Proof.
    intros; by rewrite /low/zext size_cat subnDA subnn sub0n cats0 take_cat ltnn subnn take0 cats0. 
  Qed.

  Lemma zext_zero : forall m n, zext m (zeros n) = zeros (m + n).
  Proof. intros. by rewrite /zext zeros_cats addnC. Qed.


  (* Lemmas about sext *)

  Lemma sext_nil n : sext n [::] = zeros n.
  Proof. by elim: n. Qed.

  Lemma sext0 bs : sext 0 bs = bs.
  Proof. rewrite /sext. rewrite cats0. reflexivity. Qed.

  Lemma sext_Sn n bs : sext n.+1 bs = sext n bs ++ [:: msb bs].
  Proof.
    elim: n => [| n IHn].
    - rewrite sext0. reflexivity.
    - rewrite IHn /sext. rewrite -catA -catA. rewrite (catA (copy n (msb bs))).
      rewrite !cats1. rewrite -addn2. rewrite copy_addn. rewrite {2}/copy /=.
      rewrite -cat_rcons. rewrite cats1. reflexivity.
  Qed.

  Lemma sext_Sn_nil n : zext n.+1 [::] = b0::sext n [::].
  Proof. reflexivity. Qed.

  Lemma sext_cons n hd tl : tl != [::] -> sext n (hd::tl) = hd::(sext n tl).
  Proof. by case: tl. Qed.

  Lemma sext_rcons0 n bs : sext n (rcons bs b0) = rcons (zext n bs) b0.
  Proof.
    rewrite /sext /zext. rewrite msb_joinmsb rcons_cat.
    rewrite zeros_rcons -zeros_cons. rewrite -cat_rcons. reflexivity.
  Qed.

  Lemma msb_sext n bs : msb (sext n bs) = msb bs.
  Proof.
    elim: n => [| n IHn] /=.
    - rewrite sext0. reflexivity.
    - rewrite sext_Sn. rewrite cats1. exact: msb_joinmsb.
  Qed.

  Lemma sext_sext n m bs : sext n (sext m bs) = sext (n + m) bs.
  Proof.
    elim: n m bs => [| n IHn] m bs.
    - rewrite sext0 add0n. reflexivity.
    - rewrite sext_Sn IHn. rewrite msb_sext. rewrite -addn1.
      rewrite -addnA (addnC 1 m) addnA addn1 sext_Sn. reflexivity.
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

  Lemma to_nat_joinlsb a n : to_nat (joinlsb a n) = (to_nat n).*2 + a.
  Proof. by rewrite addnC. Qed.

  Lemma to_nat_droplsb n: to_nat (droplsb n) = (to_nat n)./2.
  Proof. elim n=>[|nhd ntl IH]/=. done.
         rewrite -div.divn2 div.divnDr. case nhd ; (rewrite/= div.divn_small; last done).
         rewrite add0n; by rewrite -!muln2 div.mulnK.
         rewrite add0n; by rewrite -!muln2 div.mulnK.
         rewrite div.dvdn2 odd_double; done.
  Qed.

  Lemma to_nat_joinmsb a n : to_nat (joinmsb n a) = a * 2^(size n) + to_nat n.
  Proof.
    move : a. elim n=>[|nhd ntl IH]a/=. by rewrite -muln2 mul0n !addn0 expn0 muln1.
    rewrite (IH a) -!muln2 mulnDl expnS; ring.
  Qed.

  Lemma to_nat_dropmsb n : to_nat (dropmsb (n)) = div.modn (to_nat n) (2^(size n).-1).
  Proof.
    rewrite-(revK n). case (rev n); first by rewrite/= div.modn1.
    intros. rewrite/dropmsb/splitmsb/=rev_cons belastd_rcons size_rcons.
    have->:((size (rev l)).+1.-1=size (rev l)) by rewrite-addn1-subn1 addnK.
    case b; rewrite to_nat_rcons.
    - by rewrite mul1n-div.modnDmr div.modnn addn0 (div.modn_small (to_nat_bounded (rev l))).
    - by rewrite mul0n addn0 (div.modn_small (to_nat_bounded (rev l))).
  Qed.

  (* Lemma lt1_eq0 : forall (n:nat), n<1 -> n=0. *)
  (* Proof. intros. induction n; try done. *)
  (* Qed. *)

  Lemma to_nat_from_nat_bounded : forall n m, m < 2^n -> to_nat (from_nat n m) = m.
  Proof.
    elim => [|ns IH] m /=. rewrite expn0. symmetry. exact : lt1_eq0.
    move: (IH m./2) => IHm. intros. rewrite IHm. apply odd_double_half.
    rewrite-ltn_double. rewrite-divn2-2!muln2. rewrite expnSr in H.
    exact : (leq_ltn_trans (leq_trunc_div m 2) H).
  Qed.

  Lemma from_nat_bounded_eq m1 m2 n : m1 < 2^n -> m2 < 2^n ->
                                      (m1==m2) = (from_nat n m1 == from_nat n m2).
  Proof.
    move => Hlt1 Hlt2. case E: (m1 == m2); case E': (from_nat n m1 == from_nat n m2) => //.
      by rewrite (eqP E) eq_refl in E'.
      rewrite -(to_nat_from_nat_bounded Hlt1) -(to_nat_from_nat_bounded Hlt2) in E.
        by rewrite (eqP E') eq_refl in E.
  Qed.

  Lemma from_nat_dhalf n m : joinlsb (odd m) (from_nat n m./2) = from_nat n.+1 m.
  Proof. done. Qed.

  Lemma from_nat_wrap n : forall m, from_nat n m = from_nat n (m + 2^n).
  Proof. induction n => //.
         rewrite expnS.
         move => m.
         case ODD: (odd m); rewrite /from_nat-/from_nat /=ODD odd_add odd_mul/=ODD/= halfD ODD/=.
         specialize (IHn m./2). by rewrite odd_mul/= add0n mul2n doubleK IHn.
         specialize (IHn m./2). by rewrite add0n mul2n doubleK IHn.
  Qed.

  Lemma from_nat_wrapMany n c : forall m, from_nat n m = from_nat n (m + c * 2^n).
  Proof. induction c => m. by rewrite mul0n addn0.
         rewrite mulSn (addnC (2^n)) addnA from_nat_wrap. rewrite IHc.
           by rewrite -addnA (addnC (2^n)) addnA.
  Qed.

  Lemma to_nat_mod p: to_nat p = div.modn (to_nat p) (2^(size p)).
  Proof. rewrite div.modn_small => //. apply to_nat_bounded. Qed.

  Lemma to_nat_from_nat n m : to_nat (from_nat n m) = div.modn m (2^n).
  Proof. have H:= div.divn_eq m (2^n). rewrite {1}H.
         have HH:= from_nat_wrapMany n (div.divn m (2^n)) (div.modn m (2^n)). rewrite addnC in HH. rewrite -HH.
         rewrite to_nat_from_nat_bounded. done. apply div.ltn_pmod. apply expn_gt0. Qed.


  (* Lemmas about to_Zpos *)

  Lemma to_Zpos_nil : to_Zpos [::] = 0%Z.
  Proof. reflexivity. Qed.

  Lemma to_Zpos_inj bs1 bs2 :
    to_Zpos bs1 = to_Zpos bs2 ->
    zext (size bs2 - size bs1) bs1 = zext (size bs1 - size bs2) bs2.
  Proof.
    rewrite 2!to_Zpos_nat. move=> Hn. move: (Nat2Z.inj _ _ Hn) => {Hn} /eqP Hn.
    rewrite to_nat_inj in Hn. exact: (eqP Hn).
  Qed.

  Lemma to_Zpos_inj_ss bs1 bs2 :
    size bs1 = size bs2 -> to_Zpos bs1 = to_Zpos bs2 -> bs1 = bs2.
  Proof.
    rewrite 2!to_Zpos_nat. move=> Hs Hn. move: (Nat2Z.inj _ _ Hn) => {Hn} Hn.
    apply/eqP. rewrite -(to_nat_inj_ss Hs). apply/eqP. assumption.
  Qed.

  Lemma to_Zpos0 bs : (to_Zpos bs = 0)%Z -> (bs = zeros (size bs)).
  Proof.
    rewrite to_Zpos_nat -Nat2Z.inj_0 => H. move: (Nat2Z.inj _ _ H) => {H} /eqP H.
    rewrite to_nat_zero in H. exact: (eqP H).
  Qed.

  Lemma to_Zpos1 bs : (to_Zpos bs = 1)%Z -> bs = b1::zeros (size bs - 1).
  Proof.
    case: bs => [| b bs] //=. rewrite subn1 -pred_Sn.
    rewrite -(Z.add_0_r 1) -(Z.mul_0_l 2). replace 1%Z with (Z.b2z b1) by reflexivity.
    move=> H. move: (b2z_cons H) => {H} [H1 H2]. rewrite H1 -(to_Zpos0 H2).
    reflexivity.
  Qed.

  Lemma to_Zpos_zeros n : to_Zpos (zeros n) = 0%Z.
  Proof.
    elim: n => [| n IHn] //=. rewrite IHn Z.mul_0_l. reflexivity.
  Qed.

  Lemma to_Zpos_ones n : to_Zpos (ones n) = (Z.pow 2 (Z.of_nat n) - 1)%Z.
  Proof.
    rewrite to_Zpos_nat. rewrite to_nat_ones.
    have Hn: (1 <= 2 ^ n)%coq_nat. { apply/leP. exact: exp2n_gt0. }
    rewrite (Nat2Z.inj_sub _ _ Hn) /=. rewrite Nat2Z_inj_expn /=.
    reflexivity.
  Qed.

  Lemma to_Zpos_cat bs1 bs2 :
    to_Zpos (bs1 ++ bs2) = (to_Zpos bs1 + to_Zpos bs2 * 2 ^ (Z.of_nat (size bs1)))%Z.
  Proof.
    rewrite to_Zpos_nat to_nat_cat. rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z_inj_expn.
    rewrite -!to_Zpos_nat. reflexivity.
  Qed.

  Lemma to_Zpos_low_high bs n m :
    n + m = size bs -> 
    to_Zpos bs = (to_Zpos (low n bs) + to_Zpos (high m bs) * 2 ^ Z.of_nat n)%Z.
  Proof.
    move=> Hsz. by rewrite -{1}(cat_low_high Hsz) to_Zpos_cat size_low.
  Qed.

  Lemma to_Zpos_rcons bs b :
    to_Zpos (rcons bs b) = (to_Zpos bs + b * 2 ^ (Z.of_nat (size bs)))%Z.
  Proof.
    rewrite to_Zpos_nat to_nat_rcons Nat2Z.inj_add Nat2Z.inj_mul Nat2Z_inj_expn.
    rewrite -!to_Zpos_nat. by case: b.
  Qed.

  Lemma to_Zpos_invB bs : to_Zpos (invB bs) = to_Zneg bs.
  Proof.
    elim: bs => [| b bs IH] //=. rewrite -IH. reflexivity.
  Qed.

  Lemma to_Zpos_zext bs n : to_Zpos (zext n bs) = to_Zpos bs.
  Proof.
    rewrite to_Zpos_nat to_nat_zext -to_Zpos_nat. reflexivity.
  Qed.

  Lemma high1_0_to_Zpos_sext bs n :
    high 1 bs = [:: b0] -> to_Zpos (sext n bs) = to_Zpos bs.
  Proof.
    move: (lastP bs). case => {bs} /=.
    - rewrite sext_nil to_Zpos_zeros. reflexivity.
    - move=> bs b. rewrite high1_rcons. case => ->.
      rewrite /sext. rewrite msb_joinmsb. rewrite to_Zpos_cat to_Zpos_zeros /=.
      rewrite Z.add_0_r. reflexivity.
  Qed.

  Lemma high_zeros_to_Zpos_low_eq bs n :
    high (size bs - n) bs = zeros (size bs - n) ->
    to_Zpos (low n bs) = to_Zpos bs.
  Proof.
    case/orP: (AuxLemmas.ltn_geq_total n (size bs)) => Hs.
    - move: (@cat_low_high bs n (size bs - n)). rewrite (subnKC (ltnW Hs)) => H.
      move: (H (Logic.eq_refl (size bs))) => {H} H. rewrite -{5}H.
      move=> ->.  rewrite to_Zpos_cat to_Zpos_zeros Z.mul_0_l Z.add_0_r.
      reflexivity.
    - move=> _. rewrite (low_oversize Hs). rewrite to_Zpos_cat.
      rewrite to_Zpos_zeros Z.mul_0_l Z.add_0_r. reflexivity.
  Qed.

  Lemma to_Zpos_bounded bs : (to_Zpos bs < 2 ^ Z.of_nat (size bs))%Z.
  Proof.
    rewrite to_Zpos_nat. 
    have->: 2%Z = Z.of_nat 2 by trivial.
    rewrite -Nat2Z_inj_expn -(Nat2Z.inj_lt). apply/ltP; exact: to_nat_bounded. 
  Qed.

  Lemma high_zeros_to_Zpos_bounded bs n :
    high n bs = zeros n -> (to_Zpos bs < 2 ^ Z.of_nat (size bs - n))%Z.
  Proof.
    case Hsz : (size bs <= n).
    - rewrite (high_oversize Hsz) => Hzeros.
      apply (f_equal (high (size bs))) in Hzeros; move: Hzeros.
      rewrite high_size_cat; last by trivial.
      rewrite high_zeros => ->. rewrite to_Zpos_zeros.
      apply Z.pow_pos_nonneg; [done | exact: Nat2Z.is_nonneg].
    - move=> Hhighn.
      rewrite -(@high_zeros_to_Zpos_low_eq bs (size bs - n)).
      + move: (to_Zpos_bounded (low (size bs - n) bs)). by rewrite size_low.
      + rewrite subKn; first done. apply ltnW. 
        rewrite leqNgt in Hsz. apply negbT in Hsz. by rewrite negbK in Hsz.
  Qed.

  Lemma high_zeros_to_Zpos_mul_pow2_bounded bs n :
    high n bs = zeros n -> (to_Zpos bs * 2 ^ Z.of_nat n < 2 ^ Z.of_nat (size bs))%Z.
  Proof.
    case Hsz : (size bs <= n).
    - rewrite (high_oversize Hsz) => Hzeros.
      apply (f_equal (high (size bs))) in Hzeros; move: Hzeros.
      rewrite high_size_cat; last by trivial.
      rewrite high_zeros => ->. rewrite to_Zpos_zeros.
      apply Z.pow_pos_nonneg; [done | exact: Nat2Z.is_nonneg].
    - move=> Hhighn.
      move: (high_zeros_to_Zpos_bounded Hhighn) => Hbs.
      rewrite leqNgt in Hsz. apply negbT in Hsz. 
      rewrite negbK in Hsz. apply ltnW in Hsz.
      have->: size bs = size bs - n + n by rewrite subnK.
      rewrite Nat2Z.inj_add. rewrite Z.pow_add_r; try exact: Nat2Z.is_nonneg.
      apply Zmult_lt_compat_r; last done.
      apply Z.pow_pos_nonneg; [done | exact: Nat2Z.is_nonneg].
  Qed.

  Lemma to_Zpos_dropmsb bs : 
    to_Zpos (dropmsb bs) = ((to_Zpos bs) mod (2 ^ (Z.of_nat (size bs) - 1)))%Z.
  Proof.
    case (lastP bs) => {bs} [| bs b] //=.
    rewrite /dropmsb splitmsb_rcons /= to_Zpos_rcons size_rcons.
    rewrite Nat2Z.inj_succ -Z.add_1_r Z.add_simpl_r Z.mod_add.
    - rewrite Z.mod_small; first reflexivity. 
      split; [exact: to_Zpos_ge0 | exact: to_Zpos_bounded].
    - apply Z.pow_nonzero; [ done | exact: Nat2Z.is_nonneg ].
  Qed.

  Lemma to_Zpos_joinlsb b bs : to_Zpos (joinlsb b bs) = ((to_Zpos bs) * 2 + b)%Z.
  Proof.
    case: bs => [| x bs] /=; [rewrite Z.add_0_r | rewrite Z.add_comm]; done.
  Qed.

  Lemma to_Zpos_div_pow2 bs n :
    (to_Zpos bs / 2 ^ Z.of_nat n)%Z = to_Zpos (high (size bs - n) bs).
  Proof.
    case/orP: (ltn_geq_total (size bs) n) => Hsz.
    - have Hbnd : (0 <= to_Zpos bs < 2 ^ Z.of_nat n)%Z.
      {
        split.
        + exact: to_Zpos_ge0.
        + apply (Z.lt_trans _ _ _ (to_Zpos_bounded bs)).
          apply Z.pow_lt_mono_r; try done. 
          * exact: Nat2Z.is_nonneg.
          * rewrite -Nat2Z.inj_lt. by apply/ltP. 
      }
      rewrite (Z.div_small _ _ Hbnd). apply ltnW in Hsz. rewrite -subn_eq0 in Hsz.
      rewrite (eqP Hsz) high0. reflexivity.
    - move: (@to_Zpos_low_high bs n (size bs - n)).
      rewrite (subnKC Hsz) => H. move: (H (eqP (eqxx (size bs)))) => {H} H.
      rewrite Z.add_comm Z.mul_comm in H. apply Logic.eq_sym.
      apply: (Z.div_unique_pos _ _ _ _ _ H). split.
      + exact: to_Zpos_ge0.
      + have{2}<-: size (low n bs) = n by rewrite size_low. exact: to_Zpos_bounded.
  Qed.

  Lemma to_Zpos_mod_pow2 bs n :
    (to_Zpos bs mod 2 ^ Z.of_nat n)%Z = to_Zpos (low n bs).
  Proof.
    rewrite Z.mod_eq. 
    - rewrite to_Zpos_div_pow2. Check to_Zpos_low_high.
      case/orP: (leq_total n (size bs)) => Hsz.
      + rewrite (@to_Zpos_low_high bs n (size bs - n)); last by rewrite (subnKC Hsz).
        rewrite Z.mul_comm Z.add_simpl_r. reflexivity.
      + rewrite (low_oversize Hsz) to_Zpos_zext. rewrite -subn_eq0 in Hsz. 
        rewrite (eqP Hsz) high0 /= Z.mul_0_r Z.sub_0_r. reflexivity.
    - apply Z.pow_nonzero; [done | exact: Nat2Z.is_nonneg].
  Qed.

  Lemma to_Zpos_div_eucl_pow2 bs n :
    Z.div_eucl (to_Zpos bs) (2 ^ Z.of_nat n) = 
    (to_Zpos (high (size bs - n) bs), to_Zpos (low n bs)).
  Proof.
    by rewrite eta_expand_Z_div_eucl to_Zpos_div_pow2 to_Zpos_mod_pow2.
  Qed.

  (* Lemmas about to_Zneg *)

  Lemma to_Zneg_nil : to_Zneg [::] = 0%Z.
  Proof. reflexivity. Qed.

  Lemma to_Zpos_add_to_Zneg bs :
    (to_Zpos bs + to_Zneg bs)%Z = (Z.pow 2 (Z.of_nat (size bs)) - 1)%Z.
  Proof.
    elim: bs => [| b1 [| b2 bs]] //=.
    - move=> _. by case: b1.
    - move=> Hs. replace (b1 + (b2 + to_Zpos bs * 2) * 2 +
                          (~~ b1 + (~~ b2 + to_Zneg bs * 2) * 2))%Z with
                     ((b2 + to_Zpos bs * 2 + (~~ b2 + to_Zneg bs * 2)) * 2 +
                      (b1 + ~~ b1))%Z by ring. rewrite Hs.
      rewrite /Z.pow_pos. rewrite Pos.iter_succ.
      replace (2 * Pos.iter (Z.mul 2) 1 (Pos.of_succ_nat (size bs)) - 1)%Z with
          (2 * (Pos.iter (Z.mul 2) 1 (Pos.of_succ_nat (size bs)) - 1) + 1)%Z by ring.
      set n := (Pos.iter (Z.mul 2) 1 (Pos.of_succ_nat (size bs)) - 1)%Z.
      have ->: (b1 + ~~ b1)%Z = 1%Z by case: b1. ring.
  Qed.

  Lemma to_Zneg0 bs : (to_Zneg bs = 0)%Z -> bs = ones (size bs).
  Proof.
    move=> H0. move: (to_Zpos_add_to_Zneg bs). rewrite H0 Z.add_0_r.
    rewrite -(to_Zpos_ones (size bs)) => H. move: (to_Zpos_inj H).
    rewrite size_ones. rewrite subnn !zext0. by apply.
  Qed.

  Lemma to_Zneg1 bs : (to_Zneg bs = 1)%Z -> bs = b0::(copy (size bs - 1) b1).
  Proof.
    elim: bs => [| b bs IH] //=. rewrite -(Z.add_0_r 1) -(Z.mul_0_l 2) => Hz.
    replace 1%Z with (Z.b2z true) in Hz by reflexivity.
    move: (b2z_cons Hz) => {Hz} [Hz1 Hz2]. rewrite subn1 -pred_Sn.
    rewrite -/(ones (size bs)). rewrite -(to_Zneg0 Hz2). move: Hz1. by case: b.
  Qed.

  Lemma to_Zneg_zeros n : to_Zneg (zeros n) = (Z.pow 2 (Z.of_nat n) - 1)%Z.
  Proof.
    move: (to_Zpos_add_to_Zneg (zeros n)). rewrite size_zeros. move=> <-.
    rewrite to_Zpos_zeros Z.add_0_l. reflexivity.
  Qed.

  Lemma to_Zneg_ones n : to_Zneg (ones n) = 0%Z.
  Proof.
    move: (to_Zpos_add_to_Zneg (ones n)). rewrite size_ones. rewrite to_Zpos_ones.
    move/Z.add_move_l. rewrite Z.sub_diag. by apply.
  Qed.

  Lemma to_Zneg_inj_ss bs1 bs2 :
    size bs1 = size bs2 -> to_Zneg bs1 = to_Zneg bs2 -> bs1 = bs2.
  Proof.
    elim: bs1 bs2 => [| b1 bs1 IH] [| b2 bs2] //=. move=> Hs Hn.
    move: (Nat.succ_inj _ _ Hs) => {Hs} Hs. move: (b2z_cons Hn) => [H1 H2].
    move: (IH _ Hs H2) => ->. move: {Hn Hs H2} H1. by case: b1; case: b2.
  Qed.

  Lemma to_Zneg_is_bool bs1 b1 b2 :
    to_Zneg (b1::bs1) = (~~ b2)%Z -> bs1 = copy (size bs1) true /\ b1 = b2.
  Proof.
    case: b2.
    - move=> H. move: (to_Zneg0 H). rewrite /=. case=> -> ->.
      rewrite size_ones. done.
    - move=> H. move: (to_Zneg1 H). rewrite /=. rewrite subn1 -pred_Sn.
      case=> -> ->. rewrite size_copy. done.
  Qed.

  Lemma to_Zneg_inj_rl bs1 bs2 :
    size bs1 <= size bs2 -> to_Zneg bs1 = to_Zneg bs2 ->
    bs2 = bs1 ++ copy (size bs2 - size bs1) b1.
  Proof.
    elim: bs1 bs2 => [| b1 bs1 IH1] bs2 /=.
    - move=> _ H. move: (Logic.eq_sym H) => {H} H. rewrite subn0.
      rewrite {1}(to_Zneg0 H). reflexivity.
    - case: bs2 => [| b2 bs2] //=. move=> Hs Hz. rewrite ltnS in Hs.
      move: (b2z_cons Hz) => {Hz} [Hz1 Hz2]. move: (negb_eq_negb Hz1) => {Hz1} Hz1.
      rewrite -(addn1 (size bs2)) -(addn1 (size bs1)) subnDr.
      rewrite -(IH1 _ Hs Hz2). rewrite Hz1; reflexivity.
  Qed.

  Lemma to_Zneg_inj bs1 bs2 :
    to_Zneg bs1 = to_Zneg bs2 ->
    bs1 ++ copy (size bs2 - size bs1) b1 = bs2 ++ copy (size bs1 - size bs2) b1.
  Proof.
    case Hs: (size bs1 <= size bs2) => Hz.
    - rewrite -(to_Zneg_inj_rl Hs Hz). rewrite -subn_eq0 in Hs.
      rewrite (eqP Hs) /=. rewrite cats0. reflexivity.
    - move/idP/negP: Hs. rewrite -ltnNge => Hs. move: (ltnW Hs) => {Hs} Hs.
      move: (Logic.eq_sym Hz) => {Hz} Hz. rewrite -(to_Zneg_inj_rl Hs Hz).
      rewrite -subn_eq0 in Hs. rewrite (eqP Hs) /=. rewrite cats0. reflexivity.
  Qed.

  Lemma to_Zneg_rcons bs b :
    to_Zneg (rcons bs b) = (to_Zneg bs + (~~b) * 2 ^ (Z.of_nat (size bs)))%Z.
  Proof.
    elim: bs b => [| hd tl IH] la /=.
    - rewrite Z.add_0_r Z.mul_1_r. reflexivity.
    - rewrite IH. rewrite Zpower_pos_nat Zpower_nat_Z SuccNat2Pos.id_succ.
      rewrite -addn1 Nat2Z.inj_add /=.
      rewrite (Z.pow_add_r _ _ _ (Nat2Z.is_nonneg (size tl))); last by done.
      rewrite -Z.add_assoc Z.mul_assoc. rewrite -Z.mul_add_distr_r. reflexivity.
  Qed.

  Lemma to_Zneg_invB bs : to_Zneg (invB bs) = to_Zpos bs.
  Proof.
    rewrite -{2}(invB_involutive bs). rewrite to_Zpos_invB. reflexivity.
  Qed.

  Lemma to_Zneg_cat bs1 bs2 :
    to_Zneg (bs1 ++ bs2) = (to_Zneg bs1 + to_Zneg bs2 * 2 ^ (Z.of_nat (size bs1)))%Z.
  Proof.
    rewrite -(to_Zpos_invB (bs1 ++ bs2)). rewrite invB_cat to_Zpos_cat.
    rewrite !to_Zpos_invB size_invB. reflexivity.
  Qed.

  Lemma high_ones_to_Zneg_low_eq bs n :
    n <= size bs -> high (size bs - n) bs = ones (size bs - n) -> 
    to_Zneg (low n bs) = to_Zneg bs.
  Proof.
    move=> Hsz.
    move: (@cat_low_high bs n (size bs - n)). rewrite (subnKC Hsz) => H.
    move: (H (Logic.eq_refl (size bs))) => {H} H. rewrite -{5}H.
    move=> ->.  rewrite to_Zneg_cat to_Zneg_ones Z.mul_0_l Z.add_0_r.
    reflexivity.
  Qed.


  (* Lemmas about to_Z *)

  Lemma to_Z_nil : to_Z [::] = 0%Z.
  Proof. reflexivity. Qed.

  Lemma to_Z_rcons bs b :
    to_Z (rcons bs b) = if b then Z.opp (Z.succ (to_Zneg bs))
                        else to_Zpos bs.
  Proof.
    rewrite /to_Z. rewrite splitmsb_joinmsb. reflexivity.
  Qed.

  Lemma to_Z0 bs : (to_Z bs = 0)%Z -> bs = zeros (size bs).
  Proof.
    case: (lastP bs) => {bs} //=. move=> bs b.
    rewrite to_Z_rcons. rewrite size_rcons. case: b.
    - move/Z.eq_opp_l. rewrite Z.opp_0. rewrite -(Z.sub_0_r 0).
      rewrite -(Z.sub_0_r (to_Zneg bs)). rewrite -Z.sub_pred_r /=.
      move/Z.sub_move_0_r. move=> H. move: (@to_Zneg_ge0 bs). rewrite H. done.
    - move=> Hs. rewrite -zeros_rcons. rewrite -(to_Zpos0 Hs). reflexivity.
  Qed.

  Lemma to_Z_ge0_msb bs : (0 <= to_Z bs)%Z -> msb bs = b0.
  Proof.
    case: (lastP bs) => {bs} //=. move=> bs lb. rewrite msb_joinmsb.
    case: lb => //=. rewrite to_Z_rcons. move/Z.opp_nonneg_nonpos.
    move=> H. move/Z.le_succ_l: H => H.
    move: (Z.le_lt_trans _ _ _ (@to_Zneg_ge0 bs) H). done.
  Qed.

  Lemma to_Z1 bs : (to_Z bs = 1)%Z -> bs = b1::(copy (size bs - 1) b0).
  Proof.
    case: (lastP bs) => {bs} //=. move=> bs lb.
    rewrite size_rcons subn1 -pred_Sn. move=> H.
    have Hs: (0 <= to_Z (rcons bs lb))%Z by rewrite H.
    move: (to_Z_ge0_msb Hs). rewrite msb_joinmsb. move=> ?; subst.
    clear Hs.  rewrite to_Z_rcons /= in H. rewrite {1}(to_Zpos1 H) /=.
    rewrite zeros_rcons. have Hs: (0 < size bs) by case: bs H.
    rewrite subn1. rewrite (ltn_predK Hs). reflexivity.
  Qed.

  Lemma to_Z_zeros n : to_Z (zeros n) = 0%Z.
  Proof.
    case: n => [| n] //. rewrite -zeros_rcons. rewrite to_Z_rcons /=.
    exact: to_Zpos_zeros.
  Qed.

  Lemma to_Z_ones n : 0 < n -> to_Z (ones n) = (-1)%Z.
  Proof.
    case: n => [| n] //. move=> _. rewrite -ones_rcons. rewrite to_Z_rcons /=.
    rewrite to_Zneg_ones. reflexivity.
  Qed.

  Lemma to_Z_copy n b : 0 < n -> to_Z (copy n b) = (- b)%Z.
  Proof.
    case b; rewrite /= => Hn. 
    - have->: copy n true = ones n by reflexivity. exact: to_Z_ones. 
    - have->: copy n false = zeros n by reflexivity. exact: to_Z_zeros.
  Qed.

  Lemma to_Z_inj_ss bs1 bs2 :
    size bs1 = size bs2 -> to_Z bs1 = to_Z bs2 -> bs1 = bs2.
  Proof.
    case: (lastP bs1); case (lastP bs2) => {bs1 bs2} //=.
    - move=> ? ?; rewrite size_rcons. discriminate.
    - move=> ? ?; rewrite size_rcons. discriminate.
    - move=> bs2 lb2 bs1 lb1. rewrite !size_rcons => Hs.
      move: (eq_add_S _ _ Hs) => {Hs} Hs. rewrite !to_Z_rcons.
      case: lb1; case: lb2 => /=.
      + move=> Hz. move: (Z.opp_inj _ _ Hz) => {Hz} Hz.
        move: (Z.succ_inj _ _ Hz) => {Hz} Hz.
        by rewrite (to_Zneg_inj_ss Hs Hz).
      + move: (@to_Zpos_ge0 bs2) => {Hs} H. move=> Hz. rewrite -Hz in H.
        move/Z.opp_nonneg_nonpos: H => H. move/Z.le_succ_l: H => H.
        move: (Z.le_lt_trans _ _ _ (@to_Zneg_ge0 bs1) H). done.
      + move: (@to_Zpos_ge0 bs1) => {Hs} H. move=> Hz. rewrite Hz in H.
        move/Z.opp_nonneg_nonpos: H => H. move/Z.le_succ_l: H => H.
        move: (Z.le_lt_trans _ _ _ (@to_Zneg_ge0 bs2) H). done.
      + move=> Hz. rewrite (to_Zpos_inj_ss Hs Hz). reflexivity.
  Qed.

  Lemma to_Z_inj bs1 bs2 :
    to_Z bs1 = to_Z bs2 ->
    sext (size bs2 - size bs1) bs1 = sext (size bs1 - size bs2) bs2.
  Proof.
    case: (lastP bs1); case: (lastP bs2) => {bs1 bs2} //=.
    - move=> bs2 lb2. rewrite to_Z_nil. rewrite subn0 sub0n sext_nil sext0.
      move=> H. move: (Logic.eq_sym H) => {H} H. rewrite (to_Z0 H).
      rewrite size_zeros. reflexivity.
    - move=> bs1 lb1. rewrite to_Z_nil. rewrite subn0 sub0n sext_nil sext0.
      move=> H. rewrite (to_Z0 H). rewrite size_zeros. reflexivity.
    - move=> bs2 lb2 bs1 lb1. rewrite !size_rcons.
      rewrite -!(addn1 (size bs1)) -!(addn1 (size bs2)) !subnDr.
      rewrite /sext !msb_joinmsb.
      rewrite !to_Z_rcons. case: lb1; case: lb2 => /=.
      + move=> H. move: (Z.opp_inj _ _ H) => {H} H. move: (Z.succ_inj _ _ H) => {H} H.
        rewrite !cat_rcons. rewrite !copy_cons. rewrite -!copy_rcons.
        rewrite -!rcons_cat. rewrite (to_Zneg_inj H). reflexivity.
      + move=> H. move: (@to_Zpos_ge0 bs2). rewrite -H => {H} H.
        move/Z.opp_nonneg_nonpos: H => H. move/Z.le_succ_l: H => H1.
        move: (@to_Zneg_ge0 bs1) => H2. move: (Z.le_lt_trans _ _ _ H2 H1). done.
      + move=> H. move: (@to_Zpos_ge0 bs1). rewrite H => {H} H.
        move/Z.opp_nonneg_nonpos: H => H. move/Z.le_succ_l: H => H1.
        move: (@to_Zneg_ge0 bs2) => H2. move: (Z.le_lt_trans _ _ _ H2 H1). done.
      + move=> H. rewrite !cat_rcons. rewrite !copy_cons. rewrite -!copy_rcons.
        rewrite -!rcons_cat. move: (to_Zpos_inj H). rewrite /zext. move=> ->.
        reflexivity.
  Qed.

  Lemma to_Z_zext bs n : 0 < n -> to_Z (zext n bs) = to_Zpos bs.
  Proof.
    case: n => //=. move=> n _. rewrite zext_Sn cats1.
    rewrite to_Z_rcons /=. exact: to_Zpos_zext.
  Qed.

  Lemma to_Z_sext bs n : to_Z (sext n bs) = to_Z bs.
  Proof.
    case: n => [| n] /=.
    - rewrite sext0. reflexivity.
    - move: (lastP bs). case=> {bs} [| bs b] /=.
      + rewrite sext_nil. rewrite to_Z_zeros. reflexivity.
      + rewrite /sext msb_joinmsb. rewrite -copy_rcons -rcons_cat.
        rewrite !to_Z_rcons. case: b.
        * rewrite cat_rcons copy_cons. rewrite to_Zneg_cat.
          rewrite -/(ones n.+1) to_Zneg_ones /= Z.add_0_r. reflexivity.
        * rewrite cat_rcons copy_cons. rewrite to_Zpos_cat.
          rewrite -/(zeros n.+1) to_Zpos_zeros /= Z.add_0_r. reflexivity.
  Qed.

  Lemma high1_0_to_Z bs : high 1 bs = [:: b0] -> to_Z bs = to_Zpos bs.
  Proof.
    move: (lastP bs). case => {bs} //=. move=> bs b.
    rewrite high_rcons high0 /=. case=> ->. rewrite to_Z_rcons /=.
    rewrite to_Zpos_rcons. rewrite Z.mul_0_l Z.add_0_r. reflexivity.
  Qed.

  Lemma high1_1_to_Z bs : high 1 bs = [:: b1] -> to_Z bs = Z.opp (Z.succ (to_Zneg bs)).
  Proof.
    move: (lastP bs). case => {bs} //=. move=> bs b.
    rewrite high_rcons high0 /=. case=> ->. rewrite to_Z_rcons /=.
    rewrite to_Zneg_rcons. rewrite Z.mul_0_l Z.add_0_r. reflexivity.
  Qed.

  Lemma highn_0_to_Z bs n :
    0 < n -> high n bs = zeros n -> to_Z bs = to_Zpos bs.
  Proof.
    move=> Hn Hbs. apply: high1_0_to_Z. rewrite (highn_high1 Hn Hbs).
    rewrite msb_zeros. reflexivity.
  Qed.

  Lemma to_Z_cat bs1 bs2 :
    0 < size bs2 ->
    to_Z (bs1 ++ bs2) = (to_Zpos bs1 + to_Z bs2 * 2 ^ Z.of_nat (size bs1))%Z.
  Proof.
    move: (lastP bs2). case=> {bs2} [| bs b] Hs //=.
    rewrite -rcons_cat => {Hs}. rewrite !to_Z_rcons. case: b.
    - rewrite to_Zneg_cat. rewrite Z.mul_opp_l. rewrite Z.mul_succ_l.
      rewrite (Z.add_comm (to_Zneg bs * 2 ^ Z.of_nat (size bs1))).
      rewrite Z.opp_add_distr Z.add_assoc.
      rewrite -Z.add_succ_l Z.opp_add_distr. apply/Z.add_cancel_r.
      move/Z.add_move_r: (to_Zpos_add_to_Zneg bs1). move=> ->. ring.
    - exact: to_Zpos_cat.
  Qed.

  Lemma to_Z_low_high bs n m :
    0 < m -> n + m = size bs -> 
    to_Z bs = (to_Zpos (low n bs) + to_Z (high m bs) * 2 ^ Z.of_nat n)%Z.
  Proof.
    move=> Hm Hsz. rewrite -(size_high m bs) in Hm. 
    by rewrite -{1}(cat_low_high Hsz) (to_Z_cat _ Hm) size_low. 
  Qed.

  Lemma high_zeros_to_Z_low bs n :
    high (size bs - n + 1) bs = zeros (size bs - n + 1) ->
    to_Z (low n bs) = to_Zpos bs.
  Proof.
    case Hn: (size bs <= n).
    - rewrite leq_eqVlt in Hn. case/orP: Hn => Hn.
      + rewrite -(eqP Hn) subnn add0n. rewrite low_size. exact: high1_0_to_Z.
      + move=> H. rewrite (low_oversize (ltnW Hn)).
        rewrite to_Z_cat; last by (rewrite size_zeros subn_gt0; exact: Hn).
        rewrite to_Z_zeros /= Z.add_0_r. reflexivity.
    - move/idP/negP: Hn. rewrite -ltnNge => Hn. move=> Hz. case Hn0: (n == 0).
      + rewrite (eqP Hn0) in Hn Hz *. rewrite low0 /to_Z /=.
        rewrite subn0 (high_oversize (leq_addr 1 (size bs))) in Hz.
        rewrite -(addnBAC _ (leqnn _)) subnn /= in Hz.
        rewrite addn1 -zeros_cons in Hz. case: Hz => ->. rewrite to_Zpos_zeros.
        reflexivity.
      + move/idP/negP: Hn0. rewrite -lt0n => H0n.
        have H1: (high 1 (low n bs) = zeros 1).
        { rewrite (high_low H0n (ltnW Hn)). rewrite Hz low_zeros. reflexivity. }
        rewrite (high1_0_to_Z H1).
        move: (subnKC (ltnW Hn)) => {H1} H1. rewrite -{2}(cat_low_high H1) => {H1}.
        rewrite to_Zpos_cat.
        have ->: high (size bs - n) bs = zeros (size bs - n).
        { apply: (high_zeros_le _ Hz). exact: leq_addr. }
        rewrite to_Zpos_zeros /= Z.add_0_r. reflexivity.
  Qed.

  Lemma to_Z_to_Zpos bs : 
    to_Z bs = (to_Zpos bs - (msb bs) *  2 ^ Z.of_nat (size bs))%Z.
  Proof.
    move: (high1_msb bs). case (msb bs) => Hmsb.
    - rewrite (high1_1_to_Z Hmsb). rewrite Z.mul_1_l Z.opp_succ -Z.sub_1_r.
      move/Z.add_move_r: (to_Zpos_add_to_Zneg bs) => ->. 
      rewrite -(Z.sub_add_distr _ 1) -(Z.add_opp_r _ (1 + _)). 
      rewrite Z.add_simpl_l Z.add_comm Z.opp_add_distr. reflexivity.
    - rewrite (high1_0_to_Z Hmsb). rewrite /= Z.sub_0_r. reflexivity.
  Qed.

  Lemma to_Z_mod_pow2_oversize bs n :
    size bs <= n ->
    ((to_Z bs) mod 2 ^ Z.of_nat n)%Z = to_Zpos (sext (n - size bs) bs).
  Proof.
    move=> Hsz. apply Logic.eq_sym. rewrite /sext to_Zpos_cat.
    move: (to_Z_to_Zpos bs). case (msb bs).
    - have->: copy (n - size bs) true = ones (n - size bs) by reflexivity.
      rewrite to_Zpos_ones Z.mul_sub_distr_r Z.mul_1_l. 
      rewrite -Z.pow_add_r; try exact: Nat2Z.is_nonneg.
      rewrite -Nat2Z.inj_add. 
      have->: (n - size bs + size bs)%coq_nat = n - size bs + size bs by reflexivity.
      rewrite (subnK Hsz) -{1}(Z.add_simpl_l ((2 ^ Z.of_nat n) * -1) (to_Zpos bs)).
      rewrite -{2}Z.opp_eq_mul_m1 Z.sub_opp_r -Z.add_sub_assoc -Z.add_assoc.
      apply Z.mod_unique_pos. split.
      + apply Z.add_nonneg_nonneg; first exact: to_Zpos_ge0.
        apply Zle_minus_le_0. apply Z.pow_le_mono_r; first by trivial.
        apply inj_le; by apply /leP.
      + apply (Z.le_lt_sub_lt (2 ^ Z.of_nat n) (2 ^ Z.of_nat n)); 
          first exact: Z.le_refl.
        rewrite Z.add_assoc Z.add_comm -Z.add_sub_assoc Z.add_simpl_r Z.sub_diag. 
        apply (Z.le_lt_add_lt (2 ^ Z.of_nat (size bs)) (2 ^ Z.of_nat (size bs))); 
          first exact: Z.le_refl.
        rewrite Z.add_comm Z.add_assoc Z.add_opp_r Z.sub_diag /=.
        exact: to_Zpos_bounded.
    - have->: copy (n - size bs) false = zeros (n - size bs) by reflexivity.
      rewrite to_Zpos_zeros /= Z.sub_0_r Z.add_0_r.
      move=> ->. rewrite Z.mod_small; first reflexivity.
      split; first exact: to_Zpos_ge0. 
      apply (Z.lt_le_trans _ _ _ (to_Zpos_bounded bs)).
      apply Z.pow_le_mono_r; try by trivial. apply inj_le; by apply /leP.
  Qed.

  Lemma to_Z_mod_pow2 bs n :
    n <= size bs  ->
    ((to_Z bs) mod 2 ^ Z.of_nat n)%Z = to_Zpos (low n bs).
  Proof.
    rewrite leq_eqVlt => /orP [/eqP-> | Hsz]. 
    - rewrite to_Z_mod_pow2_oversize; last exact: leqnn.
      by rewrite subnn sext0 low_size.
    - rewrite (@to_Z_low_high bs n (size bs - n)); 
        [ | by rewrite subn_gt0 | exact: (subnKC (ltnW Hsz))].
      rewrite Z_mod_plus_full Z.mod_small; first reflexivity.
      split; first exact: to_Zpos_ge0.
      apply (Z.lt_stepr _ _ _ (to_Zpos_bounded (low n bs))). by rewrite size_low.
  Qed.


(*---------------------------------------------------------------------------
    Lemmas of take
  ---------------------------------------------------------------------------*)


Lemma to_nat_take : forall n p, to_nat ((take n) p) = if n < size p then to_nat (from_nat n (to_nat p)) else to_nat p.
  elim => [| ns IH] p.
  rewrite take0/=.
  elim p => [| phd ptl IHm]; done.
  elim p => [| phd ptl IHm]; first done.
  rewrite to_nat_cons/=.
  case Hlt : (ns.+1 < (size ptl).+1); rewrite ltnS in Hlt.
  rewrite odd_add odd_double oddb. rewrite (IH ptl) Hlt.
  case phd; first by rewrite/=uphalf_double.
  by (rewrite/=3!add0n-3!muln2-div.divn2 div.mulnK; last done).
  by rewrite IH Hlt.
Qed.

(*---------------------------------------------------------------------------
    Lemmas of most/last significant bit
  ---------------------------------------------------------------------------*)

Lemma dropmsb_zeros : forall n, dropmsb (zeros n) = zeros n.-1.
Proof.
  move => n. case n. done.
  move => n0. have->:(zeros n0.+1.-1=zeros n0) by rewrite-addn1-subn1 addnK.
  by rewrite-zeros_rcons/dropmsb/=belastd_rcons.
Qed.


End Lemmas.
