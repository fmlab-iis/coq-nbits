From Coq Require Import ZArith Arith List Decidable.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq div.
Require Import FunInd Recdef.
From nbits Require Import NBitsDef NBitsOp AuxLemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module SMTLIB .

(* Functions *)

Definition concat (bs1 : bits) (bs2 : bits) : bits := bs2 ++ bs1.

Definition extract (i j : nat) (bs : bits) : bits := NBitsDef.extract i j bs.

Definition bvnot (bs : bits) : bits := invB bs.

Definition bvand (bs1 : bits) (bs2 : bits) : bits := andB bs1 bs2.

Definition bvor (bs1 : bits) (bs2 : bits) : bits := orB bs1 bs2.

Definition bvneg (bs : bits) : bits := negB bs.

Definition bvadd (bs1 : bits) (bs2 : bits) : bits := addB bs1 bs2.

Definition bvmul (bs1 : bits) (bs2 : bits) : bits := mulB bs1 bs2.

Definition bvudiv (bs1 : bits) (bs2 : bits) : bits := udivB' bs1 bs2.

Definition bvurem (bs1 : bits) (bs2 : bits) : bits := uremB bs1 bs2.

Definition bvshl (bs1 : bits) (bs2 : bits) : bits := shlB (to_nat bs2) bs1.

Definition bvlshr (bs1 : bits) (bs2 : bits) : bits := shrB (to_nat bs2) bs1.

Definition bvult (bs1 : bits) (bs2 : bits) : bool := ltB bs1 bs2.


(* Extensions *)

Definition bvnand (bs1 : bits) (bs2 : bits) : bits := bvnot (bvand bs1 bs2).

Definition bvnor (bs1 : bits) (bs2 : bits) : bits := bvnot (bvor bs1 bs2).

Definition bvxor (bs1 : bits) (bs2 : bits) : bits :=
  bvor (bvand bs1 (bvnot bs2)) (bvand (bvnot bs1) bs2).

Definition bvxnor (bs1 : bits) (bs2 : bits) : bits :=
  bvor (bvand bs1 bs2) (bvand (bvnot bs1) (bvnot bs2)).

Function bvcomp (bs1 : bits) (bs2 : bits) {measure size bs1} : bits :=
  let m := size bs1 in
  if m <= 1 then bvxnor bs1 bs2 
  else bvand (bvxnor (extract (m - 1) (m - 1) bs1) (extract (m - 1) (m - 1) bs2))
             (bvcomp (extract (m - 2) 0 bs1) (extract (m - 2) 0 bs2)).
Proof.
  move=> bs1 _. rewrite /extract size_extract subn0. 
  case (size bs1) => [// | n]; case: n => [// | n] _. 
  rewrite -addn2 -addnBA; last done. rewrite subnn addn0. by apply plus_lt_compat_l.
Defined.

Definition bvsub (bs1 : bits) (bs2 : bits) : bits := bvadd bs1 (bvneg bs2).

Definition bvsdiv (bs1: bits) (bs2 : bits) : bits :=
  let m := size bs1 in
  let msb1 := extract (m - 1) (m - 1) bs1 in
  let msb2 := extract (m - 1) (m - 1) bs2 in
  if andb (msb1 == [:: false]) (msb2 == [:: false]) then bvudiv bs1 bs2
  else if andb (msb1 == [:: true]) (msb2 == [:: false]) 
       then bvneg (bvudiv (bvneg bs1) bs2)
       else if andb (msb1 == [:: false]) (msb2 == [:: true]) 
            then bvneg (bvudiv bs1 (bvneg bs2))
            else bvudiv (bvneg bs1) (bvneg bs2).

Definition bvsrem (bs1 : bits) (bs2 : bits) : bits :=
  let m := size bs1 in
  let msb1 := extract (m - 1) (m - 1) bs1 in
  let msb2 := extract (m - 1) (m - 1) bs2 in
  if andb (msb1 == [:: false]) (msb2 == [:: false]) then bvurem bs1 bs2
  else if andb (msb1 == [:: true]) (msb2 == [:: false]) 
       then bvneg (bvurem (bvneg bs1) bs2)
       else if andb (msb1 == [:: false]) (msb2 == [:: true]) 
            then bvurem bs1 (bvneg bs2)
            else bvneg (bvurem (bvneg bs1) (bvneg bs2)).

Definition bvsmod (bs1 : bits) (bs2 : bits) : bits :=
  let m := size bs1 in
  let msb1 := extract (m - 1) (m - 1) bs1 in
  let msb2 := extract (m - 1) (m - 1) bs2 in
  let abs1 := if msb1 == [:: false] then bs1 else bvneg bs1 in
  let abs2 := if msb2 == [:: false] then bs2 else bvneg bs2 in
  let u := bvurem abs1 abs2 in
  if u == zeros m then u
  else if andb (msb1 == [:: false]) (msb2 == [:: false]) then u
       else if andb (msb1 == [:: true]) (msb2 == [:: false]) then bvadd (bvneg u) bs2
            else if andb (msb1 == [:: false]) (msb2 == [:: true]) then bvadd u bs2
                 else bvneg u.
                                                                   
Definition bvule (bs1 : bits) (bs2 : bits) : bool := 
  orb (bvult bs1 bs2) (bs1 == bs2).

Definition bvugt (bs1 : bits) (bs2 : bits) : bool := bvult bs2 bs1.

Definition bvuge (bs1 : bits) (bs2 : bits) : bool := 
  orb (bvult bs2 bs1) (bs1 == bs2).

Definition bvslt (bs1 : bits) (bs2 : bits) : bool :=
  let m := size bs1 in
  orb (andb (extract (m - 1) (m - 1) bs1 == [:: true])
            (extract (m - 1) (m - 1) bs2 == [:: false]))
      (andb (extract (m - 1) (m - 1) bs1 == extract (m - 1) (m - 1) bs2)
            (bvult bs1 bs2)).

Definition bvsle (bs1 : bits) (bs2 : bits) : bool :=
  let m := size bs1 in
  orb (andb (extract (m - 1) (m - 1) bs1 == [:: true])
            (extract (m - 1) (m - 1) bs2 == [:: false]))
      (andb (extract (m - 1) (m - 1) bs1 == extract (m - 1) (m - 1) bs2)
            (bvule bs1 bs2)).

Definition bvsgt (bs1 : bits) (bs2 : bits) : bool := bvslt bs2 bs1.

Definition bvsge (bs1 : bits) (bs2 : bits) : bool := bvsle bs2 bs1.

Definition bvashr (bs1 : bits) (bs2 : bits) : bits :=
  let m := size bs1 in
  if extract (m - 1) (m - 1) bs1 == [:: false] then bvlshr bs1 bs2
  else bvnot (bvlshr (bvnot bs1) bs2).

Fixpoint repeat (j : nat) (bs : bits) : bits :=
  match j with 
  | O => [::]
  | S j' => concat bs (repeat j' bs)
  end.

Definition zero_extend (i : nat) (bs : bits) : bits :=
  match i with
  | O => bs
  | _ => concat (repeat i [:: false]) bs
  end.

Definition sign_extend (i : nat) (bs : bits) : bits :=
  match i with
  | O => bs
  | _ => let m := size bs in
         concat (repeat i (extract (m - 1) (m - 1) bs)) bs
  end.

Fixpoint rotate_left (i : nat) (bs : bits) : bits :=
  match i with 
  | O => bs
  | S i' => let m := size bs in
            if m <= 1 then bs
            else rotate_left i' (concat (extract (m - 2) 0 bs) 
                                        (extract (m - 1) (m - 1) bs))
  end.

Fixpoint rotate_right (i : nat) (bs : bits) : bits :=
  match i with
  | O => bs
  | S i' => let m := size bs in
            if m <= 1 then bs
            else rotate_right i' (concat (extract 0 0 bs)
                                         (extract (m - 1) 1 bs))
  end.

End SMTLIB.


(* Equivalence Lemmas *)

Lemma smtlib_concat_cat bs1 bs2 : SMTLIB.concat bs1 bs2 = cat bs2 bs1.
Proof. by rewrite /SMTLIB.concat. Qed.

Lemma smtlib_extract_extract i j bs : SMTLIB.extract i j bs = extract i j bs.
Proof. by rewrite /SMTLIB.extract. Qed.

Lemma smtlib_bvnot_invB bs : SMTLIB.bvnot bs = invB bs.
Proof. by rewrite /SMTLIB.bvnot. Qed.

Lemma smtlib_bvand_andB bs1 bs2 : SMTLIB.bvand bs1 bs2 = andB bs1 bs2.
Proof. by rewrite /SMTLIB.bvand. Qed.

Lemma smtlib_bvor_orB bs1 bs2 : SMTLIB.bvor bs1 bs2 = orB bs1 bs2.
Proof. by rewrite /SMTLIB.bvor. Qed.

Lemma smtlib_bvneg_negB bs : SMTLIB.bvneg bs = negB bs.
Proof. by rewrite /SMTLIB.bvneg. Qed.

Lemma smtlib_bvadd_addB bs1 bs2 : SMTLIB.bvadd bs1 bs2 = addB bs1 bs2.
Proof. by rewrite /SMTLIB.bvadd. Qed.

Lemma smtlib_bvmul_mulB bs1 bs2 : SMTLIB.bvmul bs1 bs2 = mulB bs1 bs2.
Proof. by rewrite /SMTLIB.bvmul. Qed.

Lemma smtlib_bvudiv_udivB' bs1 bs2 : SMTLIB.bvudiv bs1 bs2 = udivB' bs1 bs2.
Proof. by rewrite /SMTLIB.bvudiv. Qed.

Lemma smtlib_bvurem_uremB bs1 bs2 : SMTLIB.bvurem bs1 bs2 = uremB bs1 bs2.
Proof. by rewrite /SMTLIB.bvurem. Qed.

Lemma smtlib_bvshl_shlB bs1 bs2 : SMTLIB.bvshl bs1 bs2 = shlB (to_nat bs2) bs1.
Proof. by rewrite /SMTLIB.bvshl. Qed.

Lemma smtlib_bvlshr_shrB bs1 bs2 : SMTLIB.bvlshr bs1 bs2 = shrB (to_nat bs2) bs1.
Proof. by rewrite /SMTLIB.bvlshr. Qed.

Lemma smtlib_bvult_ltB bs1 bs2 : SMTLIB.bvult bs1 bs2 = ltB bs1 bs2.
Proof. by rewrite /SMTLIB.bvult. Qed.

Lemma smtlib_bvxor_xorB bs1 bs2 : SMTLIB.bvxor bs1 bs2 = xorB bs1 bs2.
Proof. 
Admitted.

Lemma smtlib_bvcomp_eqop bs1 bs2 : SMTLIB.bvcomp bs1 bs2 = [:: eq_op bs1 bs2].
Proof.
Admitted.

Lemma smtlib_bvsub_subB bs1 bs2 : 
  size bs1 = size bs2 -> SMTLIB.bvsub bs1 bs2 = subB bs1 bs2.
Proof.
  rewrite /SMTLIB.bvsub /SMTLIB.bvadd /SMTLIB.bvneg => /eqP Hsz.
  by rewrite (eqP (subB_equiv_addB_negB Hsz)).
Qed.

Lemma smtlib_bvsdiv_sdivB bs1 bs2 :
  size bs1 = size bs2 -> SMTLIB.bvsdiv bs1 bs2 = sdivB bs1 bs2.
Proof.
  rewrite /SMTLIB.bvsdiv /SMTLIB.extract /extract subnn !high1_msb.
  case : (bs2) => [|bshd2 bstl2].
  - move => /size0nil -> //.
  - move => Hsz. have Hsz' : 0 < size bs1 by rewrite Hsz.
    rewrite subnK// low_size Hsz low_size /sdivB /absB.
    case (msb bs1); case (msb (bshd2::bstl2)); try done.
Qed.  

Lemma smtlib_bvsrem_sremB bs1 bs2 :
  size bs1 = size bs2 -> SMTLIB.bvsrem bs1 bs2 = sremB bs1 bs2.
Proof.
  rewrite /SMTLIB.bvsrem /SMTLIB.extract /extract subnn !high1_msb.
  case : bs2 => [|bshd2 bstl2].
  - move => /size0nil -> //.
    move => Hsz. have Hsz' : 0 < size bs1 by rewrite Hsz.
    rewrite subnK// low_size Hsz low_size /sremB /absB.
    case (msb bs1); case (msb (bshd2::bstl2)); try done.
Qed.  

Lemma smtlib_bvsmod_smodB bs1 bs2 : 
  size bs1 = size bs2 -> SMTLIB.bvsmod bs1 bs2 = smodB bs1 bs2.
Proof.
  rewrite /SMTLIB.bvsmod /SMTLIB.extract /extract subnn !high1_msb.
  case : bs2 => [|bshd2 bstl2].
  - move => /size0nil -> //.
  - move => Hsz. have Hsz' : 0 < size bs1 by rewrite Hsz.
    rewrite subnK// low_size Hsz low_size /smodB /sremB /absB -/(uremB _ _) !smtlib_bvurem_uremB !smtlib_bvneg_negB.
    case (msb bs1); case (msb (bshd2::bstl2)); rewrite/=.
    + case H0 : (uremB (-# bs1)%bits (-# (bshd2 :: bstl2))%bits == b0 :: zeros (size bstl2)); last done.
      rewrite (eqP H0) zeros_cons (eqP (negB_zeros _))//.
    + case H0 : (uremB (-# bs1)%bits (bshd2 :: bstl2) == b0 :: zeros (size bstl2)).
      * rewrite (eqP H0) zeros_cons (eqP (negB_zeros _)) size_zeros eq_refl//.
      * rewrite smtlib_bvadd_addB.
        case Hn0: ((-# uremB (-# bs1) (bshd2 :: bstl2))%bits == zeros (size (-# uremB (-# bs1) (bshd2 :: bstl2))%bits)); last done.
        rewrite <-(negB_zeros' (uremB (-# bs1) (bshd2 :: bstl2))%bits) in Hn0;
          rewrite (eqP Hn0) size_uremB size_negB zeros_cons Hsz eq_refl// in H0.
    + rewrite smtlib_bvadd_addB size_uremB zeros_cons Hsz//.
    + by case H0 : (uremB bs1 (bshd2 :: bstl2) == b0 :: zeros (size bstl2)).
Qed.
                                                                   
Lemma smtlib_bvule_leB bs1 bs2 : SMTLIB.bvule bs1 bs2 = leB bs1 bs2.
Proof. 
Admitted.

Lemma smtlib_bvugt_gtB bs1 bs2 : SMTLIB.bvugt bs1 bs2 = gtB bs1 bs2.
Proof. 
Admitted.

Lemma smtlib_bvuge_geB bs1 bs2 : SMTLIB.bvuge bs1 bs2 = geB bs1 bs2.
Proof.
Admitted.

Lemma smtlib_bvslt_sltB bs1 bs2 : SMTLIB.bvslt bs1 bs2 = sltB bs1 bs2.
Proof.
Admitted.

Lemma smtlib_bvsle_sleB bs1 bs2 : SMTLIB.bvsle bs1 bs2 = sleB bs1 bs2.
Proof.
Admitted.

Lemma smtlib_bvsgt_sgtB bs1 bs2 : SMTLIB.bvsgt bs1 bs2 = sgtB bs1 bs2.
Proof.
Admitted.

Lemma smtlib_bvsge_sgeB bs1 bs2 : SMTLIB.bvsge bs1 bs2 = sgeB bs1 bs2.
Proof.
Admitted.

Lemma smtlib_bvashr_sarB bs1 bs2 : SMTLIB.bvashr bs1 bs2 = sarB (to_nat bs2) bs1.
Proof.
Admitted.

Lemma smtlib_repeat_repeat j bs : SMTLIB.repeat j bs = repeat j bs.
Proof.
Admitted.

Lemma smtlib_zero_extend_zext i bs : SMTLIB.zero_extend i bs = zext i bs.
Proof.
Admitted.

Lemma smtlib_sign_extend_sext i bs : SMTLIB.sign_extend i bs = sext i bs.
Proof.
Admitted.

Lemma smtlib_rotate_left_rolB i bs : SMTLIB.rotate_left i bs = rolB i bs.
Proof.
Admitted.

Lemma smtlib_rotate_right_rorB i bs : SMTLIB.rotate_right i bs = rorB i bs.
Proof.
Admitted.
