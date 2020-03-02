
From Coq Require Import ZArith Arith List Decidable.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq div.
From nbits Require Import NBitsDef AuxLemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section ExtZip.

  Variable S : Type.
  Variable T : Type.
  Variable sd : S.
  Variable td : T.

  Fixpoint extzip (ss : seq S) (ts : seq T) : seq (S * T) :=
    match ss, ts with
    | _, [::] => zip ss (nseq (size ss) td)
    | [::], _ => zip (nseq (size ts) sd) ts
    | s::ss, t::ts => (s, t)::(extzip ss ts)
    end.

  Lemma size_extzip ss ts : size (extzip ss ts) = maxn (size ss) (size ts).
  Proof.
    elim: ss ts.
    - elim=> /=.
      + reflexivity.
      + move=> t ts IH. rewrite size_zip size_nseq minnn max0n. reflexivity.
    - move=> s ss IHs. case=> /=.
      + rewrite size_zip size_nseq minnn maxn0. reflexivity.
      + move=> t ts. rewrite IHs maxnSS. reflexivity.
  Qed.

  Definition extzip0d (ss : seq S) : seq (S * T) := extzip ss [::].

  Definition extzipd0 (ts : seq T) : seq (S * T) := extzip [::] ts.

  Lemma extzip_zip (ss : seq S) (ts : seq T) :
    extzip ss ts = zip (ss ++ nseq (size ts - size ss) sd)
                       (ts ++ nseq (size ss - size ts) td).
  Proof.
    elim: ss ts => [| s ss IHs] [|t ts] //=.
    - rewrite cats0. reflexivity.
    - rewrite cats0. reflexivity.
    - rewrite -(addn1 (size ss)) -(addn1 (size ts)) 2!subnDr. rewrite -(IHs _).
      reflexivity.
  Qed.

  Lemma extzip_zip_ss (ss : seq S) (ts : seq T) :
    size ss = size ts -> extzip ss ts = zip ss ts.
  Proof. move=> Hs. rewrite extzip_zip. rewrite Hs subnn 2!cats0. reflexivity. Qed.

  Lemma nth_extzip ss ts i : nth (sd, td) (extzip ss ts) i = (nth sd ss i, nth td ts i).
  Proof.
    elim: i ss ts => [| i IH] [| s ss] [| t ts] //=.
    - rewrite nth_zip; last by rewrite size_nseq. rewrite nth_nseq. by case: ifP.
    - rewrite nth_zip; last by rewrite size_nseq. rewrite nth_nseq. by case: ifP.
  Qed.

  Lemma unzip1_extzip_ll ss ts : size ts <= size ss -> unzip1 (extzip ss ts) = ss.
  Proof.
    elim: ss ts => [| s ss IHs] [| t ts] //=.
    - move=> _. rewrite unzip1_zip; first reflexivity. rewrite size_nseq. exact: leqnn.
    - rewrite ltnS => Hs. rewrite (IHs _ Hs). reflexivity.
  Qed.

  Lemma unzip1_extzip_rl ss ts :
    size ss < size ts -> unzip1 (extzip ss ts) = ss ++ nseq (size ts - size ss) sd.
  Proof.
    elim: ss ts => [| s ss IHs] [| t ts] //=.
    - move=> _. rewrite unzip1_zip; last by rewrite size_nseq; exact: leqnn.
      reflexivity.
    - rewrite -(addn1 (size ss)) -(addn1 (size ts)) ltn_add2r => Hs.
      rewrite (IHs _ Hs). rewrite subnDr. reflexivity.
  Qed.

  Lemma unzip1_extzip_ss ss ts : size ss = size ts -> unzip1 (extzip ss ts) = ss.
  Proof. move=> Hs. apply: unzip1_extzip_ll. by rewrite Hs. Qed.

  Lemma unzip1_extzip ss ts :
    unzip1 (extzip ss ts) = ss ++ nseq (size ts - size ss) sd.
  Proof.
    case/orP: (ltn_geq_total (size ss) (size ts)) => Hs.
    - exact: (unzip1_extzip_rl Hs).
    - rewrite (eqP Hs) cats0. exact: (unzip1_extzip_ll Hs).
  Qed.

  Lemma unzip2_extzip_ll ss ts :
    size ts < size ss -> unzip2 (extzip ss ts) = ts ++ nseq (size ss - size ts) td.
  Proof.
    elim: ss ts => [| s ss IHs] [| t ts] //=.
    - move=> _. rewrite unzip2_zip; last by rewrite size_nseq; exact: leqnn.
      reflexivity.
    - rewrite -(addn1 (size ss)) -(addn1 (size ts)) ltn_add2r => Hs.
      rewrite (IHs _ Hs). rewrite subnDr. reflexivity.
  Qed.

  Lemma unzip2_extzip_rl ss ts : size ss <= size ts -> unzip2 (extzip ss ts) = ts.
  Proof.
    elim: ss ts => [| s ss IHs] [| t ts] //=.
    - move=> _. rewrite unzip2_zip; first reflexivity. rewrite size_nseq. exact: leqnn.
    - rewrite ltnS => Hs. rewrite (IHs _ Hs). reflexivity.
  Qed.

  Lemma unzip2_extzip_ss ss ts : size ss = size ts -> unzip2 (extzip ss ts) = ts.
  Proof. move=> Hs. apply: unzip2_extzip_rl. by rewrite Hs. Qed.

  Lemma unzip2_extzip ss ts :
    unzip2 (extzip ss ts) = ts ++ nseq (size ss - size ts) td.
  Proof.
    case/orP: (ltn_geq_total (size ts) (size ss)) => Hs.
    - exact: (unzip2_extzip_ll Hs).
    - rewrite (eqP Hs) cats0. exact: (unzip2_extzip_rl Hs).
  Qed.

End ExtZip.



Section Lift.

  Variable T : Type.
  Variable d : T.
  Variable op : T -> T -> T.

  Definition lift (ss : seq T) (ts : seq T) : seq T :=
    map (fun e => op e.1 e.2) (extzip d d ss ts).

  Lemma lift_cons s ss t ts : lift (s::ss) (t::ts) = (op s t)::(lift ss ts).
  Proof. reflexivity. Qed.

  Lemma lift_nil : lift [::] [::] = [::].
  Proof. reflexivity. Qed.

  Lemma lift_nil_cons t ts : lift [::] (t::ts) = (op d t)::(lift [::] ts).
  Proof. by case: ts. Qed.

  Lemma lift_cons_nil s ss : lift (s::ss) [::] = (op s d)::(lift ss [::]).
  Proof. by case: ss. Qed.

  Definition liftE := (lift_nil_cons, lift_cons_nil, lift_cons, lift_nil).

  Lemma lift0n (h : left_id d op) : left_id [::] lift.
  Proof. by elim=> [| s ss IHs]; rewrite // lift_nil_cons IHs h. Qed.

  Lemma liftn0 (h : right_id d op) : right_id [::] lift.
  Proof. by elim=> [| s ss IHs]; rewrite // lift_cons_nil IHs h. Qed.

  Lemma size_lift ss ts : size (lift ss ts) = maxn (size ss) (size ts).
  Proof.
    elim: ss ts => [| s ss IHs] [| t ts] //=.
    - rewrite max0n size_map size_zip size_nseq minnn. reflexivity.
    - rewrite maxn0 size_map size_zip size_nseq minnn. reflexivity.
    - rewrite IHs maxnSS. reflexivity.
  Qed.

End Lift.



Section Ops.

  Local Open Scope bits_scope.

  Definition lift0 := lift b0.

  Definition extzip0 := extzip b0 b0.

  Fixpoint succB (bs : bits) : bits :=
    match bs with
    | [::] => [::]
    | hd::tl => if hd then b0::(succB tl)
                else b1::tl
    end.

  Fixpoint predB (bs : bits) : bits :=
    match bs with
    | [::] => [::]
    | hd::tl => if hd then b0::tl
                else b1::(predB tl)
    end.

  Definition invB (bs : bits) : bits := map (fun b => ~~ b) bs.

  Definition andB (bs1 bs2 : bits) : bits := lift0 andb bs1 bs2.

  Definition orB (bs1 bs2 : bits) : bits := lift0 orb bs1 bs2.

  Definition xorB (bs1 bs2 : bits) : bits := lift0 xorb bs1 bs2.

  Definition negB (bs : bits) : bits := succB (invB bs).

  Fixpoint orb_all (bs: bits): bool :=
    match bs with
    | [::] => false
    | hd::tl =>
      let result_tl := orb_all tl in
      orb result_tl hd
    end.

  Fixpoint andb_orb_all_zip (bsp: seq(bool * bool)) : bool :=
    match bsp with
    | [::] => false
    | (ls1_low, ls2_high)::bsp_tl =>
      let result_tl := andb_orb_all_zip bsp_tl in
      let result_or := orb_all (unzip1 bsp) in
      orb result_tl (andb result_or ls2_high)
    end.

  Definition andb_orb_all (bs1 bs2 : bits) : bool := andb_orb_all_zip (extzip0 bs1 (rev bs2)).

  Definition bool_adder (c b1 b2 : bool) : bool * bool :=
    match c, b1, b2 with
    | false, false, false => (false, false)
    | true, false, false | false, true, false | false, false, true => (false, true)
    | true, true, false | false, true, true | true, false, true => (true, false)
    | true, true, true => (true, true)
    end.

  Fixpoint full_adder_zip (c : bool) (zip : seq (bool * bool)) : bool * bits :=
    match zip with
    | [::] => (c, [::])
    | (hd1, hd2)::tl => let (c, hd) := bool_adder c hd1 hd2 in
                        let (c, tl) := full_adder_zip c tl in
                        (c, hd::tl)
    end.

  Definition full_adder (c : bool) (bs1 bs2 : bits) := full_adder_zip c (zip bs1 bs2).

  Definition adcB (c : bool) (bs1 bs2 : bits) : bool * bits := full_adder c bs1 bs2.

  Definition addB (bs1 bs2 : bits) : bits := (adcB false bs1 bs2).2.

  Definition carry_addB (bs1 bs2 : bits) : bool := (adcB false bs1 bs2).1.

  Definition addB_ovf (bs1 bs2 : bits) : bool := carry_addB bs1 bs2.

  Definition sbbB b (bs1 bs2 : bits) : bool * bits :=
    let (c, res) := (adcB (~~b) bs1 (invB bs2)) in
    (~~ c, res).

  Definition subB (bs1 bs2 : bits) : bits := (sbbB false bs1 bs2).2.

  Definition borrow_subB (bs1 bs2 : bits) : bool := (sbbB false bs1 bs2).1.

  Definition Saddo (bs1 bs2: bits) :=
    let (tbs1, sign1) := eta_expand (splitmsb bs1) in
    let (tbs2, sign2) := eta_expand (splitmsb bs2) in
    let b_add := addB bs1 bs2 in
    let (u_fa, sign_fa) := eta_expand (splitmsb b_add) in
    (sign1 && sign2 && ~~sign_fa) || (~~sign1 && ~~sign2 && sign_fa).

  Definition Ssubo (bs1 bs2: bits) :=
    let (tbs1, sign1) := eta_expand (splitmsb bs1) in
    let (tbs2, sign2) := eta_expand (splitmsb bs2) in
    let b_sub := subB bs1 bs2 in
    let (t_sub, sign_sub) := eta_expand (splitmsb b_sub) in
    (~~sign1 && sign2 && sign_sub) || (sign1 && ~~sign2 && ~~sign_sub).

  Fixpoint full_mul (bs1 bs2 : bits) : bits :=
    match bs1 with
    | [::] => from_nat (size bs1 + size bs2) 0
    | hd::tl =>
      if hd then addB (joinlsb false (full_mul tl bs2)) (zext (size bs1) bs2)
      else joinlsb false (full_mul tl bs2)
    end.

  Definition mulB (bs1 bs2 : bits) : bits := low (size bs1) (full_mul bs1 bs2).

  Definition Umulo bs1 bs2 : bool :=
    let (bs1_low, bs1_hightl) := eta_expand (splitlsb bs1) in
    let (bs2_low, bs2_hightl) := eta_expand (splitlsb bs2) in
    let wbs1 := zext 1 bs1 in
    let wbs2 := zext 1 bs2 in
    let mul := mulB wbs1 wbs2 in
    let mul_high := msb mul in
    orb (andb_orb_all bs1_hightl bs2_hightl) mul_high.
  
  Definition Smulo bs1 bs2 : bool :=
    let (bs1_tl, bs1_sign) := eta_expand (splitmsb bs1) in
    let (bs2_tl, bs2_sign) := eta_expand (splitmsb bs2) in
    let wsign1 := copy (size bs1_tl) bs1_sign in
    let wsign2 := copy (size bs2_tl) bs2_sign in
    let xbs1 := xorB bs1_tl wsign1 in
    let xbs2 := xorB bs2_tl wsign2 in
    let (xbs1_low, xbs1_hightl) := eta_expand (splitlsb xbs1) in
    let (xbs2_low, xbs2_hightl) := eta_expand (splitlsb xbs2) in
    let and_or := andb_orb_all xbs1_hightl xbs2_hightl in
    let wbs1 := sext 1 bs1 in
    let wbs2 := sext 1 bs2 in
    let mul := mulB wbs1 wbs2 in
    let (mul_tl, mul_n) := eta_expand (splitmsb mul) in
    let (_, mul_n_minus1) := eta_expand (splitmsb mul_tl) in
    orb and_or (xorb mul_n mul_n_minus1).

  Fixpoint ltB_lsb_zip (zip : seq (bool * bool)) : bool :=
    match zip with
    | [::] => false
    | (hd1, hd2)::tl => ((unzip1 tl == unzip2 tl) && (~~hd1) && hd2) || ltB_lsb_zip tl
    end.

  (* Test if bs1 < bs2 where LSB is at the head *)
  Definition ltB_lsb (bs1 bs2 : bits) : bool := ltB_lsb_zip (extzip0 bs1 bs2).

  Fixpoint ltB_msb_zip (zip : seq (bool * bool)) :=
    match zip with
    | [::] => false
    | (hd1, hd2)::tl => (~~hd1 && hd2) || (hd1 == hd2) && ltB_msb_zip tl
    end.

  (* Test if bs1 < bs2 where MSB is at the head
     (the reverse of the usual representation) *)
  Definition ltB_msb (bs1 bs2 : bits) : bool := ltB_msb_zip (extzip0 bs1 bs2).

  Fixpoint ltB_rev_zip (zip : seq (bool * bool)) : bool :=
    match zip with
    | [::] => false
    | (hd1, hd2)::tl => (~~hd1 && hd2) || (hd1 == hd2) && ltB_rev_zip tl
    end.

  (* Test if bs1 < bs2 (where LSB is at the head) by reversing first
     and then applying ltB_msb. *)
  Definition ltB_rev (bs1 bs2 : bits) : bool :=
    ltB_rev_zip (extzip0 (rev bs1) (rev bs2)).

  (* By default, the ltB operation is ltB_lsb, which makes us easy to prove lemmas.
     To have a better performance, use ltB_rev instead. *)
  Notation ltB := ltB_lsb.

  Definition leB (bs1 bs2 : bits) : bool := (bs1 == bs2) || ltB bs1 bs2.

  Definition gtB (bs1 bs2 : bits) : bool := ltB bs2 bs1.

  Definition geB (bs1 bs2 : bits) : bool := leB bs2 bs1.

  (* signed comparison *)
  (* TODO: semantic properties of signed comparison *)

  Definition sltB (bs1 bs2: bits) :=
    let (tbs1, sign1) := eta_expand (splitmsb bs1) in
    let (tbs2, sign2) := eta_expand (splitmsb bs2) in
    let ult_tl := ltB tbs1 tbs2 in
    ((sign1 == sign2) && ult_tl) || (sign1 && ~~sign2).

  Definition sleB (bs1 bs2: bits) := (bs1 == bs2) || (sltB bs1 bs2).

  Definition sgtB (bs1 bs2: bits) := sltB bs2 bs1.

  Definition sgeB (bs1 bs2: bits) := sleB bs2 bs1.

  (* Rotate from high to low *)
  Definition rorB (bs : bits) : bits := rotr 1 bs.

  (* Rotate from low to high *)
  Definition rolB (bs : bits) : bits := rot 1 bs.

  Definition shrB1 (bs : bits) : bits := droplsb (joinmsb bs b0).

  Definition shrB (n : nat) (bs : bits) : bits := iter n shrB1 bs.

  Definition sarB1 (bs : bits) : bits := droplsb (joinmsb bs (msb bs)).

  Definition sarB (n : nat) (bs : bits) : bits := iter n sarB1 bs.

  Definition shlB1 (bs : bits) := dropmsb (joinlsb false bs).

  Definition shlB (n : nat) (bs : bits) : bits := iter n shlB1 bs.

  (* Cast an unsigned bits to an unsigned/signed bits of another size *)
  Definition ucastB (bs : bits) (n : nat) :=
    if n == size bs then bs
    else if n < size bs then low n bs
         else zext (n - size bs) bs.

  (* Cast a signed bits to an unsigned/signed bits of another size *)
  Definition scastB (bs : bits) (n : nat) :=
    if n == size bs then bs
    else if n < size bs then low n bs
         else sext (n - size bs) bs.

End Ops.

Notation ltB := ltB_lsb.

Notation "~~# bs" := (invB bs) (at level 35, right associativity) : bits_scope.
Notation "bs1 &&# bs2" := (andB bs1 bs2) (at level 40, left associativity) : bits_scope.
Notation "bs1 ||# bs2" := (orB bs1 bs2) (at level 40, left associativity) : bits_scope.
Notation "bs1 ^# bs2" := (xorB bs1 bs2) (at level 40, left associativity) : bits_scope.
Notation "-# bs" := (negB bs) (at level 35, right associativity) : bits_scope.
Notation "bs1 +# bs2" := (addB bs1 bs2) (at level 40, left associativity) : bits_scope.
Notation "bs1 -# bs2" := (subB bs1 bs2) (at level 40, left associativity) : bits_scope.
Notation "bs1 *# bs2" := (mulB bs1 bs2) (at level 40, left associativity) : bits_scope.
Notation "bs1 <# bs2" := (ltB bs1 bs2) (at level 70, no associativity) : bits_scope.
Notation "bs1 <=# bs2" := (leB bs1 bs2) (at level 70, no associativity) : bits_scope.
Notation "bs1 ># bs2" := (gtB bs1 bs2) (at level 70, no associativity) : bits_scope.
Notation "bs1 >=# bs2" := (geB bs1 bs2) (at level 70, no associativity) : bits_scope.
Notation "bs >># n" := (shrB n bs) (at level 40, left associativity) : bits_scope.
Notation "bs <<# n" := (shlB n bs) (at level 40, left associativity) : bits_scope.

Section Lemmas.

  Ltac dcase t := move: (refl_equal t); generalize t at -1.

  Local Open Scope bits_scope.

  (* size after operations *)

  Lemma size_succB bs : size (succB bs) = size bs.
  Proof.
    elim: bs => [|b bs IH]; first done. rewrite /succB -/succB.
    case: b. rewrite /= IH //. by done.
  Qed.

  Lemma size_full_adder_zip c bs0 bs1 :
    size (full_adder_zip c (zip bs0 bs1)).2 = minn (size bs0) (size bs1).
  Proof.
    dcase (zip bs0 bs1) => [zs Hzip]. rewrite -(size_zip bs0 bs1) Hzip.
    elim: zs bs0 bs1 Hzip c => [|z zs IH] bs0 bs1 Hzip c //=.
    dcase z => [[hd1 hd2] Hz]. rewrite Hz in Hzip => {Hz z}.
    dcase (bool_adder c hd1 hd2) => [[c0 hd] Hadder].
    dcase (full_adder_zip c0 zs) => [[c1 tl] Hfull]. move: Hzip.
    case: bs0; case: bs1 => //=. move=> b bs d ds Hzs. case: Hzs => H1 H2 H3.
    move: (IH _ _ H3 c0). rewrite Hfull /=. by move=> ->.
  Qed.

  Lemma size_addB bs0 bs1 : size (addB bs0 bs1) = minn (size bs0) (size bs1).
  Proof. exact: size_full_adder_zip. Qed.

  Lemma size_subB bs0 bs1 : size (subB bs0 bs1) = minn (size bs0) (size bs1).
  Proof.
    rewrite /subB /sbbB /adcB /full_adder.
    dcase (full_adder_zip (~~false) (zip bs0 (~~# bs1)%bits)) => [[c res] Hfull].
    move : (size_full_adder_zip (~~false) bs0 (~~#bs1)%bits).
    rewrite Hfull /=. by rewrite /invB size_map.
  Qed.

  Lemma size_full_mul bs0 bs1 : size (full_mul bs0 bs1) = (size bs0) + (size bs1).
  Proof.
    elim: bs0 => [| b bs0 IH] /=.
    - by rewrite /full_mul add0n size_from_nat.
    - case b.
      + rewrite size_addB size_zext size_joinlsb IH.
        rewrite addn1 addSn addnS addnC minnE. by rewrite subnn subn0.
      + by rewrite size_joinlsb IH addSn addn1.
  Qed.

  Lemma size_mulB bs0 bs1 : size (mulB bs0 bs1) = size bs0.
  Proof. by rewrite /mulB size_low. Qed.

  Lemma size_rorB bs : size (rorB bs) = size bs.
  Proof. rewrite /rorB. rewrite size_rotr. reflexivity. Qed.

  Lemma size_rolB bs : size (rolB bs) = size bs.
  Proof. rewrite /rolB. rewrite size_rot. reflexivity. Qed.

  Lemma size_shrB1 bs : size (shrB1 bs) = size bs.
  Proof.
    rewrite /shrB1. rewrite size_droplsb size_joinmsb. rewrite addn1 subn1.
    exact: Nat.pred_succ.
  Qed.

  Lemma size_shrB n bs : size (shrB n bs) = size bs.
  Proof. elim: n bs => [| n IH] bs //=. by rewrite size_shrB1 IH. Qed.

  Lemma size_sarB1 bs : size (sarB1 bs) = size bs.
  Proof.
    rewrite /sarB1. rewrite size_droplsb size_joinmsb. rewrite addn1 subn1.
    exact: Nat.pred_succ.
  Qed.

  Lemma size_sarB n bs : size (sarB n bs) = size bs.
  Proof. elim: n bs => [| n IH] bs //=. by rewrite size_sarB1 IH. Qed.

  Lemma size_shlB1 bs : size (shlB1 bs) = size bs.
  Proof.
    rewrite /shlB1. rewrite size_dropmsb size_joinlsb. rewrite addn1 subn1.
    exact: PeanoNat.Nat.pred_succ.
  Qed.

  Lemma size_shlB n bs : size (shlB n bs) = size bs.
  Proof. elim: n bs => [| n IH] bs //=. by rewrite size_shlB1 IH. Qed.
  
  Lemma size_inv_same bs :
    size bs = size (~~# bs)%bits .
  Proof .
    elim : bs; first done .
    move => b bs IH .
    rewrite /= IH // .
  Qed .  
  
  Lemma size_neg_same bs :
    size bs = size (-# bs)%bits .
  Proof .
    elim : bs; first done .
    move => b bs IH .
    rewrite /negB /= .
    case b; rewrite /= size_inv_same // . by rewrite size_succB.
  Qed .

  Lemma size_sbbB b bs0 bs1 : 
    size (sbbB b bs0 bs1).2 = minn (size bs0) (size bs1) .
  Proof .
    rewrite /sbbB /adcB /full_adder /= .
    dcase (full_adder_zip (~~ b) (zip bs0 (~~# bs1)%bits)) => [[c res] Hadder] => /= .
    have : res = (c, res).2 => // .
    rewrite -Hadder; case => -> .
    rewrite size_full_adder_zip -size_inv_same // .
  Qed .

  Lemma size_ucast bs n :
    size (ucastB bs n) = n .
  Proof .
    rewrite /ucastB /= .
    case Heq : (n == size bs) .
    - rewrite (eqP Heq) // .
    - case Hlt : (n < size bs) {Heq} .
      + rewrite size_low // .
      + rewrite size_zext addnBA; first auto with * .
        rewrite leqNgt Hlt // .
  Qed .

  Lemma size_scast bs n :
    size (scastB bs n) = n .
  Proof .
    rewrite /scastB /= .
    case Heq : (n == size bs) .
    - rewrite (eqP Heq) // .
    - case Hlt : (n < size bs) {Heq} .
      + rewrite size_low // .
      + rewrite size_sext addnBA; first auto with * .
        rewrite leqNgt Hlt // .
  Qed .

  (*
    Lemma size_tcast bs s t :
    size (Typ.tcast bs s t) = Typ.sizeof_typ t .
    Proof .
    rewrite /Typ.tcast; case s => _;
    [rewrite size_ucast // | rewrite size_scast //] .
    Qed .
 *)

  (* Lemma about comparison operations *)

  Lemma ltB_cons (hd1 : bool) (tl1 : bits) (hd2 : bool) (tl2 : bits) :
    (ltB (hd1::tl1) (hd2::tl2)) = ((zext (size tl2 - size tl1) tl1 ==
                                   (zext (size tl1 - size tl2) tl2))
                                     && (~~hd1) && hd2) || ltB tl1 tl2.
  Proof.
    rewrite /ltB /ltB_lsb_zip -/ltB_lsb_zip /=. rewrite unzip1_extzip unzip2_extzip.
    reflexivity.
  Qed.

  Lemma ltB_cons_ss (hd1 : bool) (tl1 : bits) (hd2 : bool) (tl2 : bits) :
    size tl1 = size tl2 ->
    (ltB (hd1::tl1) (hd2::tl2)) = ((tl1 == tl2) && (~~hd1) && hd2) || ltB tl1 tl2.
  Proof. move=> Hs. rewrite ltB_cons. rewrite Hs subnn !zext0. reflexivity. Qed.

  Lemma ltBnn (bs : bits) : ltB bs bs = false.
  Proof.
    elim: bs => //=. move=> hd tl IH. rewrite ltB_cons_ss; last by reflexivity.
    by rewrite eqxx andNb IH.
  Qed.

  Lemma ltB_eqF (bs1 bs2 : bits) : ltB bs1 bs2 -> bs1 == bs2 = false.
  Proof.
    move=> Hlt. apply/negP => /eqP Heq. rewrite Heq ltBnn in Hlt. discriminate.
  Qed.

  Lemma ltB_nil_cons hd tl : ltB [::] (hd::tl) = ltB (b0::[::]) (hd::tl).
  Proof.
    rewrite /ltB_lsb /ltB_lsb_zip -/ltB_lsb_zip.
    have ->: extzip0 [::] (hd :: tl) = extzip0 [:: b0] (hd :: tl) by case: tl.
    reflexivity.
  Qed.

  Lemma ltB_cons_nil hd tl : ltB (hd::tl) [::] = ltB (hd::tl) (b0::[::]).
  Proof.
    rewrite /ltB_lsb /ltB_lsb_zip -/ltB_lsb_zip.
    have ->: extzip0 (hd :: tl) [::] = extzip0 (hd :: tl) [:: b0] by case: tl.
    reflexivity.
  Qed.

  Lemma ltBn0 bs : ltB bs [::] = false.
  Proof.
    elim: bs => [| hd tl] //=. rewrite /ltB_lsb /ltB_lsb_zip -/ltB_lsb_zip /=.
    rewrite andbF orFb. rewrite /extzip0 extzip_zip. rewrite sub0n subn0 cats0 cat0s.
    by apply.
  Qed.

  Lemma ltB0n bs : (ltB [::] bs) = (bs != zeros (size bs)).
  Proof.
    elim: bs => [| hd tl IHs] //=. rewrite negb_and -/eqseq.
    rewrite ltB_nil_cons ltB_cons. rewrite subn0 sub0n zext_nil zext0.
    rewrite andbT. rewrite IHs (eq_sym tl). rewrite -IHs IHs (eq_sym tl).
    by case: hd; case: (zeros (size tl) == tl).
  Qed.

  Lemma ltB_nil_cons0l bs : ltB [::] bs = ltB ([:: b0]) bs.
  Proof.
    case: bs => [| hd tl].
    - rewrite ltBnn ltBn0. reflexivity.
    - exact: ltB_nil_cons.
  Qed.

  Lemma ltB_nil_cons0r bs : ltB bs [::] = ltB bs ([:: b0]).
  Proof.
    case: bs => [| hd tl].
    - rewrite ltBnn ltB0n eqxx. reflexivity.
    - exact: ltB_cons_nil.
  Qed.

  Lemma ltB_nil_rcons0 bs : ltB [::] (rcons bs b0) = ltB [::] bs.
  Proof.
    elim: bs => [| hd tl IH] //=. rewrite 2!ltB_nil_cons. rewrite 2!ltB_cons.
    rewrite !subn0 !sub0n !zext_nil !zext0 !andbT. rewrite IH.
    rewrite size_rcons. rewrite -zeros_rcons. rewrite eqseq_rcons eqxx andbT.
    reflexivity.
  Qed.

  Lemma ltB_rcons0_nil bs : ltB (rcons bs b0) [::] = ltB bs [::].
  Proof.
    elim: bs => [| hd tl IH] //=. rewrite 2!ltB_cons_nil. rewrite 2!ltB_cons.
    rewrite !subn0 !sub0n !zext_nil !zext0 !andbF !orFb. assumption.
  Qed.

  Lemma ltB_rcons0_r bs1 bs2 : ltB bs1 (rcons bs2 b0) = ltB bs1 bs2.
  Proof.
    elim: bs2 bs1 => [| hd2 tl2 IH] bs1 /=.
    - rewrite -ltB_nil_cons0r. reflexivity.
    - case: bs1 => [| hd1 tl1].
      + rewrite 2!ltB_nil_cons 2!ltB_cons.
        rewrite !sub0n !subn0 !zext_nil !zext0 !andbT.
        rewrite (IH [::]). rewrite size_rcons -zeros_rcons eqseq_rcons.
        rewrite eqxx andbT. reflexivity.
      + rewrite 2!ltB_cons. rewrite (IH _). rewrite size_rcons.
        have ->: (zext ((size tl2).+1 - size tl1) tl1 ==
                  zext (size tl1 - (size tl2).+1) (rcons tl2 b0)) =
        (zext (size tl2 - size tl1) tl1 ==
         zext (size tl1 - size tl2) tl2); last reflexivity.
        { case/orP: (ltn_geq_total (size tl2) (size tl1)) => H.
          - move: (ltnW H) => Hle. rewrite -subn_eq0 in Hle.
            rewrite (eqP Hle) zext0 => {Hle}.
            have Hlt: (size tl2 < size tl1) by exact: H.
            rewrite -subn_eq0 in Hlt. rewrite (eqP Hlt) zext0 => {Hlt}.
            rewrite zext_rcons0. rewrite -cats1 -zext_Sn.
            replace ((size tl1 - (size tl2).+1).+1) with (size tl1 - size tl2);
              first reflexivity.
            rewrite -addn1 (addnBAC _ H). rewrite addn1. rewrite subSS. reflexivity.
          - have Hle: (size tl1 <= size tl2) by exact: H.
            rewrite -subn_eq0 in Hle. rewrite (eqP Hle) zext0 => {Hle}.
            have Hlt: (size tl1 <= size tl2) by exact: H. rewrite -ltnS in Hlt.
            move: (ltnW Hlt) => {Hlt} Hlt. rewrite -subn_eq0 in Hlt.
            rewrite (eqP Hlt) zext0 => {Hlt}. rewrite -addn1 -(addnBAC _ H).
            rewrite addn1 zext_Sn cats1. rewrite eqseq_rcons eqxx andbT.
            reflexivity. }
  Qed.

  Lemma ltB_rcons0_l bs1 bs2 : ltB (rcons bs1 b0) bs2 = ltB bs1 bs2.
  Proof.
    elim: bs1 bs2 => [| hd1 tl1 IH] bs2 /=.
    - rewrite -ltB_nil_cons0l. reflexivity.
    - case: bs2 => [| hd2 tl2].
      + rewrite 2!ltB_cons_nil 2!ltB_cons.
        rewrite !sub0n !subn0 !zext_nil !zext0 !andbF !orFb.
        exact: (IH [::]).
      + rewrite 2!ltB_cons. rewrite (IH _). rewrite size_rcons.
        have ->: (zext (size tl2 - (size tl1).+1) (rcons tl1 b0) ==
                  zext ((size tl1).+1 - size tl2) tl2) =
        (zext (size tl2 - size tl1) tl1 ==
         zext (size tl1 - size tl2) tl2); last reflexivity.
        { case/orP: (ltn_geq_total (size tl1) (size tl2)) => H.
          - move: (ltnW H) => Hle. rewrite -subn_eq0 in Hle.
            rewrite (eqP Hle) zext0 => {Hle}.
            have Hlt: (size tl1 < size tl2) by exact: H.
            rewrite -subn_eq0 in Hlt. rewrite (eqP Hlt) zext0 => {Hlt}.
            rewrite zext_rcons0. rewrite -cats1 -zext_Sn.
            replace ((size tl2 - (size tl1).+1).+1) with (size tl2 - size tl1);
              first reflexivity.
            rewrite -addn1 (addnBAC _ H). rewrite addn1. rewrite subSS. reflexivity.
          - have Hle: (size tl2 <= size tl1) by exact: H.
            rewrite -subn_eq0 in Hle. rewrite (eqP Hle) zext0 => {Hle}.
            have Hlt: (size tl2 <= size tl1) by exact: H. rewrite -ltnS in Hlt.
            move: (ltnW Hlt) => {Hlt} Hlt. rewrite -subn_eq0 in Hlt.
            rewrite (eqP Hlt) zext0 => {Hlt}. rewrite -addn1 -(addnBAC _ H).
            rewrite addn1 zext_Sn cats1. rewrite eqseq_rcons eqxx andbT.
            reflexivity. }
  Qed.

  Lemma ltB_rcons0 bs1 bs2 : ltB (rcons bs1 b0) (rcons bs2 b0) = ltB bs1 bs2.
  Proof. by rewrite ltB_rcons0_l ltB_rcons0_r. Qed.

  Lemma ltB_nil_zext n bs : ltB [::] (zext n bs) = ltB [::] bs.
  Proof.
    elim: n => [| n IHn] /=.
    - rewrite zext0. reflexivity.
    - rewrite zext_Sn. rewrite cats1 ltB_nil_rcons0. assumption.
  Qed.

  Lemma ltB_zext_nil n bs : ltB (zext n bs) [::] = ltB bs [::].
  Proof.
    elim: n => [| n IHn] /=.
    - rewrite zext0. reflexivity.
    - rewrite zext_Sn. rewrite cats1 ltB_rcons0_nil. assumption.
  Qed.

  Lemma ltB_zeros_l n bs : ltB (zeros n) bs = ltB [::] bs.
  Proof.
    elim: n => [| n IHn] //. rewrite -zeros_rcons. rewrite ltB_rcons0_l. assumption.
  Qed.

  Lemma ltB_zeros_r n bs : ltB bs (zeros n) = ltB bs [::].
  Proof.
    elim: n => [| n IHn] //. rewrite -zeros_rcons. rewrite ltB_rcons0_r. assumption.
  Qed.

  Lemma ltB_zext_l n bs1 bs2 : ltB (zext n bs1) bs2 = ltB bs1 bs2.
  Proof.
    elim: n bs1 bs2 => [| n IHn] bs1 bs2 /=.
    - rewrite zext0. reflexivity.
    - rewrite zext_Sn cats1 ltB_rcons0_l IHn. reflexivity.
  Qed.

  Lemma ltB_zext_r n bs1 bs2 : ltB bs1 (zext n bs2) = ltB bs1 bs2.
  Proof.
    elim: n bs1 bs2 => [| n IHn] bs1 bs2 /=.
    - rewrite zext0. reflexivity.
    - rewrite zext_Sn cats1 ltB_rcons0_r IHn. reflexivity.
  Qed.

  Lemma ltB_zext n m bs1 bs2 : ltB (zext n bs1) (zext m bs2) = ltB bs1 bs2.
  Proof. rewrite ltB_zext_l ltB_zext_r. reflexivity. Qed.

  Lemma ltB_to_nat_ss (bs1 bs2 : bits) :
    size bs1 = size bs2 ->
    ltB bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Proof.
    elim: bs1 bs2 => [| hd1 tl1 IH1] [| hd2 tl2] //=. move/eqP. rewrite eqSS=> /eqP Hs.
    rewrite (ltB_cons_ss _ _ Hs). rewrite (IH1 _ Hs).
    rewrite b2n_cons_ltn. rewrite (to_nat_inj_ss Hs). reflexivity.
  Qed.

  Lemma ltB_to_nat (bs1 bs2 : bits) : ltB bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Proof.
    rewrite -(ltB_zext (size bs2 - size bs1) (size bs1 - size bs2)).
    rewrite ltB_to_nat_ss; last exact: size_zext_mkss.
    rewrite !to_nat_zext. reflexivity.
  Qed.

  Lemma ltB_msb_to_nat (bs1 bs2 : bits) : ltB_msb bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Admitted.

  Lemma ltB_msb_ltB (bs1 bs2: bits): ltB_msb bs1 bs2 = ltB bs1 bs2.
  Proof.
    rewrite ltB_msb_to_nat ltB_to_nat. reflexivity.
  Qed.

  Lemma ltB_rev_ltB_msb (bs1 bs2 : bits) : ltB_rev bs1 bs2 = ltB_msb bs1 bs2.
  Admitted.

  Lemma ltB_rev_ltB (bs1 bs2 : bits) : ltB_rev bs1 bs2 = ltB bs1 bs2.
  Proof.
    rewrite ltB_rev_ltB_msb ltB_msb_ltB. reflexivity.
  Qed.

  Lemma ltB_trans (bs1 bs2 bs3 : bits) : ltB bs1 bs2 -> ltB bs2 bs3 -> ltB bs1 bs3.
  Proof. rewrite !ltB_to_nat. exact: ltn_trans. Qed.

  Lemma eqB_ltB_gtB_cases (bs1 bs2 : bits) :
    (zext (size bs2 - size bs1) bs1 == zext (size bs1 - size bs2) bs2)
    || (ltB bs1 bs2) || (ltB bs2 bs1).
  Proof.
    move: (leq_gtn_total (to_nat bs1) (to_nat bs2)). rewrite leq_eqVlt.
    rewrite -2!ltB_to_nat. case/orP; [case/orP|].
    - rewrite to_nat_inj. move=> ->. rewrite !orTb. reflexivity.
    - move=> ->. rewrite orbT orTb. reflexivity.
    - move=> ->. rewrite !orbT. reflexivity.
  Qed.

  Lemma eqB_ltB_gtB_cases_ss (bs1 bs2 : bits) :
    size bs1 = size bs2 ->
    (bs1 == bs2) || (ltB bs1 bs2) || (ltB bs2 bs1).
  Proof.
    move=> Hs. move: (eqB_ltB_gtB_cases bs1 bs2). rewrite Hs subnn !zext0. by apply.
  Qed.

  Lemma ltBNle (bs1 bs2: bits) : ltB bs1 bs2 = ~~ leB bs2 bs1.
  Admitted.

  Lemma leBNlt (bs1 bs2: bits) : leB bs1 bs2 = ~~ ltB bs2 bs1.
  Admitted.

  Corollary sbbB_ltB_leB (bs1 bs2: bits):
    if (sbbB false bs1 bs2).1 then ltB bs1 bs2 else leB bs2 bs1.
  Admitted.


  (*---------------------------------------------------------------------------
    Aux Properties
    ---------------------------------------------------------------------------*)
  
  Lemma zip_nil S T (p:seq T) : @zip S T [::] p = [::].
  Proof.
    case p; done. Qed.

  Lemma zip_nil_r S T (p:seq S) : @zip S T p [::] = [::].
  Proof.
    case p; done. Qed.

  (*---------------------------------------------------------------------------
    Properties of arithmetic shift right
    ---------------------------------------------------------------------------*)
  
  Lemma sarB_add bs i j :
    sarB i (sarB j bs) = sarB (i + j) bs .
  Proof .
      by rewrite /sarB iter_add .
  Qed .

  Lemma sarB1_size bs :
    size (sarB1 bs) = size bs .
  Proof .
    elim : bs => [| b bs Hbs] .
    - done .
    - by rewrite /sarB1 size_joinmsb /= addn1 .
  Qed .

  Lemma sarB_size n bs :
    size (sarB n bs) = size bs .
  Proof .
    rewrite /sarB /iter .
    elim: n; first done .
    move => n IH .
      by rewrite sarB1_size .
  Qed .
  
  (*---------------------------------------------------------------------------
    Properties of logic shift right
    ---------------------------------------------------------------------------*)
  
  Lemma shrB_add bs i j :
    shrB i (shrB j bs) = shrB (i + j) bs .
  Proof .
      by rewrite /shrB iter_add .
  Qed .
  
  Lemma shrB1_size bs :
    size (shrB1 bs) = size bs .
  Proof .
    elim : bs => [| b bs Hbs] .
    - done .
    - by rewrite /shrB1 size_joinmsb /= addn1 .
  Qed .
  
  Lemma shrB_size n bs :
    size (shrB n bs) = size bs .
  Proof .
    rewrite /shrB /iter .
    elim: n; first done .
    move => n IH .
      by rewrite shrB1_size .
  Qed .

  Lemma to_nat_shrB1 : forall bs, to_nat (shrB1 bs) = div.divn (to_nat bs) 2.
  Proof.
    elim => [|bhd btl IH]/=. done.
      by rewrite/shrB1 to_nat_droplsb to_nat_joinmsb mul0n add0n/=-muln2-div.divn2.
  Qed.
  
  Lemma to_nat_shrB : forall n bs, to_nat (shrB n bs) = div.divn (to_nat bs) (2^n).
  Proof.
    intros.
    elim n => [|ns IH]/=. by rewrite div.divn1.
      by rewrite to_nat_shrB1 IH-div.divnMA expnS mulnC. 
  Qed.

  (*---------------------------------------------------------------------------
    Properties of shift left
    ---------------------------------------------------------------------------*)
  
  Lemma shlB_add bs i j :
    shlB i (shlB j bs) = shlB (i + j) bs .
  Proof .
      by rewrite /shlB iter_add .
  Qed .

  Lemma size_joinlsb T b (bs : seq T) :
    size (joinlsb b bs) = (size bs) + 1 .
  Proof .
      by rewrite /= addn1 .
  Qed .

  Lemma shlB1_size bs :
    size (shlB1 bs) = size bs .
  Proof .
    rewrite /shlB1 size_dropmsb size_joinlsb .
    rewrite subn1 addn1 .
    reflexivity .
  Qed .

  Lemma shlB_size n bs :
    size (shlB n bs) = size bs .
  Proof .
    rewrite /shlB /iter .
    elim: n; first done .
    move => n IH .
      by rewrite shlB1_size .
  Qed .

  Lemma to_nat_shlB1 : forall (p: bits), to_nat (shlB1 p) = div.modn ((to_nat p).*2) (2^size p).
  Proof. move => p. by rewrite /shlB1 to_nat_dropmsb to_nat_joinlsb size_joinlsb-subn1 addnK addn0-muln2.
  Qed.

  Lemma to_nat_shlBn:
    forall n k, k < n -> to_nat (shlB k (from_nat n 1) ) = 2 ^ k.
  Proof.
  Admitted.

  Lemma shlB_dropmsb n (p: bits) : shlB n (dropmsb p) = dropmsb (shlB n p).
  Proof.
  Admitted.

  (*---------------------------------------------------------------------------
    Properties of addition
    ---------------------------------------------------------------------------*)
  Lemma addB1 bs:
    addB bs (from_nat (size bs) 1) = succB bs.
  Proof.
  Admitted.

 
  Lemma size_full_adder : forall p q c, size (full_adder c p q).2 = minn (size p) (size q).
  Proof.
    elim => [|phd ptl IH] q c.
      by rewrite min0n /full_adder zip_nil/=. 
        by rewrite size_full_adder_zip /=. 
  Qed.

  Lemma size_adcB : forall p q c, size (adcB c p q).2 = minn (size p) (size q).
  Proof. rewrite /adcB. exact : size_full_adder. Qed.

  (*
  Lemma size_addB : forall p q, size (addB p q) = minn (size p) (size q).
  Proof. intros; rewrite/addB; apply : (size_adcB p q false).
  Qed.
   *)

  Lemma full_adder_zip_B0 : forall p n, (full_adder_zip false (zip p (zeros n))).2 = unzip1 (zip p (zeros n)).
  Proof.
    elim => [|phd ptl IH] n. by rewrite zip_nil.
    elim n =>[|ns IH1] /=. done.
    case phd; case Hfadderz :(full_adder_zip false (zip ptl (zeros ns)))=>[c1 tl];
                                                                            by rewrite -(IH ns) Hfadderz. 
  Qed.

  Lemma full_adder_B0 : forall p n, (full_adder false p (zeros n)).2 = unzip1 (zip p (zeros n)).
  Proof. rewrite /full_adder. exact : full_adder_zip_B0. Qed.
  
  Lemma addB0 : forall p n, addB p (zeros n) = unzip1 (zip p (zeros n)).
  Proof. rewrite /addB. exact : full_adder_B0. Qed.

  Lemma bool_adderC c : commutative (bool_adder c).
  Proof. by (case ; case).
  Qed.
  
  Lemma full_adderC c : commutative (full_adder c).
  Proof.
    intro. generalize dependent c.
    elim x => [|xhd xtl IH]/=.
    - intros. rewrite/full_adder zip_nil; case y; done.
    - intros; rewrite/full_adder/=; case y; try done.
      intros; rewrite/= bool_adderC. case (bool_adder c b xhd)=>[c0 hd].
      move : (IH c0 l); rewrite/full_adder; move => IH1. by rewrite IH1.
  Qed.

  Lemma adcBC c : commutative (adcB c).
  Proof. exact :full_adderC.
  Qed.

  Lemma addBA : associative (@addB).
  Proof.
  Admitted.


  Lemma addBC : commutative (addB).
  Proof.
  Admitted.

  Lemma full_adder_zip_0_l : forall p n, (full_adder_zip false (zip (zeros n) p)).2 = unzip2 (zip (zeros n) p).
  Proof.
    intros. generalize dependent p. elim n => [|ns IH] p/=.
      by rewrite zip_nil. 
      elim p => [|phd ptl IH1]/=. done.
      case phd;
        case Hfadd : (full_adder_zip false (zip (zeros ns) ptl))=>[c tl]/=;
        by rewrite -(IH ptl) Hfadd.
  Qed.
  
  Lemma add0B : forall p n, addB (zeros n) p = unzip2 (zip (zeros n) p).
  Proof.
    rewrite /addB/adcB/full_adder.  exact : full_adder_zip_0_l.
  Qed.

  Lemma adcB_nat p1 p2 c : (adcB c p1 p2).2 = from_nat (size (adcB c p1 p2).2) (c + to_nat p1 + to_nat p2).
  Proof.
    move : p2 c. elim p1 => [|phd1 ptl1 IH1] p2 c/=.
    - by rewrite size_adcB/=min0n/=/adcB/full_adder zip_nil.
    - move : c. elim p2 => [|phd2 ptl2 IH2] c/=; first done.
      move :(IH1 ptl2 c). rewrite/adcB/full_adder/=/bool_adder.
      case Hc : c; case Hphd1 : phd1; case Hphd2: phd2; move => Hfazt; case Hfadderzt : (full_adder_zip true (zip ptl1 ptl2)) =>[c0 tl0]; case Hfadderzf : (full_adder_zip false (zip ptl1 ptl2)) =>[c1 tl1]; try (rewrite Hfadderzt/= in Hfazt; rewrite Hfazt/=).
      + rewrite!odd_add!odd_double/= size_from_nat-divn2 divnDl; last by rewrite dvdn2 odd_double.
        rewrite -2!muln2!(mulnK _ (ltn0Sn 1)) divnDr;[ by rewrite (divn_small (ltnSn 1)) add0n (mulnK _ (ltn0Sn 1)) add1n addSn |by rewrite div.dvdn_mull]. 
      + rewrite add0n odd_add!odd_double/=size_from_nat-div.divn2 div.divnDr; last by rewrite div.dvdn2 odd_double. by rewrite-2!muln2!(div.mulnK _ (ltn0Sn 1)) add1n addSn. 
      + rewrite add0n uphalf_half!odd_add!odd_double/=size_from_nat-div.divn2 div.divnDl; last by rewrite div.dvdn2 odd_double. rewrite div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!(div.mulnK _ (ltn0Sn 1))div.divn_small; last done. by rewrite add0n addnA. 
      + rewrite-!muln2!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf-addnA-mulnDl-div.divn2 div.divnDr; last by rewrite div.dvdn2 muln2 odd_double. rewrite div.divn_small; last done. rewrite (div.mulnK _ (ltn0Sn 1)) add0n odd_add muln2 odd_double/=.
        move: (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf/=add0n. move=>Hfazf; by rewrite Hfazf/=size_from_nat.
      + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2 addnACA div.divnDl; last by rewrite div.dvdn2. rewrite div.divnn/=div.divnDr; last by rewrite div.dvdn2 odd_double.
        rewrite-2!muln2!div.mulnK; try done. move : (IH1 ptl2 true); rewrite/adcB/full_adder Hfadderzt/=; move => Hfazf; by rewrite Hfazf size_from_nat addnA.
      + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2!div.divnDr; try by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. rewrite div.divn_small/=; try done.
        move: (IH1 ptl2 false); rewrite/adcB/full_adder size_full_adder_zip add0n Hfadderzf/=; move => Hfazf; by rewrite Hfazf size_from_nat.
      + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2 div.divnDl; last by rewrite div.dvdn2 odd_double. rewrite div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. rewrite div.divn_small/=; try done. move : (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf!add0n/=; move => Hfazf; by rewrite Hfazf size_from_nat.
      + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf odd_add!odd_double-div.divn2 div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. move : (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf add0n/=; move => Hfazf; by rewrite Hfazf size_from_nat.
  Qed.

  Corollary to_nat_adcB b p1 p2 : to_nat (adcB b p1 p2).2 = to_nat (from_nat (size (adcB b p1 p2).2) (b + to_nat p1 + to_nat p2)).
  Proof.
    rewrite adcB_nat. rewrite size_adcB!to_nat_from_nat size_from_nat=> //. 
  Qed.

  Lemma to_nat_addB p1 p2 : to_nat (addB p1 p2) = to_nat (from_nat (size (addB p1 p2)) (to_nat p1 + to_nat p2)). 
  Proof.
    rewrite/addB. rewrite to_nat_adcB => //. 
  Qed.  

  (*---------------------------------------------------------------------------
    Properties of subtraction
  ---------------------------------------------------------------------------*)

  Lemma subB_equiv_addB_negB (p q : bits) : subB p q = addB p (negB q).
  Proof.
  Admitted.

  Lemma ltB_borrow_subB bs1 bs2:
    ltB bs1 bs2 <->
    borrow_subB bs1 bs2.
  Proof.
    split.
    +
      apply contrapositive.
    - case: (borrow_subB bs1 bs2);  rewrite /Decidable.decidable. by left. by right.
    - move => Hinv_carry.
      move /negP /eqP /eqP: Hinv_carry.
      rewrite Bool.negb_true_iff => H.
      move: (sbbB_ltB_leB bs1 bs2).
      rewrite /borrow_subB in H.
      rewrite H /=.
      move=> HleB HltB.
      rewrite leBNlt in HleB.
      move /negP : HleB => HleB.
      rewrite HltB in HleB.
      done.
      +
        move=> Hcarry.
        move: (sbbB_ltB_leB bs1 bs2).
        rewrite /borrow_subB in Hcarry.
          by rewrite Hcarry.
  Qed.

  Lemma subB_is_dropmsb_adcB_invB (p q: bits) : subB p q = dropmsb (adcB true p (invB q)).2.
  Proof. 
  Admitted.

  Lemma sub0B : forall m, subB (zeros (size m)) m = negB m.
  Proof.
    elim => [|mhd mtl IH]/=. done.
    case mhd. rewrite/subB/sbbB/adcB/full_adder/=.
    case Hfaddzf : (full_adder_zip false (zip (zeros (size mtl)) (~~# mtl)%bits))=>[c res]/=.
    have -> : res = (full_adder_zip false (zip (zeros (size mtl)) (~~# mtl)%bits)).2
      by rewrite Hfaddzf.
    rewrite full_adder_zip_0_l unzip2_zip ; last by rewrite size_zeros -size_inv_same. 
  Admitted.
  
  Lemma subB0: forall m n, subB m (zeros n) = m.
  Proof.
  Admitted.
  

  (*---------------------------------------------------------------------------
    Properties of multiplication
  ---------------------------------------------------------------------------*)


  Lemma joinlsb_false_zeros : forall n, joinlsb false (zeros n) = zeros n.+1.
  Proof. elim; done. Qed.

  Lemma zeros_cats : forall m n, zeros m ++ zeros n = zeros (m + n).
  Proof. elim => [|m IH] n. done. by rewrite addSn -!zeros_cons cat_cons -IH. Qed.

  Lemma zext_zero : forall m n, zext m (zeros n) = zeros (m + n).
  Proof. intros. by rewrite /zext zeros_cats addnC. Qed.

  Lemma full_mulB0 : forall p n, full_mul p (zeros n) = (zeros (size p + n)).
  Proof.
    elim => [|phd ptl IH] n. by rewrite /=from_natn0 size_zeros.
    case Hphd : phd; rewrite /= IH; try done.
      by rewrite joinlsb_false_zeros zext_zero addB0 unzip1_zip -zeros_cons.
  Qed.

  Lemma mulB0 p: mulB p (from_nat (size p) 0) = (from_nat (size p) 0).
  Proof.
    rewrite /mulB from_natn0 full_mulB0/low -zeros_cats take_size_cat; try by rewrite size_zeros.
      by rewrite !zeros_cats size_zeros subnDA subnn sub0n addn0.
  Qed.

  Lemma to_nat_one n : if (n==0) then to_nat (from_nat n 1) = 0 else to_nat (from_nat n 1) = 1.
  Proof.
    case n; first done.
    intros; rewrite to_nat_cons-/from_nat from_natn0 addnC/= to_nat_zeros-muln2. done.
  Qed.  
  
  Lemma full_mulB1 : forall p n, if (n==0) then full_mul p (from_nat n 1) = zeros (size p) else full_mul p (from_nat n 1) = zext n p.
  Proof.
    intros; case n.
    - elim p => [|phd ptl IH]/=; first done.
      + case phd; rewrite IH; last done. by rewrite zext_nil addB0 unzip1_zip.
    - rewrite/=;intros. elim p => [|phd ptl IH]/=.
      + rewrite zext_nil size_from_nat from_natn0. done.
      + case phd; rewrite IH; last done. 
        rewrite /addB adcB_nat. 
        rewrite to_nat_zext/=from_natn0 to_nat_zeros to_nat_zext-!muln2 mul0n!add0n addn0. 
        rewrite size_adcB size_joinlsb.
        apply/eqP ; rewrite -to_nat_inj_ss; last by rewrite !size_zext size_joinlsb size_zeros -addnA addSnnS minnC-addSnnS addn1 addnC addn2 minnn size_from_nat/=-addSnnS.
        rewrite minnE !size_zext size_joinlsb size_zeros addn1 subKn; last by rewrite addnC addSn addn1 ltnSn. 
        rewrite addn1 muln2. have->:((to_nat ptl).*2 + 1 = true + (to_nat ptl).*2) by rewrite addnC.
        rewrite-(to_nat_cons)-(to_nat_zext n0.+1 (true :: ptl)) to_nat_from_nat_bounded; first done.
        move : (to_nat_bounded (zext n0.+1 (true::ptl))); rewrite size_zext/=.
        have-> :(((size ptl).+1 + n0.+1) = (n0.+1 + (size ptl).+1)) by rewrite addnC. done.
  Qed.  

  Lemma low_zext : forall n p, low (size p) (zext n p) = p.
  Proof.
    intros; by rewrite /low/zext size_cat subnDA subnn sub0n cats0 take_cat ltnn subnn take0 cats0. 
  Qed.

  Lemma mulB1 p n: if (n == 0) then mulB p (from_nat n 1) = zeros (size p) else mulB p (from_nat n 1) = p.
  Proof. 
    move : (full_mulB1 p n). rewrite/mulB.
    case n; rewrite/=;intros.
    -rewrite full_mulB2/low size_zeros subnn zeros0 cats0.
     have->:(take (size p) (zeros (size p)) = take (size (zeros (size p))) (zeros (size p))) by rewrite size_zeros. by rewrite take_size.
       by rewrite full_mulB2 low_zext.
  Qed.

  Lemma full_mulBC : forall p q, full_mul p q = full_mul q p.
  Proof.
  Admitted.
      
  Lemma mulBC : forall (p q: bits), size p = size q -> mulB p q = mulB q p.
  Proof.

  Admitted.
  
  Lemma shlB_mul2exp i (p: bits) : iter i shlB1 p = mulB p (from_nat (size p) (2^i)).
  Proof.
    elim i. rewrite expn0. case H : ((size p) == 0). rewrite (eqP H)/=.
    elim p => [|phd ptl IH]/=; first done. case phd. rewrite/mulB/=zext_nil addB0 unzip1_zip. 
  Admitted.

  Lemma mulB_addn p m1 m2: mulB p (from_nat (size p) (m1 + m2)) = addB (mulB p (from_nat (size p) m1)) (mulB p (from_nat (size p) m2)). 
  Proof.
  Admitted.

  Lemma mulB_muln p m1 m2 : mulB p (from_nat (size p) (m1*m2)) = mulB (mulB p (from_nat (size p) m1)) (from_nat (size p) m2).
  Proof.
  Admitted.


  Lemma full_mul0B : forall m n, full_mul (zeros m) n = zeros (m + (size n)).
  Proof.
    elim => [|ms IH]n /=. by rewrite from_natn0.
      by rewrite (IH n)/joinlsb. 
  Qed.
  
  Lemma mul0B n m: mulB (zeros m) n = zeros m.
  Proof.
    rewrite/mulB full_mul0B/low!size_zeros subnDA subnn sub0n cats0-zeros_cats take_size_cat; [ done | by rewrite size_zeros]. Qed.

  Lemma mulB_nil_l n : mulB [::] n = [::].
  Proof. by rewrite/mulB/low/= take0. Qed.

  Lemma full_mul_nil_r n : full_mul n [::]= zeros (size n).
  Proof.
    elim n. done. intros. rewrite/=. case a. rewrite H zext_nil addB0 unzip1_zip; last by rewrite size_joinlsb. done.
      by rewrite H.
  Qed.

  Lemma mulB_nil_r n : mulB n [::] = zeros (size n).
  Proof.  rewrite/mulB full_mul_nil_r/low size_zeros subnn cats0 take_oversize; last by rewrite size_zeros. done. Qed.

  Lemma to_nat_full_mul p1 p2 : to_nat (full_mul p1 p2) = to_nat (from_nat (size (full_mul p1 p2)) (to_nat p1 * to_nat p2)).
  Proof.
    move : p2. elim p1 => [|phd1 ptl1 IH] p2 /=; first by rewrite!from_natn0 size_zeros!add0n. 
    move : (to_nat_bounded ptl1) => Hbd1; move : (to_nat_bounded p2) => Hbd2.
    move : (ltn_mul Hbd1 Hbd2); rewrite -expnD; move => Hbd. generalize Hbd.
    rewrite -(ltn_pmul2l (ltn0Sn 1)) -expnS mulnC in Hbd. move => Hbd'.
    case phd1. 
    - rewrite/=to_nat_addB size_addB size_joinlsb to_nat_joinlsb (IH p2) size_full_mul size_zext to_nat_zext addn1-addSn addnC minnn addn0 !to_nat_from_nat -!muln2 muln_modl; last done. rewrite addnS expnS.
      have-> :(2 * 2 ^ (size p2 + size ptl1) = (2 ^ (size ptl1 + size p2) * 2)) by rewrite mulnC addnC. rewrite div.modnDml.
      have->:(((1 + to_nat ptl1 * 2) * to_nat p2) = to_nat ptl1 * to_nat p2 * 2 + to_nat p2) by rewrite mulnDl mul1n; ring. done.
    - rewrite size_joinlsb to_nat_joinlsb (IH p2) size_full_mul addn0 add0n-!muln2!to_nat_from_nat_bounded; first ring; try exact. by rewrite addn1 mulnAC.
  Qed.

  Lemma to_nat_mulB p1 p2 : to_nat (mulB p1 p2) = to_nat (from_nat (size p1) (to_nat p1 * to_nat p2)).
  Proof.
    rewrite/mulB/low size_full_mul to_nat_cat to_nat_zeros mul0n addn0 to_nat_take size_full_mul.
    case Hlt : (size p1 < size p1 + size p2). 
    rewrite to_nat_full_mul size_full_mul 2!to_nat_from_nat expnD.
    set n:= (to_nat p1 * to_nat p2). set x :=(2 ^ size p1). set y:= (2 ^ size p2).
    have: (n %% x) = (n %/ (x * y) * (x * y) + n %% (x * y)) %% x.
    { rewrite -(divn_eq n (x * y)). reflexivity. }
    rewrite -modnDm.
    have: (n %/ (x * y) * (x * y)) %% x = 0.
    { rewrite (mulnC x y) mulnA modnMl. reflexivity. }
    move=> ->. rewrite add0n. rewrite modn_mod. move=> <-. rewrite to_nat_from_nat. reflexivity.
    rewrite to_nat_full_mul size_full_mul.
    have Hadd0 : size p1 = size p1 +0 by rewrite addn0. rewrite {1}Hadd0 ltn_add2l in Hlt.
    move/negP/negP: Hlt. rewrite-eqn0Ngt. move/eqP => Hlt. by rewrite Hlt addn0.
  Qed.

  Lemma mulnB_eq0: forall m n : bits, (mulB m n == (zeros (size m))) = (m == zeros (size m)) || (n == zeros (size n)).
  Proof.
    intros.
    case Hmz : (m == zeros (size m)).
    - by rewrite (eqP Hmz) mul0B size_zeros eq_refl.
    - case Hnz : (n == zeros (size n)).
      + rewrite (eqP Hnz)/mulB full_mulB0/low size_zeros subnDA subnn sub0n cats0-zeros_cats take_size_cat/= ; last by rewrite size_zeros. exact: eq_refl.
      + move : Hmz Hnz. move : n.
        elim m => [|mhd mtl IH]n/=. by rewrite mulB_nil_l.
        rewrite /mulB/=. case Hmhd: mhd. intros.
        move : (IH n). rewrite/mulB/low size_addB size_joinlsb size_zext!size_full_mul addnAC addn1 subnDA subnn sub0n cats0. intros. rewrite addnC minnn subnDA subnAC subnn sub0n cats0. rewrite (take_nth false). 
  Admitted.

  Lemma mulB0' : forall m n, mulB m (zeros n) = zeros (size m).
  Proof.
    intros. rewrite/mulB full_mulB0/low -zeros_cats take_cat size_zeros/=.
    case H : (size m < size m). rewrite (ltnn (size m)) in H. discriminate.
      by rewrite size_cat size_zeros subnDA subnn take0 sub0n !cats0.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of bitwise and
    ---------------------------------------------------------------------------*)

  Lemma and1B n : left_id (ones n) andB.
  Proof.
  Admitted.

  Lemma and0B n : left_zero (from_nat n 0) andB.
  Proof.
  Admitted.

  Lemma andB_copy_case :
    forall b (bs : bits),
      andB (copy (size bs) b) bs = if b then bs else (from_nat (size bs) 0).
  Proof.
    move=> [] bs.
    - exact: and1B.
    - rewrite -/(zeros (size bs)) -from_natn0. exact: and0B.
  Qed.

  Lemma andB_copy_mul :
    forall b (bs : bits),
      andB (copy (size bs) b) bs = mulB bs (from_nat (size bs) b).
  Proof.
    move=> b bs. rewrite andB_copy_case. case: b.
    - move : (mulB1 bs (size bs)). case H : (size bs == 0); last done.
      + by rewrite (eqP H) (size0nil (eqP H)).
    - rewrite mulB0; reflexivity.
  Qed.
  

  (*---------------------------------------------------------------------------
    Properties of signed extend 
  ---------------------------------------------------------------------------*)
  
  Lemma adc_sext_add_high b bs0 bs1 :
    size bs0 = size bs1 ->
    from_bool 1 (adcB (to_bool b) bs0 bs1).1 ==
    high 1 ((zext (size bs0) b) +# (sext 1 bs0) +# (sext 1 bs1))%bits .
  Admitted .

  Lemma adc_sext_add_low b bs0 bs1 :
    size bs0 = size bs1 ->
    (adcB (to_bool b) bs0 bs1).2 ==
    low (size bs0) ((zext (size bs0) b) +# (sext 1 bs0) +# (sext 1 bs1))%bits .
  Admitted .

  
  Lemma adc_false_sext_add_high bs0 bs1 :
    size bs0 = size bs1 ->
    from_bool 1 (adcB false bs0 bs1).1 ==
    high 1 ((sext 1 bs0) +# (sext 1 bs1))%bits .
  Proof .
    move => Hsize .
    move : (adc_sext_add_high [::false] Hsize) .
    have : (to_bool [:: false] = false) .
    { rewrite /to_bool // . }
    move => Hbool .
    rewrite Hbool => {Hbool} Heq .
    rewrite (eqP Heq) .
  Admitted .  

  Lemma adc_false_sext_add_low bs0 bs1 :
    size bs0 = size bs1 ->
    (adcB false bs0 bs1).2 ==
    low (size bs0) ((sext 1 bs0) +# (sext 1 bs1))%bits .
  Proof .
    move => Hsize .
    move : (adc_sext_add_low [::false] Hsize) .
    have : (to_bool [:: false] = false) .
    { rewrite /to_bool // . }
    move => Hbool .
    rewrite Hbool => {Hbool} Heq .
    rewrite (eqP Heq) .
  Admitted .  

  Lemma sbb_sext_sub_high b bs0 bs1 :
    size bs0 = size bs1 ->
    from_bool 1 (sbbB (to_bool b) bs0 bs1).1 ==
    high 1 ((sext 1 bs0) -# (sext 1 bs1) -# (zext (size bs0) b))%bits .
  Admitted .

  Lemma sbb_sext_sub_low b bs0 bs1 :
    size bs0 = size bs1 ->
    (sbbB (to_bool b) bs0 bs1).2 ==
    low (size bs0) ((sext 1 bs0) -# (sext 1 bs1) -# (zext (size bs0) b))%bits .
  Admitted .

  Lemma sbb_false_sext_sub_high bs0 bs1 :
    size bs0 = size bs1 ->
    from_bool 1 (sbbB false bs0 bs1).1 ==
    high 1 ((sext 1 bs0) -# (sext 1 bs1))%bits .
  Proof .
    move => Hsize .
    move : (sbb_sext_sub_high [::false] Hsize) .
    have : (to_bool [:: false] = false) .
    { rewrite /to_bool // . }
    move => Hbool .
    rewrite Hbool => {Hbool} Heq .
    rewrite (eqP Heq) .
  Admitted .
  
  Lemma sbb_false_sext_sub_low bs0 bs1 :
    size bs0 = size bs1 ->
    (sbbB false bs0 bs1).2 ==
    low (size bs0) ((sext 1 bs0) -# (sext 1 bs1))%bits .
  Proof .
    move => Hsize .
    move : (sbb_sext_sub_low [::false] Hsize) .
    have : (to_bool [:: false] = false) .
    { rewrite /to_bool // . }
    move => Hbool .
    rewrite Hbool => {Hbool} Heq .
    rewrite (eqP Heq) .
  Admitted .

  Lemma mul_sext bs0 bs1 :
    full_mul bs0 bs1 ==
    ((sext (size bs0) bs0) *# (sext (size bs0) bs1))%bits .
  Admitted .
   

  (*---------------------------------------------------------------------------
    Properties of unsigned division
  ---------------------------------------------------------------------------*)



  (*---------------------------------------------------------------------------
    Others
  ---------------------------------------------------------------------------*)  
  Lemma to_nat_not_zero (q : bits) : (q == zeros (size q))=false -> (to_nat q == 0)=false.  
  Proof.
    intro. apply negbT in H; rewrite -ltB0n ltB_to_nat/= in H.
    apply/eqP. rewrite-(prednK H). apply Nat.neq_succ_0. 
  Qed.


  
(*---------------------------------------------------------------------------
    Others
  ---------------------------------------------------------------------------*) 

  Fixpoint sig_bits_aux bs n : nat :=
    match bs with
    | [::] => n
    | hd :: tl => if hd then n else sig_bits_aux tl (n - 1)
    end .

  Definition sig_bits bs := sig_bits_aux (rev bs) (size bs).

  Lemma rev_cons_nil : forall (hd:bool) tl, ~~ (rcons tl hd == [::]).
  Proof.
    intros. move : hd. elim tl;  done.
  Qed.
    
  Lemma rev_nil : forall (hd:bool) tl, ~~ (rev (hd :: tl) == [::]).
  Proof.
    move => hd tl. rewrite rev_cons. exact : rev_cons_nil.
  Qed.

  Lemma sig_bits_le : forall bs,  (sig_bits bs) <= size bs.
  Proof.
    rewrite/sig_bits. move =>bs.
    move : (revK bs) => Hrev. rewrite -Hrev. set bsr := rev bs. rewrite revK size_rev.
    elim bsr => [|bsr_hd bsr_tl IH]; first by done.  
    case Hbsr_hd: bsr_hd.
    -  done.
    - rewrite/=-{1}addn1 addnK. move :( ltnSn (size bsr_tl)) => Hsn.
      move : (leq_ltn_trans IH Hsn) => Hle. auto.
  Qed.

  Lemma upper_bound : forall bs,
      ltB bs (joinmsb (zeros (sig_bits bs)) b1).
  Proof.
    rewrite /sig_bits . move => bs.
    move : (revK bs) => Hrev. rewrite -Hrev. set bsr := rev bs. rewrite revK size_rev.
    elim bsr => [|bsrhd bsrtl IH] .
    - by rewrite /ltB.
    - case Hbsrhd: bsrhd; rewrite rev_cons /=; move : IH.
      + rewrite 2!ltB_to_nat /= add0n 2!to_nat_joinmsb 2!to_nat_zeros 2!size_zeros to_nat_rcons 3!mul1n 2!addn0 size_rev -addnn ltn_add2r.
        move : (sig_bits_le (rev bsrtl)); rewrite/sig_bits revK size_rev.
        move => Hle.
        move: (leq_pexp2l (ltn0Sn 1) Hle). move => Hexp Hlt1.
        exact : (ltn_leq_trans Hlt1 Hexp).
      + rewrite 2!ltB_to_nat /= to_nat_rcons mul0n 2!to_nat_joinmsb 2!to_nat_zeros 2!size_zeros 3!addn0 2!mul1n subn1. auto.
  Qed.

  Lemma lower_bound : forall bs,
      0 < sig_bits bs -> ltB (joinmsb (zeros (sig_bits bs).-1) b1) bs.
  Proof.
    rewrite/sig_bits; move =>bs.
    move : (revK bs) => Hrev. rewrite -Hrev. move: Hrev; set bsr := rev bs.
    move => Hrev. rewrite revK size_rev.
    elim bsr => [|bsrhd bsrtl IH] ; first done. 
    rewrite ltB_to_nat/=subn1/= to_nat_joinmsb size_zeros rev_cons to_nat_rcons.
    case bsrhd. rewrite/= to_nat_zeros addn0 2!mul1n.
  Admitted.    
    
  Lemma from_nat_exp_joinmsb0 : forall n, from_nat (n+1) (2^n) == joinmsb (zeros n) b1.
  Proof.
    elim => [|ns IH]. done.
    rewrite -to_nat_inj_ss. 
    rewrite to_nat_from_nat_bounded; first by rewrite to_nat_joinmsb size_zeros to_nat_zeros addn0 mul1n.
    by rewrite (ltn_exp2l ns.+1 (ns.+1 +1) (ltnSn 1)) addn1 ltnSn.
    by rewrite size_from_nat size_joinmsb size_zeros. 
  Qed.
  
  Lemma from_nat_exp_mul : forall n1 n2 , 1<n1 -> 1<n2->full_mul (from_nat n1 (2^(n1-1))) (from_nat n2 (2^(n2-1))) == from_nat (n1+n2) (2^(n1+n2-2)).
  Proof.
    intros.
    have Hsz : (size (full_mul (n1) -bits of (2 ^ (n1 - 1)) (n2) -bits of (2 ^ (n2 - 1))) = size ((n1 + n2) -bits of (2 ^ (n1 + n2 - 2)))) by rewrite size_full_mul !size_from_nat.
    rewrite -(to_nat_inj_ss Hsz).
    rewrite to_nat_full_mul size_full_mul !size_from_nat !to_nat_from_nat_bounded; first rewrite -expnD. 
    rewrite -addnABC. 
Admitted.
 

  Lemma orb_all_true : forall bs, orb_all bs = (0 < to_nat bs).
  Proof.
    elim => [| bshd bstl IH]; first done.
    case Hbshd: bshd; rewrite/=.
    - by rewrite orbT add1n ltn0Sn. 
    - rewrite orbF add0n -muln2 muln_gt0 IH.
      by rewrite (ltn0Sn 1) andbT.
  Qed.    

  Lemma orb_all_false : forall bs, (orb_all bs == false) = (to_nat bs == 0).
  Proof.
    elim => [|bshd bstl IH]. done.
    case Hbshd: bshd ; rewrite /=.
    - rewrite orbT; auto.
    - rewrite orbF IH add0n. symmetry. exact : double_eq0 .
  Qed.

  Lemma andb_orb_all_zip11 : forall bsptl , andb_orb_all_zip ((b1, b1)::bsptl) = true.
  Proof.
    intros. by rewrite/= andbT !orbT.
  Qed.

  Lemma andb_orb_all_zipb0 : forall bsptl b, andb_orb_all_zip ((b, b0)::bsptl) = andb_orb_all_zip bsptl.
  Proof.
    intros. by rewrite/=andbF orbF.
  Qed.

  Lemma andb_orb_all_zip01 : forall bsptl, andb_orb_all_zip ((b0, b1)::bsptl) = if (andb_orb_all_zip bsptl) then true else orb_all (unzip1 bsptl).
  Proof.
    intros. rewrite/=andbT orbF. case (andb_orb_all_zip bsptl); try done.
  Qed.

  Lemma rev_behead : forall bs, zext (size bs - (size bs - 1)) (rev (behead bs)) = rev bs.
  Proof.
    elim =>[|bshd bstl IH]. by rewrite/=sub0n zext0.
    rewrite/=. Abort.

  Lemma rev_copy : forall n (b: bool), rev (copy n b) = copy n b.
  Proof.
    elim => [| ns IH] b. done.
    rewrite/=-{1}(IH b) rev_cons revK.
    case b. by rewrite-/b1 ones_rcons. by rewrite-/b0 zeros_rcons. 
  Qed.
  
  Lemma sig_bits_zeros n : sig_bits (zeros n) = 0.
  Proof.
    elim n. done.
    rewrite/sig_bits. intros. rewrite rev_cons rev_copy zeros_rcons /zeros/=size_copy-addn1 addnK.
    by rewrite size_zeros rev_copy in H.
  Qed.

  Lemma sig_bits_nil : sig_bits nil = 0.
  Proof. done. Qed.

  Lemma sig_bits_rcons0 bs : sig_bits (rcons bs b0) = sig_bits bs.
  Proof.
    by rewrite/sig_bits rev_rcons/= size_rcons -addn1 addnK. 
  Qed.

  Lemma sig_bits_rcons1 bs : sig_bits (rcons bs b1) = (size bs).+1.
  Proof.
    by rewrite/sig_bits rev_rcons/=size_rcons.
  Qed.
    
  Lemma sig_bits_zext : forall bs n, sig_bits (zext n bs) = sig_bits bs.
  Proof.
    elim => [| bshd bstl IH] n; first by rewrite zext_nil sig_bits_zeros sig_bits_nil.
    elim n => [| ns IHm] ; first by rewrite zext0.
    move : IHm.
    rewrite /sig_bits/=/zext rev_cat rev_copy/= 2!size_cat/= size_zeros. move => IHm.
    by rewrite-IHm/= zeros_cons -cat_cons rev_cat rev_copy/=subn1/=addnS.
  Qed.

  Lemma sig_bits_cons b bs : sig_bits bs <= sig_bits (b::bs).
  Proof.
    rewrite/sig_bits rev_cons/= -(size_rev bs).
    set bsr := rev bs. move : b.
    elim  bsr; first done. move => a l IH b.
    case a.
    - rewrite/=; exact : (ltn_trans (ltnSn (size l)) (ltnSn (size l).+1)). 
    - by rewrite/=!subn1/=. 
  Qed.

    
  Lemma sig_bits_zero_cat bs : bs = low (sig_bits bs) bs ++ zeros (size bs - (sig_bits bs)).
  Proof.
    rewrite /sig_bits -(size_rev bs) -{1 4}(revK bs). set bsr := rev bs.
    elim bsr => [| bshd bstl IH]. done.
    move : IH. rewrite/low -!catA !zeros_cats size_rev/=subn1/=.
    move : (sig_bits_le (rev bstl)); rewrite/sig_bits revK size_rev; move => Hle.
    rewrite -subn_eq0 in Hle. rewrite (eqP Hle)/=add0n size_rev/=. move => IH.
    case Hbshd : bshd.
    - rewrite subnn/= cats0. have-> : (size bstl).+1 = (size (rev (true::bstl))) by rewrite size_rev/=. by rewrite take_size.
    - generalize Hle; rewrite subn_eq0; move => Hle'. Local Opaque drop.
      rewrite subnS (eqP Hle)/=add0n (subSn Hle') rev_cons {1}IH rcons_cat -{1}cats1 -/b0.
      have->: (b0::nil) = (zeros 1) by done. rewrite zeros_cats. 
      have->: (rcons (rev bstl) b0) = (rev bstl) ++ [:: b0] by rewrite cats1.
      rewrite (takel_cat); last by rewrite size_rev Hle'. 
      by rewrite addn1.
  Qed.
  
  Lemma sig_bits_to_nat bs : to_nat (ucastB bs (sig_bits bs)) = to_nat bs.
  Proof.
    rewrite/ucastB.
    case Hsz: (sig_bits bs == size bs); try done.
    case Hsz1 : (sig_bits bs < size bs). by rewrite {3}(sig_bits_zero_cat bs) to_nat_cat to_nat_zeros mul0n addn0.
    by rewrite to_nat_zext.
  Qed.


  Lemma sig_bits_is0 bs :  (sig_bits bs = 0) <-> (bs = zeros (size bs)).
  Proof.
    elim bs. by rewrite sig_bits_nil/=.
    intros. split. move => Heq0. move : (sig_bits_cons a l). 
    rewrite Heq0 leqn0. move/eqP => Heq0'. apply ->H in Heq0'. move : Heq0. rewrite Heq0' /= size_zeros.
    case a; last done. have {1}-> : (true :: zeros (size l)) = zext (size l) (true ::nil) by done.
    move : (sig_bits_zext [::true] (size l))=> H1. by rewrite H1/sig_bits/=. 
    move => Hal. by rewrite Hal sig_bits_zeros.
  Qed.
  
  Lemma sig_bits_consb: forall (bs : seq bool) (b:bool),
      sig_bits bs = 0 -> (sig_bits bs) + b = (sig_bits (b :: bs)). 
  Proof.
    intros. case b. rewrite addn1/=. rewrite-> sig_bits_is0 in H.
    rewrite H sig_bits_zeros. have ->:((true :: zeros (size bs)) = zext ( (size bs)) [::true]) by done.
      by rewrite sig_bits_zext/sig_bits/=.
    rewrite addn0 H. rewrite-> sig_bits_is0 in H. by rewrite H zeros_cons sig_bits_zeros.
  Qed.
  
  Lemma sig_bits_cons1: forall (bs : seq bool) b, 0 < sig_bits bs -> (sig_bits bs).+1 = (sig_bits (b :: bs)).
  Proof.
  Admitted.
    
  Lemma get_sig_bit bs: 0 < sig_bits bs-> nth b1 bs (sig_bits bs - 1).
  Proof.
    rewrite/sig_bits -(size_rev bs) -{1 3}(revK bs). set bsr := rev bs.
    rewrite -{2 4 5}(revK bsr) size_rev -/(sig_bits (rev bsr)).
    elim bsr => [|bsrhd bsrtl IH]; first done.
    case bsrhd. Local Opaque nth.
    - by rewrite /sig_bits revK rev_cons size_rcons !size_rev nth_rcons /=subn1/= size_rev eq_refl ltnn.
    - rewrite /sig_bits/=revK size_rev/= rev_cons 2!subn1/= nth_rcons. 
      rewrite -{1 2 3 4 7 8 9 10}(revK bsrtl) size_rev -/(sig_bits (rev bsrtl)). 
      move : (sig_bits_le (rev bsrtl))=> Hle. rewrite leq_eqVlt size_rev in Hle.
      move/orP : Hle => [Heq|Hlt]. 
      + rewrite size_rev-(eqP Heq) -subn1. 
        case Hsz : (sig_bits (rev bsrtl) - 1 < sig_bits (rev bsrtl)); first exact IH.
        move => Hgt0. rewrite -subn_gt0 (subKn Hgt0) in Hsz; discriminate.
      + rewrite-subn1. move => Hgt0. rewrite -subn_gt0 (subnBA _ Hgt0) size_rev -(addnBAC _ (ltnW Hlt)) addn1 ltn0Sn. move : Hgt0. exact : IH.
  Qed.

  Lemma andb_orb_all_0s : forall n , andb_orb_all (zeros n) (zeros n) = false.
  Proof.
    elim => [|ns IH]. done.
    rewrite /andb_orb_all rev_copy/= andbF orbF. by rewrite/andb_orb_all rev_copy in IH.
  Qed.

  Lemma andb_orb_all_0nm : forall n m, andb_orb_all (zeros n) (zeros m) = false.
  Proof.
    elim => [|ns IH]; elim => [|ms IHm]; first done.
    - rewrite zeros0/andb_orb_all rev_copy/= size_copy andbF orbF.
      move : (eq_refl (size (copy ms b0))) => Heq.
      have -> : (zip (copy ms b0) (copy ms b0)) = extzip b0 b0 (copy ms b0) (copy ms b0) by
      rewrite extzip_zip_ss. rewrite -/extzip0-/(zeros ms). move : (andb_orb_all_0s ms).
      by rewrite/andb_orb_all rev_copy. 
    - rewrite /zeros0/andb_orb_all /rev/= andbF orbF size_copy.
      move : (eq_refl (size (copy ns b0))) => Heq.
      have -> : (zip (copy ns b0) (copy ns b0)) = extzip b0 b0 (copy ns b0) (copy ns b0) by
      rewrite extzip_zip_ss. rewrite -/extzip0-/(zeros ns). move : (andb_orb_all_0s ns).
      by rewrite/andb_orb_all rev_copy. 
    - move : (IH ms ). by rewrite/=/andb_orb_all 2!zeros_cons 2!rev_copy/= andbF orbF/=.
  Qed.      
      
  Lemma andb_orb_all_0r : forall bs n, andb_orb_all bs (zeros n) = false.
  Proof.
    elim => [|bshd bstl IH]; elim => [|ns IHm].
    - by rewrite (andb_orb_all_0s 0).
    - by rewrite (andb_orb_all_0nm 0 ns.+1).
    - rewrite/=/andb_orb_all/rev/= andbF orbF.
      move : (size_copy (size bstl) b0)=> Hsz. symmetry in Hsz.
      rewrite -(extzip_zip_ss b0 b0 Hsz)-/extzip0.
      move: (IH (size bstl)); by rewrite/andb_orb_all rev_copy.
    - move : (IH ns). by rewrite/andb_orb_all 2!rev_copy/= andbF orbF. 
  Qed.

  Lemma orb_all_0 n : orb_all (zeros n) = false.
  Proof.
    elim n => [|ns IH]; first done. by rewrite/=orbF IH. Qed.
    
  Lemma andb_orb_all_0l : forall bs n, andb_orb_all (zeros n) bs = false.
  Proof.
    intros. rewrite/andb_orb_all /extzip0 extzip_zip size_rev size_zeros zeros_cats. 
  Admitted.


  Lemma size_unzip (bsp: seq (bool*bool)) : size (unzip1 bsp) = size (unzip2 bsp).
  Proof.
    elim bsp; first done. intros. by rewrite/=H.
  Qed.

  Lemma orb_all_rev bsp : orb_all (rev bsp) = orb_all bsp.
  Proof.
    elim bsp => [| bsphd bsptl IH]; first done.
    elim bsphd.
    - rewrite !orb_all_true rev_cons to_nat_rcons mul1n/=.
      case bsptl.
      + by rewrite/=expn0 -muln2 mul0n.
      + intros; by rewrite size_rev/=2!addn_gt0/= expn_gt0/= orbT. 
    - rewrite !orb_all_true rev_cons to_nat_rcons mul0n /= add0n addn0. 
      elim bsptl; first done.
      intros. rewrite rev_cons to_nat_rcons/=.
      rewrite size_rev -2!muln2 mulnDl 2!addn_gt0 H -muln2.
      by rewrite !muln_gt0 !andbT expn_gt0/= andbT Bool.orb_comm. 
  Qed.

  Lemma head_rev : forall bs b, head b0 (rev (b::bs)) = head b (rev bs).
  Proof.
    intros.
    rewrite -nth0 nth_rev/=; last done. rewrite subn1/= -last_nth.
    rewrite -nth0. 
    move : bs b.
    elim => [ | bshd bstl IH] b; first done.
    rewrite nth_rev/=; last done. by rewrite subn1/=-last_nth.
  Qed.

  Lemma andb_orb_all_true : forall bs1 bs2, andb_orb_all bs1 bs2 -> (0 < sig_bits bs1) /\ (0 < sig_bits bs2).
  Proof.
  Admitted.

  Lemma andb_orb_all_sig_bits : forall bs1 bs2,
      size bs1 = size bs2 -> andb_orb_all bs1 bs2 -> size bs1 < (sig_bits bs1) + (sig_bits bs2).
  Proof.
    rewrite /andb_orb_all. move => bs1 bs2.
    rewrite -{1 3}(revK bs2). set bs2r :=rev bs2. rewrite size_rev.
    move : bs1 bs2r.
    elim => [| bs1hd bs1tl IH]; elim => [| bs2rhd bs2rtl IHm]; try done.
    move => Hszcons. generalize Hszcons. move => Hsz; rewrite /=-addn1 in Hsz; symmetry in Hsz; rewrite -addn1 in Hsz.
    move : (addIn Hsz) => Hsz'; rewrite 2!addn1 in Hsz.
    case Hbs1tl0 :  (sig_bits bs1tl) => [| nsbbs1tl].
    - move:(sig_bits_consb bs1hd Hbs1tl0) => Hconsbs1hd. 
      rewrite-Hconsbs1hd rev_cons. rewrite /extzip0 extzip_zip_ss ; last by rewrite /=-Hsz.
      have Hzip : (zip (bs1hd :: bs1tl) (bs2rhd :: bs2rtl)) = (bs1hd, bs2rhd) :: (zip bs1tl bs2rtl) by done. 
      move :Hszcons; case bs2rhd.
      + move=> Hszcons. rewrite sig_bits_rcons1 size_rev Hsz (Hbs1tl0) (add0n)(*leq_addl*).
        move => Handb. generalize Handb.
        rewrite-(extzip_zip_ss b0 b0 Hszcons) -/extzip0 -(revK (true :: bs2rtl))-/(andb_orb_all (bs1hd :: bs1tl) (rev (true :: bs2rtl))).
        move => Handb'. move : (andb_orb_all_true Handb') => [Hgt1 Hgt2].
        move : Hgt1. case bs1hd. by rewrite -(sig_bits_consb true Hbs1tl0) addn1 ltnSn.
        by rewrite -(sig_bits_consb false Hbs1tl0) Hbs1tl0 addn0. 
      + rewrite sig_bits_rcons0/=andbF orbF. symmetry in Hsz'; rewrite-(extzip_zip_ss b0 b0 Hsz') -/extzip0.
        rewrite->sig_bits_is0 in Hbs1tl0. rewrite Hbs1tl0.
        by rewrite -{2}(revK bs2rtl) -/(andb_orb_all (zeros (size bs1tl)) (rev bs2rtl)) andb_orb_all_0l.
    - move: (ltn0Sn nsbbs1tl); rewrite -Hbs1tl0; move => Hgt0. move:(sig_bits_cons1 bs1hd Hgt0) => Hconsbs1hd. 
      rewrite -Hconsbs1hd rev_cons. rewrite /extzip0 extzip_zip_ss ; last by rewrite /=-Hsz.
      have -> : (zip (bs1hd :: bs1tl) (bs2rhd :: bs2rtl)) = (bs1hd, bs2rhd) :: (zip bs1tl bs2rtl) by done.
      case bs2rhd.
      + move => Handb. by rewrite sig_bits_rcons1 size_rev Hsz/= -{1}(add0n (size bs1tl).+1) ltn_add2r ltn0Sn.
        (*exact : (ltn_addl (sig_bits bs1tl).+1 (ltnSn (size bs1tl))). *)
      + rewrite sig_bits_rcons0 andb_orb_all_zipb0. symmetry in Hsz'.
        rewrite-(extzip_zip_ss b0 b0 Hsz') -/extzip0. move => Handb.
        move : (IH bs2rtl Hsz' Handb). by rewrite/=addSn.
  Qed.

  Lemma andb_orb_all_sig_bits_gt : forall bs1 bs2,
      size bs1 = size bs2 -> andb_orb_all bs1 bs2 = false -> (sig_bits bs1) + (sig_bits bs2) <= size bs1.
  Proof.
  Admitted.
  
  Compute (sig_bits (zext 4 (b1::b1::b0::(b0::nil)))). (*2*)
  Compute (to_nat (b1::b1::b0::(b0::nil))). (*3*)
  Compute (msb (b1::b1::b0::(b0::nil))). (*0*)
  Compute (lsb (b1::b1::b0::(b0::nil))). (*1*)

  (*  
fix andb_orb_all_zip (bsp : seq (bool * bool)) : bool :=
  match bsp with
  | [::] => false
  | (_, ls2_high) :: bsp_tl =>
      let result_tl := andb_orb_all_zip bsp_tl in
      let result_or := orb_all (unzip1 bsp) in result_tl || result_or && ls2_high
  end
Definition Umulo bs1 bs2 : bool :=
    let (_, bs1_hightl) := eta_expand (splitlsb bs1) in
    let (_, bs2_hightl) := eta_expand (splitlsb bs2) in
    let wbs1 := zext 1 bs1 in
    let wbs2 := zext 1 bs2 in
    let mul := mulB wbs1 wbs2 in
    let mul_high := msb mul in
    orb (andb_orb_all bs1_hightl bs2_hightl) mul_high.*)
  Definition va1 := (b1::b1::(b0::nil)).
  Definition va2 := (b0::b0::(b1::nil)).
  Definition wva1 := (b1::b1::b0::(b0::nil)).
  Definition wva2 := (b0::b0::b1::(b0::nil)).
  Definition va1h := let (_, bh) := eta_expand (splitlsb va1) in bh.
  Definition va2h := let (_, bh) := eta_expand (splitlsb va2) in bh.
  Compute (msb (mulB wva1 wva1)).
  Compute (msb (mulB wva2 wva2)).
  Compute (Umulo va1 va1). (*1*)
  Compute (Umulo va2 va2). (*1*)
  Compute (andb_orb_all va2h va2h). 
  Compute (andb_orb_all va1 va1). 
  Compute (size va1). (*3*) Compute (sig_bits va1). (*2*)
  Compute (nth b1 va1 (2-1)). (*1*) Compute (msb va1). (*0*)

 

  Lemma msb_sig_bits bs : msb bs -> sig_bits bs = size bs.
  Proof.
    rewrite /msb /sig_bits.
    elim bs; first done.
  Admitted.

  Lemma umulo_andb_orb_all : forall bs1 bs2, size bs1 = size bs2 -> andb_orb_all (splitlsb bs1).2 (splitlsb bs2).2 = true -> size bs1 <= (sig_bits bs1) + (sig_bits bs2) -2.
  Proof.
    move => bs1 bs2 Hsz Handbb. rewrite /Umulo. have Hszslsb : (size (splitlsb bs1).2  = size (splitlsb bs2).2) by rewrite 2!size_splitlsb Hsz.     
    move : (andb_orb_all_sig_bits Hszslsb) => Handb.

    move : (andb_orb_all_true Handbb) => [Hgt01 Hgt02].
      move : (sig_bits_cons1 (splitlsb bs1).1 Hgt01) => Hh1.
      move : (sig_bits_cons1 (splitlsb bs2).1 Hgt02) => Hh2.
      have Hbs1 : (bs1 = joinlsb (splitlsb bs1).1 (splitlsb bs1).2). rewrite joinlsb_splitlsb; first done.
      move : Hgt01. case bs1; done.
      have Hbs2 : (bs2 = joinlsb (splitlsb bs2).1 (splitlsb bs2).2). rewrite joinlsb_splitlsb; first done.
      move : Hgt02. case bs2; done. (*rewrite -addn1 in Hh1.*)
      move : (Handb Handbb). rewrite size_splitlsb {4}Hbs1 {2}Hbs2 -Hh1 -Hh2/= addSn addnS subn2/=.
      rewrite -(ltn_add2r 1) subnK.
      by rewrite addn1 ltnS.
      rewrite Hbs1. move : (sig_bits_le (joinlsb (splitlsb bs1).1 (splitlsb bs1).2)). rewrite -Hh1.
      move => Hszj.
      exact : (ltn_trans Hgt01 Hszj).
  Qed.

  Lemma andb_orb_all_sig_bits_n1 : forall bs1 bs2,
      size bs1 = size bs2 -> andb_orb_all (splitlsb bs1).2 (splitlsb bs2).2 = false-> size bs1 + 1 = (sig_bits bs1) + (sig_bits bs2) -> msb (mulB (zext 1 bs1) (zext 1 bs2)) = true .
  Proof.
    move => bs1 bs2.
    rewrite -(revK bs1)-(revK bs2). set bs1r := rev bs1. set bs2r := rev bs2.
    move : bs1r bs2r.
    elim  => [| bs1rhd bs1rtl IH]; elim  => [| bs2rhd bs2rtl IH2].
    - rewrite /=; have -> : (zext 1 [::] = zeros 1) by done. by rewrite mul0B sig_bits_nil -zeros0 andb_orb_all_0l/msb/=.
    - rewrite /=; have -> : (zext 1 [::] = zeros 1) by done. by rewrite size_rev/=.
    - by rewrite !size_rev/=.
    - move => Hszrev Handbf Hsigs.
      have Hszsplrev : size (splitlsb (rev (bs1rhd :: bs1rtl))).2  = size (splitlsb (rev (bs2rhd :: bs2rtl))).2 by rewrite !size_splitlsb Hszrev.
      move : (andb_orb_all_sig_bits_gt Hszsplrev Handbf) => Hsgspl.
      have Hmk1 : (size (rev (bs1rhd :: bs1rtl)) -1 =
                   (sig_bits (rev (bs1rhd :: bs1rtl))).-1 + (sig_bits (rev (bs2rhd :: bs2rtl))).-1).
      admit.
      have Hsgbrev1 : sig_bits (splitlsb (rev (bs1rhd :: bs1rtl))).2 = (sig_bits (rev (bs1rhd :: bs1rtl))).-1. admit.
      have Hsgbrev2 : sig_bits (splitlsb (rev (bs2rhd :: bs2rtl))).2 = (sig_bits (rev (bs2rhd :: bs2rtl))).-1. admit.
      rewrite Hsgbrev1 Hsgbrev2 -Hmk1 size_splitlsb leq_eqVlt Hmk1 in Hsgspl.
      move/orP : Hsgspl => [Heq|Hlt].
      admit. by rewrite ltnn in Hlt.
  Admitted.
      

End Lemmas.
