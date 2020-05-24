
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

  Lemma unzip1_rev (ps : seq (S * T)) : unzip1 (rev ps) = rev (unzip1 ps).
  Proof. by rewrite /unzip1 map_rev. Qed.

  Lemma unzip2_rev (ps : seq (S * T)) : unzip2 (rev ps) = rev (unzip2 ps).
  Proof. by rewrite /unzip2 map_rev. Qed.

  Lemma rev_nseq A n (x : A) : rev (nseq n x) = nseq n x.
  Proof. 
      by elim: n => [// | n IHn]; rewrite -{1}(addn1 n) copy_addn rev_cat IHn. 
  Qed.

  Lemma rev_extzip ss ts : 
    rev (extzip ss ts) = zip (nseq (size ts - size ss) sd ++ rev ss)
                             (nseq (size ss - size ts) td ++ rev ts).
  Proof. 
    rewrite extzip_zip rev_zip;
      last by rewrite !seq.size_cat !size_nseq -!maxnE maxnC.
    by rewrite !rev_cat !rev_nseq.
  Qed.

  Lemma rev_extzip_ss ss ts : 
    size ss = size ts -> rev (extzip ss ts) = extzip (rev ss) (rev ts).
  Proof. 
    move=> Hs. rewrite rev_extzip Hs subnn extzip_zip_ss //=. by rewrite !size_rev.
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

(* TODO: ltB_msb is incorrect. Fix it if needed. *)
(*
  Fixpoint ltB_msb_zip (zip : seq (bool * bool)) :=
    match zip with
    | [::] => false
    | (hd1, hd2)::tl => (~~hd1 && hd2) || (hd1 == hd2) && ltB_msb_zip tl
    end.

  (* Test if bs1 < bs2 where MSB is at the head
     (the reverse of the usual representation) *)
  Definition ltB_msb (bs1 bs2 : bits) : bool := ltB_msb_zip (extzip0 bs1 bs2).
*)

  Fixpoint ltB_rev_zip (zip : seq (bool * bool)) : bool :=
    match zip with
    | [::] => false
    | (hd1, hd2)::tl => (~~hd1 && hd2) || (hd1 == hd2) && ltB_rev_zip tl
    end.

  (* Test if bs1 < bs2 (where LSB is at the head) by reversing first
     and then applying ltB_msb. *)
  Definition ltB_rev (bs1 bs2 : bits) : bool :=
    ltB_rev_zip (rev (extzip0 bs1 bs2)).

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

  Lemma size_andB bs1 bs2 : size (andB bs1 bs2) = maxn (size bs1) (size bs2).
  Proof. rewrite /andB. rewrite size_lift. reflexivity. Qed.

  Lemma size_orB bs1 bs2 : size (orB bs1 bs2) = maxn (size bs1) (size bs2).
  Proof. rewrite /orB. rewrite size_lift. reflexivity. Qed.

  Lemma size_xorB bs1 bs2 : size (xorB bs1 bs2) = maxn (size bs1) (size bs2).
  Proof. rewrite /xorB. rewrite size_lift. reflexivity. Qed.

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

  Lemma size_negB bs : size (negB bs)%bits = size bs.
  Proof.
    elim: bs => [| b bs IH] //=. rewrite /negB /=. case b; rewrite /=.
    - by rewrite size_invB.
    - by rewrite IH.
  Qed.

  Lemma size_sbbB b bs0 bs1 : 
    size (sbbB b bs0 bs1).2 = minn (size bs0) (size bs1) .
  Proof .
    rewrite /sbbB /adcB /full_adder /= .
    dcase (full_adder_zip (~~ b) (zip bs0 (~~# bs1)%bits)) => [[c res] Hadder] => /= .
    have : res = (c, res).2 => // .
    rewrite -Hadder; case => -> .
    rewrite size_full_adder_zip size_invB // .
  Qed .

  Lemma size_ucastB bs n :
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

  Lemma size_scastB bs n :
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

  (******************** Free Region Begin ********************)

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

  Lemma ltB_to_Zpos (bs1 bs2 : bits) : ltB bs1 bs2 <-> (to_Zpos bs1 < to_Zpos bs2)%Z.
  Proof.
    rewrite ltB_to_nat !to_Zpos_nat -(Nat2Z.inj_lt). split; by move/ltP.
  Qed.

  Lemma ltB_to_Zpos_eqn (bs1 bs2 : bits) : 
    ltB bs1 bs2 = (to_Zpos bs1 <? to_Zpos bs2)%Z.
  Proof.
    case HltB : (ltB bs1 bs2); case Hltb : (to_Zpos bs1 <? to_Zpos bs2)%Z; try done.
    - apply ltB_to_Zpos, Z.ltb_lt in HltB. by rewrite -HltB -Hltb.
    - apply Z.ltb_lt, ltB_to_Zpos in Hltb. by rewrite -HltB -Hltb.
  Qed.

  (* TODO: Fix it if ltB_msb is needed *)
  (*
  Lemma ltB_msb_to_nat (bs1 bs2 : bits) : ltB_msb bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Admitted.

  Lemma ltB_msb_ltB (bs1 bs2: bits): ltB_msb bs1 bs2 = ltB bs1 bs2.
  Proof.
    rewrite ltB_msb_to_nat ltB_to_nat. reflexivity.
  Qed.

  Lemma ltB_rev_ltB_msb (bs1 bs2 : bits) : ltB_rev bs1 bs2 = ltB_msb bs1 bs2.
  Admitted.
   *)

  Lemma ltB_rev_zext bs1 bs2 :
    ltB_rev (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2) 
    = ltB_rev bs1 bs2.
  Proof.
    rewrite /ltB_rev /extzip0 2!extzip_zip /zext /zeros. 
    rewrite !size_cat -2!catA -2!copy_addn 2!size_nseq.
    rewrite -!maxnE !(maxnC (size bs1) (size bs2)) subnn !addn0. reflexivity.
  Qed.

  Lemma ltn_gtF : forall m n : nat, m < n -> (n < m) = false.
  Proof. move=> m n Hlt; by rewrite ltnNge (ltnW Hlt). Qed.

  Lemma ltB_rev_to_nat_ss (bs1 bs2 : bits) :
    size bs1 = size bs2 ->
    ltB_rev bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Proof.
    rewrite -(revK bs1) -(revK bs2). set bs1r := rev bs1; set bs2r := rev bs2.
    elim: bs1r bs2r => [| hd1 tl1 IH1] [| hd2 tl2] /=;
      [ done | by rewrite size_rev | by rewrite size_rev | idtac ].
    move/eqP. rewrite !size_rev => /eqP Hs.
    rewrite /ltB_rev /extzip0 -(rev_extzip_ss _ _ Hs) revK /=. 
    rewrite !rev_cons !to_nat_rcons. 
    move/eqP: Hs; rewrite /= eqSS => /eqP Hs.
    move: (IH1 tl2). 
    rewrite !size_rev /ltB_rev /extzip0 -(rev_extzip_ss _ _ Hs) revK => IHtl.
    rewrite (IHtl Hs). case hd1; case hd2; rewrite /= -Hs.
    - by rewrite ltn_add2r. 
    - rewrite mul1n mul0n addn0 Hs. 
      have Hlt : to_nat (rev tl2) < to_nat (rev tl1) + 2 ^ size tl2
        by apply ltn_addl; rewrite -size_rev to_nat_bounded.
      by rewrite (ltn_gtF Hlt).
    - rewrite mul0n mul1n addn0.
      have Hlt : to_nat (rev tl1) < to_nat (rev tl2) + 2 ^ size tl1
        by apply ltn_addl; rewrite -size_rev to_nat_bounded.
      by rewrite Hlt.
    - by rewrite mul0n !addn0. 
  Qed.

  Lemma ltB_rev_to_nat bs1 bs2 : ltB_rev bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Proof.
    rewrite -ltB_rev_zext. rewrite ltB_rev_to_nat_ss; last exact: size_zext_mkss.
    rewrite !to_nat_zext. reflexivity.
  Qed.
  
  Lemma ltB_rev_ltB (bs1 bs2 : bits) : ltB_rev bs1 bs2 = ltB bs1 bs2.
  Proof. rewrite ltB_rev_to_nat ltB_to_nat. reflexivity. Qed.

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

  Lemma ltBNle (bs1 bs2: bits) : size bs1 = size bs2 -> ltB bs1 bs2 = ~~ leB bs2 bs1.
  Proof.
    rewrite /leB => Hs. apply Logic.eq_sym in Hs. move: (eqB_ltB_gtB_cases_ss Hs).
    case Heq : (bs2 == bs1).
    - move/eqP: Heq => <-. by rewrite ltBnn.
    - rewrite orFb. case H21 : (bs2 <# bs1); case H12 : (bs1 <# bs2); try done.
      move: (ltB_trans H21 H12). by rewrite ltBnn.
  Qed.

  Lemma leBNlt (bs1 bs2: bits) : size bs1 = size bs2 -> leB bs1 bs2 = ~~ ltB bs2 bs1.
  Proof.
    move=> Hs; apply Logic.eq_sym in Hs. rewrite (ltBNle Hs).
    by rewrite Bool.negb_involutive.
  Qed.

  Lemma leB_to_nat (bs1 bs2 : bits) :
    size bs1 = size bs2 -> leB bs1 bs2 = (to_nat bs1 <= to_nat bs2).
  Proof.
    rewrite /leB leq_eqVlt ltB_to_nat => Hsz. by rewrite (to_nat_inj_ss Hsz).
  Qed.

  Lemma leB_to_Zpos (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> leB bs1 bs2 <-> (to_Zpos bs1 <= to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. rewrite (leB_to_nat Hsz) !to_Zpos_nat -(Nat2Z.inj_le). 
    split; by move/leP.
  Qed.

  Lemma leB_to_Zpos_eqn (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> leB bs1 bs2 = (to_Zpos bs1 <=? to_Zpos bs2)%Z.
  Proof.
    move=> Hsz.
    case HleB : (leB bs1 bs2); case Hleb : (to_Zpos bs1 <=? to_Zpos bs2)%Z; try done.
    - apply (leB_to_Zpos Hsz), Z.leb_le in HleB. by rewrite -HleB -Hleb.
    - apply Z.leb_le, (leB_to_Zpos Hsz) in Hleb. by rewrite -HleB -Hleb.
  Qed.

  Lemma gtB_to_nat_ss (bs1 bs2 : bits) :
    size bs1 = size bs2 -> gtB bs1 bs2 = (to_nat bs1 > to_nat bs2).
  Proof.
    move=> Hsz; apply Logic.eq_sym in Hsz. by rewrite /gtB ltB_to_nat_ss. 
  Qed.

  Lemma gtB_to_nat (bs1 bs2 : bits) : gtB bs1 bs2 = (to_nat bs1 > to_nat bs2).
  Proof. by rewrite /gtB ltB_to_nat. Qed.

  Lemma gtB_to_Zpos (bs1 bs2 : bits) : gtB bs1 bs2 <-> (to_Zpos bs1 > to_Zpos bs2)%Z.
  Proof.
    rewrite /gtB ltB_to_Zpos. split; [exact: Z.lt_gt | exact: Z.gt_lt].
  Qed.

  Lemma gtB_to_Zpos_eqn (bs1 bs2 : bits) : 
    gtB bs1 bs2 = (to_Zpos bs1 >? to_Zpos bs2)%Z.
  Proof. 
    by rewrite /gtB ltB_to_Zpos_eqn Z.gtb_ltb. 
  Qed.

  Lemma geB_to_nat (bs1 bs2 : bits) :
    size bs1 = size bs2 -> geB bs1 bs2 = (to_nat bs1 >= to_nat bs2).
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. rewrite /geB. exact: leB_to_nat. 
  Qed.

  Lemma geB_to_Zpos (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> geB bs1 bs2 <-> (to_Zpos bs1 >= to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. rewrite /geB (leB_to_Zpos Hsz).
    split; [exact: Z.le_ge | exact: Z.ge_le].   
  Qed.

  Lemma geB_to_Zpos_eqn (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> geB bs1 bs2 = (to_Zpos bs1 >=? to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. 
    by rewrite /geB (leB_to_Zpos_eqn Hsz) Z.geb_leb.
  Qed.

  Lemma full_adder_zip_carry_propagate bs0 bs1 :
    size bs0 = size bs1 ->
    ~~(~~(full_adder_zip true (zip bs0 bs1)).1 &&
         (full_adder_zip false (zip bs0 bs1)).1) .
  Proof .
    move : bs0 bs1; apply : seq_ind2; first done .
    move => c0 c1 cs0 cs1 Hsz .
    case c0; case c1 => /=;
      dcase (full_adder_zip true (zip cs0 cs1))
      => [[d0] tl0];
      dcase (full_adder_zip false (zip cs0 cs1))
      => [[d1] tl1];
         case d0; case d1; done .
  Qed .

  Lemma zip_cons A B c0 c1 cs0 cs1 :
    @zip A B (c0::cs0) (c1::cs1) = (c0, c1)::(zip cs0 cs1) .
  Proof .
    by rewrite {1}/zip /= -/zip .
  Qed .

  Lemma full_adder_zip_inv_carry bs0 bs1 :
    size bs0 = size bs1 ->
    (bs0 == bs1 <->
     (full_adder_zip true (zip bs0 (~~# bs1))).1 = true /\
     (full_adder_zip false (zip bs0 (~~# bs1))).1 = false) .
  Proof .
    move : bs0 bs1; apply : seq_ind2; first done .
    move => c0 c1 cs0 cs1 Hsz IH .
    case c0; case c1; rewrite eqseq_cons /=; split; try done;
      dcase (full_adder_zip false (zip cs0 (~~# cs1)))
      => [[d0] tl0] Hadder0;
      dcase (full_adder_zip true (zip cs0 (~~# cs1)))
      => [[d1] tl1] Hadder1 /= .
    - move : IH; case => IH _ Heq .
      move : (IH Heq) .
      by rewrite Hadder0 Hadder1 .
    - move : IH; case => _ IH .
      move : IH .
      by rewrite Hadder0 Hadder1 .
    - by rewrite Hadder1 /=; case => -> .
    - by rewrite Hadder0 /=; case => -> .
    - move : IH; case => IH _ Heq .
      move : (IH Heq) .
      by rewrite Hadder0 Hadder1 .
    - move : IH; case => _ IH .
      move : IH .      
      by rewrite Hadder0 Hadder1 .
  Qed .
  
  Lemma leB_joinlsb b bs0 bs1 :
    bs0 <=# bs1 -> (b::bs0) <=# (b::bs1) .
  Proof .
    case b; rewrite /leB; case /orP .
    - move => /eqP <-; apply /orP; by left .
    - rewrite /ltB /= => ->; by rewrite !Bool.orb_true_r .
    - move => /eqP <-; apply /orP; by left .
    - rewrite /ltB /= => ->; by rewrite !Bool.orb_true_r .
  Qed .
      
  Lemma leB_joinlsb1 b bs0 bs1 :
    bs0 <=# bs1 -> (b::bs0) <=# (true::bs1) .
  Proof .
    case b; rewrite /leB; case /orP .
    - move => /eqP <-; apply /orP; by left .
    - rewrite /ltB /= => ->; by rewrite !Bool.orb_true_r .
    - move => /eqP <-; apply /orP; right .
      rewrite /ltB /= .
      rewrite !Bool.andb_true_r .
      rewrite unzip1_extzip_ss; last by reflexivity .
      rewrite unzip2_extzip_ss; last by reflexivity .
      apply /orP; by left .
    - rewrite /ltB /= => ->; by rewrite !Bool.orb_true_r .
  Qed .

  Lemma ltB_joinlsb b c bs0 bs1 :
    bs0 <# bs1 -> (b::bs0) <# (c::bs1) .
  Proof .
    case b; case c; rewrite /ltB /=; move => ->;
      by apply Bool.orb_true_r .
  Qed .

  Corollary sbbB_ltB_leB (bs1 bs2: bits):
    size bs1 = size bs2 ->
    if (sbbB false bs1 bs2).1 then ltB bs1 bs2 else leB bs2 bs1.
  Proof .
    move : bs1 bs2; apply : seq_ind2; first done .
    move => c0 c1 cs0 cs1 Hsz .
    rewrite !ltB_cons -!Hsz !subnn !zext0 .
    have : (size cs0 = size (~~# cs1)) .
    { by rewrite size_invB -Hsz . }
    move => Hszinv;
      move : (full_adder_zip_carry_propagate Hszinv) => {Hszinv} .
    rewrite /sbbB /adcB /full_adder;
      dcase (full_adder_zip true (zip cs0 (~~# cs1)))
      => [[d0] tl0];
      dcase (full_adder_zip false (zip cs0 (~~# cs1)))
      => [[d1] tl1];
      case d0; case d1; try done;
      case c0; case c1 => /=; move => Hadder0 Hadder1 _;
      try (rewrite Hadder0 Hadder1 /=
        || rewrite Hadder1 Hadder0 /=
        || rewrite Hadder0 /= || rewrite Hadder1 /=);
      try (apply leB_joinlsb || apply leB_joinlsb1);
      try (move => ->; apply Bool.orb_true_r) .
    - rewrite /leB; case /orP .
      + move => /eqP Heq .
        move : (full_adder_zip_inv_carry Hsz); case => Hif _ .
        move : Hadder0 Hadder1 Hif; rewrite Heq => -> -> /= .
        move => Hif; move : (Hif (eq_refl cs0)); by case .
      + move => Hlt; apply /orP; right .
        by apply ltB_joinlsb .
    - rewrite /leB; case /orP .
      + move => /eqP ->; apply /orP; left;
          by rewrite !Bool.andb_true_r .
      + have : ((full_adder_zip false (zip cs0 (~~# cs1))).1 = false) .
        { by rewrite Hadder0 . }
      have : ((full_adder_zip true (zip cs0 (~~# cs1))).1 = true) .
        { by rewrite Hadder1 . }
        move => H0 H1 _ .
        move : (full_adder_zip_inv_carry Hsz);
          case; move => _ Hif .
        rewrite Hif; last split; done .
  Qed .

  (*---------------------------------------------------------------------------
    Properties of signed comparison
    ---------------------------------------------------------------------------*)

  (* the size-not-eq case is incorrect, try
     Eval cbv in sltB (false :: false :: true :: true :: nil) 
                      (false :: true :: nil)
                 ==
                 (to_Z (false :: false :: true :: true :: nil) 
                  <? to_Z (false :: true :: nil))%Z.
   *)
  Lemma sltB_to_Z (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> sltB bs1 bs2 <-> (to_Z bs1 < to_Z bs2)%Z.
  Proof.
    case (lastP bs1); case (lastP bs2) => {bs1 bs2}.
    - rewrite /sltB /to_Z //=.
    - move=> bs2 b2. rewrite /= size_rcons; discriminate.
    - move=> bs1 b1. rewrite /= size_rcons; discriminate.
    - move=> bs2 b2 bs1 b1. 
      rewrite !size_rcons /sltB /to_Z !splitmsb_rcons /= => /eqP. 
      rewrite eqSS => /eqP Hsz. case b1; case b2 => /=.
      + rewrite orbF ltB_to_Zpos.
        have -> : to_Zpos bs1 = (Z.pow 2 (Z.of_nat (size bs1)) - 1 - to_Zneg bs1)%Z
          by rewrite -Z.add_move_r; exact: (to_Zpos_add_to_Zneg bs1).
        have -> : to_Zpos bs2 = (Z.pow 2 (Z.of_nat (size bs2)) - 1 - to_Zneg bs2)%Z
          by rewrite -Z.add_move_r; exact: (to_Zpos_add_to_Zneg bs2).
        rewrite Hsz -Z.sub_lt_mono_l -Z.opp_lt_mono -Z.succ_lt_mono. done.
      + split; last done; move=> _.
        move: (@to_Zpos_ge0 bs2). apply Z.lt_le_trans.
        rewrite -Z.opp_0 -Z.opp_lt_mono. apply Zle_lt_succ. exact: to_Zneg_ge0.
      + split; first done.
        move=> Hlt; apply Z.lt_asymm in Hlt. case Hlt.
        move: (@to_Zpos_ge0 bs1). apply Z.lt_le_trans.
        rewrite -Z.opp_0 -Z.opp_lt_mono. apply Zle_lt_succ. exact: to_Zneg_ge0.
      + by rewrite orbF ltB_to_Zpos.
  Qed.

  Lemma sltB_to_Z_eqn (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> sltB bs1 bs2 = (to_Z bs1 <? to_Z bs2)%Z.
  Proof.
    move=> Hsz. 
    case HsltB : (sltB bs1 bs2); case Hltb : (to_Z bs1 <? to_Z bs2)%Z; try done.
    - apply (sltB_to_Z Hsz), Z.ltb_lt in HsltB. by rewrite -HsltB -Hltb.
    - apply Z.ltb_lt, (sltB_to_Z Hsz) in Hltb. by rewrite -HsltB -Hltb.
  Qed.

  Lemma sleB_to_Z (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> sleB bs1 bs2 <-> (to_Z bs1 <= to_Z bs2)%Z.
  Proof.
    move=> Hsz; rewrite /sleB; split.
    - case Hlt : (sltB bs1 bs2).
      + move=> _. apply (sltB_to_Z Hsz) in Hlt. exact: Z.lt_le_incl.
      + case Heq : (bs1 == bs2) => //= _.
        move/eqP: Heq => <-; exact: Z.le_refl.
    - move=> Hle. apply Z.le_lteq in Hle. case: Hle => [Hlt | Heq].
      + apply (sltB_to_Z Hsz) in Hlt. by rewrite Hlt orbT.
      + by rewrite (to_Z_inj_ss Hsz Heq) eqxx.
  Qed.

  Lemma sleB_to_Z_eqn (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> sleB bs1 bs2 = (to_Z bs1 <=? to_Z bs2)%Z.
  Proof.
    move=> Hsz. 
    case HsleB : (sleB bs1 bs2); case Hleb : (to_Z bs1 <=? to_Z bs2)%Z; try done.
    - apply (sleB_to_Z Hsz), Z.leb_le in HsleB. by rewrite -HsleB -Hleb.
    - apply Z.leb_le, (sleB_to_Z Hsz) in Hleb. by rewrite -HsleB -Hleb.
  Qed.

  Lemma sgtB_to_Z (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> sgtB bs1 bs2 <-> (to_Z bs1 > to_Z bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. rewrite /sgtB (sltB_to_Z Hsz).
    split; [exact: Z.lt_gt | exact: Z.gt_lt].
  Qed.

  Lemma sgtB_to_Z_eqn (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> sgtB bs1 bs2 = (to_Z bs1 >? to_Z bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. 
    by rewrite /sgtB (sltB_to_Z_eqn Hsz) Z.gtb_ltb. 
  Qed.    

  Lemma sgeB_to_Z (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> sgeB bs1 bs2 <-> (to_Z bs1 >= to_Z bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. rewrite /sgeB (sleB_to_Z Hsz).
    split; [exact: Z.le_ge | exact: Z.ge_le].
  Qed.

  Lemma sgeB_to_Z_eqn (bs1 bs2 : bits) : 
    size bs1 = size bs2 -> sgeB bs1 bs2 = (to_Z bs1 >=? to_Z bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. 
    by rewrite /sgeB (sleB_to_Z_eqn Hsz) Z.geb_leb. 
  Qed.


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

  (* duplicated with size_sarB1 and size_sarB *)
  (*
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
   *)  

  Lemma msb_sarB1 bs : msb (sarB1 bs) = msb bs.
  Proof.
    case: bs => [| b bs] //=.
    rewrite /sarB1 /= /droplsb /= /msb splitmsb_joinmsb /=. reflexivity.
  Qed.

  Lemma msb_sarB bs n : msb (sarB n bs) = msb bs.
  Proof.
    elim: n => [| n IHn] //=. rewrite msb_sarB1 IHn. reflexivity.
  Qed.

  Lemma sarB_nil n : sarB n [::] = [::].
  Proof.
    elim: n => [| n IHn] //=. by rewrite IHn.
  Qed.

  Lemma sarB1_copy n b : sarB1 (copy n b) = copy n b.
  Proof.
    case: n => [| n] //=. 
    rewrite /sarB1 copy_cons -{2}copy_rcons /msb splitmsb_rcons /= /droplsb /=.
    rewrite /joinmsb copy_rcons. reflexivity.
  Qed.

  Lemma sarB1_zeros n : sarB1 (zeros n) = zeros n.
  Proof. exact: sarB1_copy. Qed.

  Lemma sarB1_ones n : sarB1 (ones n) = ones n.
  Proof. exact: sarB1_copy. Qed.

  Lemma sarB_copy n b m : sarB m (copy n b) = copy n b.
  Proof. elim: m => [| m IHm] //=. by rewrite IHm sarB1_copy. Qed.

  Lemma sarB_zeros n m : sarB m (zeros n) = zeros n.
  Proof. exact: sarB_copy. Qed.

  Lemma sarB_ones n m : sarB m (ones n) = ones n.
  Proof. exact: sarB_copy. Qed.

  Lemma sarB_cat bs n : 
    n <= size bs -> sarB n bs = high (size bs - n) bs ++ copy n (msb bs).
  Proof.    
    elim: n => [| n IHn] Hsz /=.
    - by rewrite cats0 subn0 high_size. 
    - rewrite /sarB1 msb_sarB. rewrite IHn; last by apply ltnW. 
      rewrite /joinmsb rcons_cat copy_rcons copy_cons.
      rewrite droplsb_cat; last by rewrite size_high subn_gt0.
      rewrite -(subnSK Hsz) droplsb_high. reflexivity.
  Qed.

  Lemma sarB_size bs : sarB (size bs) bs = copy (size bs) (msb bs).
  Proof. 
    rewrite sarB_cat; last trivial. by rewrite subnn high0. 
  Qed.

  Lemma sarB_oversize bs n : size bs <= n -> sarB n bs = copy (size bs) (msb bs).
  Proof.
    move=> Hsz. rewrite -(subnK Hsz) -sarB_add sarB_size sarB_copy. reflexivity.
  Qed.


  (*---------------------------------------------------------------------------
    Properties of logic shift right
    ---------------------------------------------------------------------------*)
  
  Lemma shrB_add bs i j :
    shrB i (shrB j bs) = shrB (i + j) bs .
  Proof .
      by rewrite /shrB iter_add .
  Qed .
  
  (* duplicated with size_shrB1 and size_shrB *)
  (*
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
   *)

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

  Lemma msb_shrB1 bs : msb (shrB1 bs) = b0.
  Proof.
    case (lastP bs) => {bs} [| bs b] //=.
    rewrite /shrB1 droplsb_joinmsb.
    - by rewrite /msb splitmsb_joinmsb.
    - by rewrite size_rcons.
  Qed.

  Lemma shrB_nil n : [::] >># n = [::].
  Proof.
    elim: n => [| n IHn] //=. by rewrite IHn.
  Qed.

  Lemma shrB1_zeros n : shrB1 (zeros n) = zeros n.
  Proof.
    case: n => [| n] //=. by rewrite /shrB1 /= /droplsb /= /joinmsb zeros_rcons. 
  Qed.

  Lemma shrB_zeros n m : (zeros n) >># m = zeros n.
  Proof.
    elim: m => [| m IHm] //=. by rewrite IHm shrB1_zeros.
  Qed.

  Lemma shrB_cat bs n : 
    n <= size bs -> bs >># n = high (size bs - n) bs ++ zeros n.
  Proof.    
    elim: n => [| n IHn] Hsz /=.
    - by rewrite cats0 subn0 high_size. 
    - rewrite IHn; last by apply ltnW. 
      rewrite /shrB1 /joinmsb rcons_cat zeros_rcons.
      rewrite droplsb_cat; last by rewrite size_high subn_gt0.
      rewrite -(subnSK Hsz) droplsb_high. reflexivity.
  Qed.

  Lemma shrB_size bs : bs >># (size bs) = zeros (size bs).
  Proof. 
    rewrite shrB_cat; last trivial. by rewrite subnn high0. 
  Qed.

  Lemma shrB_oversize bs n : size bs <= n -> bs >># n = zeros (size bs).
  Proof.
    move=> Hsz. rewrite -(subnK Hsz) -shrB_add shrB_size shrB_zeros. reflexivity.
  Qed.

  Lemma high_shrB_ss bs n : high n (bs >># n) = zeros n.
  Proof.
    case/orP: (ltn_geq_total n (size bs)).
    - elim: n => [| n IHn] Hn.
      + by rewrite high0.
      + apply (ltn_trans (ltnSn n)) in Hn.
        rewrite /= /shrB1 high_droplsb; last by rewrite size_rcons size_shrB. 
        rewrite /joinmsb high_rcons (IHn Hn) zeros_rcons. reflexivity.
    - move=> Hsz. rewrite (shrB_oversize Hsz) high_zeros. reflexivity.
  Qed.

  Lemma high_shrB bs n m : n <= m -> high n (bs >># m) = zeros n.
  Proof.
    move=> Hsz. by rewrite -(high_high _ Hsz) high_shrB_ss high_zeros.
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

  (* duplicated with size_shlB1 and size_shlB *)
  (*
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
 *)

  Lemma to_nat_shlB1 : forall (p: bits), to_nat (shlB1 p) = div.modn ((to_nat p).*2) (2^size p).
  Proof. move => p. by rewrite /shlB1 to_nat_dropmsb to_nat_joinlsb size_joinlsb-subn1 addnK addn0-muln2.
  Qed.

  Lemma to_nat_shlBn:
    forall n k, k < n -> to_nat (shlB k (from_nat n 1) ) = 2 ^ k.
  Proof.
    move=> n; elim => [| k IH] /=.
    - move=> Hn. rewrite expn0 to_nat_from_nat_bounded //=.
      by rewrite -{1}(expn0 2) ltn_exp2l. 
    - move=> Hlt. rewrite to_nat_shlB1.
      have Hkn : k < n by apply (ltn_trans (ltnSn k)).
      rewrite (IH Hkn) size_shlB size_from_nat -muln2 -expnSr modn_small //=.
      rewrite ltn_exp2l; done.
  Qed.

  Lemma to_Zpos_shlB1 bs :
    to_Zpos (shlB1 bs) = ((to_Zpos bs * 2) mod (2 ^ Z.of_nat (size bs)))%Z.
  Proof.
    rewrite /shlB1 to_Zpos_dropmsb to_Zpos_joinlsb size_joinlsb. 
    by rewrite Nat2Z.inj_add /= Z.add_simpl_r Z.add_0_r. 
  Qed.

  Lemma shlB_dropmsb n (p: bits) : shlB n (dropmsb p) = dropmsb (shlB n p).
  Proof.
    elim: n p => [| n IHn] p /=; first done.
    rewrite /shlB1 (IHn p). case (p <<# n); by rewrite /dropmsb.
  Qed.

  Lemma lsb_shlB1 bs : lsb (shlB1 bs) = b0.
  Proof. by case: bs. Qed.


  Lemma shlB_nil n : [::] <<# n = [::].
  Proof.
    elim: n => [| n IHn] //=. by rewrite IHn.
  Qed.

  Lemma shlB1_zeros n : shlB1 (zeros n) = zeros n.
  Proof.
    case: n => [| n]; first done. 
    rewrite /shlB1 /joinlsb.
    have->: false :: zeros n.+1 = zeros n.+2 by trivial.
    rewrite dropmsb_zeros. reflexivity.
  Qed.

  Lemma shlB_zeros n m : (zeros n) <<# m = zeros n.
  Proof.
    elim: m => [| m IHm] //=. by rewrite IHm shlB1_zeros.
  Qed.

  Lemma shlB_cat bs n : 
    n <= size bs -> bs <<# n = zeros n ++ low (size bs - n) bs.
  Proof.    
    elim: n => [| n IHn] Hsz /=.
    - by rewrite subn0 low_size. 
    - rewrite IHn; last by apply ltnW. 
      rewrite /shlB1 /joinlsb -cat_cons.
      rewrite dropmsb_cat; last by rewrite size_low subn_gt0.
      rewrite -(subnSK Hsz) dropmsb_low. reflexivity.
  Qed.

  Lemma shlB_size bs : bs <<# (size bs) = zeros (size bs).
  Proof. 
    rewrite shlB_cat; last trivial. by rewrite subnn low0 cats0. 
  Qed.

  Lemma shlB_oversize bs n : size bs <= n -> bs <<# n = zeros (size bs).
  Proof.
    move=> Hsz. rewrite -(subnK Hsz) -shlB_add shlB_size shlB_zeros. reflexivity.
  Qed.

  Lemma low_shlB_ss bs n : low n (bs <<# n) = zeros n.
  Proof.
    case/orP: (ltn_geq_total n (size bs)).
    - elim: n => [| n IHn] Hn.
      + by rewrite low0.
      + apply (ltn_trans (ltnSn n)) in Hn.
        rewrite /= /shlB1 low_dropmsb; last by rewrite size_joinlsb size_shlB addn1. 
        rewrite /joinlsb low_cons (IHn Hn). reflexivity.    
    - move=> Hsz. rewrite (shlB_oversize Hsz) low_zeros. reflexivity.
  Qed.

  Lemma low_shlB bs n m : n <= m -> low n (bs <<# m) = zeros n.
  Proof.
    move=> Hsz. by rewrite -(low_low _ Hsz) low_shlB_ss low_zeros.
  Qed.

  Lemma shlB_shrB_cancel bs n : high n bs == zeros n -> bs <<# n >># n = bs.
  Proof.
    move=> Hzeros. case/orP: (leq_total n (size bs)) => Hsz.
    - rewrite (shlB_cat Hsz) shrB_cat; 
        last by rewrite size_cat size_zeros size_low leq_addr.
      rewrite size_cat size_zeros size_low -(addnBAC _ (leqnn n)) subnn add0n.
      rewrite high_size_cat; last by rewrite size_low.
      rewrite -(eqP Hzeros) cat_low_high; [reflexivity | by rewrite subnK]. 
    - rewrite (shlB_oversize Hsz) shrB_zeros.
      move/eqP in Hzeros. apply (f_equal (high (size bs))) in Hzeros.
      rewrite (high_high _ Hsz) high_size high_zeros in Hzeros. done.
  Qed.

  Lemma shrB_shlB_cancel bs n : low n bs == zeros n -> bs >># n <<# n = bs.
  Proof.
    move=> Hzeros. case/orP: (leq_total n (size bs)) => Hsz.
    - rewrite (shrB_cat Hsz) shlB_cat;
        last by rewrite size_cat size_zeros size_high leq_addl.
      rewrite size_cat size_zeros size_high addnK.
      rewrite low_size_cat; last by rewrite size_high.
      rewrite -(eqP Hzeros) cat_low_high; [reflexivity | by rewrite subnKC]. 
    - rewrite (shrB_oversize Hsz) shlB_zeros.
      move/eqP in Hzeros. apply (f_equal (low (size bs))) in Hzeros.
      rewrite (low_low _ Hsz) low_size low_zeros in Hzeros. done.
  Qed.


  (*---------------------------------------------------------------------------
    Properties of inversion
  ---------------------------------------------------------------------------*)

  Lemma to_nat_invB bs :
    to_nat (~~# bs) = 2 ^ (size bs) - 1 - to_nat bs.
  Proof.
    elim: bs => [// | b bs IH]. rewrite /= IH -!mul2n !mulnBr expnS muln1 subnDA.
    have Hle :  2 * to_nat bs <= 2 * 2 ^ size bs - 2.
    {
      move: (to_nat_bounded bs). 
      rewrite -{1}(prednK (exp2n_gt0 (size bs))) ltnS -subn1.
      move=> H. apply (@leq_mul 2 _ 2 _) in H; last done.
      rewrite mulnBr muln1 in H. exact: H.
    }
    rewrite (addnBA _ Hle) addnC -(subnDA 1 _ b). case b => /=.
    - rewrite addn0 addn1. reflexivity.
    - rewrite addn0 addn1 subnSK; first reflexivity. 
      rewrite mul2n. apply double_gt1. exact: exp2n_gt0. 
  Qed.

  Lemma to_Zpos_invB_full bs :
    to_Zpos (~~# bs)%bits = (2 ^ Z.of_nat (size bs) - Z.one - to_Zpos bs)%Z.
  Proof.
    rewrite to_Zpos_invB. move/Z.add_move_l: (to_Zpos_add_to_Zneg bs) => ->. 
    reflexivity.
  Qed.

  Lemma invB_low bs n :
    n <= size bs -> ~~# (low n bs) = low n (~~# bs).
  Proof. 
    move=> Hn.
    move: (@cat_low_high bs n (size bs - n) (subnKC Hn)) => Hcat.
    apply (f_equal invB) in Hcat. rewrite -size_invB in Hn. rewrite invB_cat in Hcat.
    rewrite -(@cat_low_high (~~# bs) n (size (~~# bs) - n) (subnKC Hn)) in Hcat.
    move/eqP: Hcat. 
    have Hsz : size (~~# low n bs) = size (low n (~~# bs)) 
      by rewrite size_invB 2!size_low.
    rewrite (eqseq_cat _ _ Hsz) => /andP [/eqP H _]. exact: H.
  Qed.


  (*---------------------------------------------------------------------------
    Properties of addition
    ---------------------------------------------------------------------------*)

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

  Lemma full_adder_zip_B1 : forall p n,
      (full_adder_zip true (zip p (zeros n))).2 =
      succB (unzip1 (zip p (zeros n))) .
  Proof .
    elim => [ | phd ptl IH] n .
    - by rewrite zip_nil .
    - case n => [ | ns ] /=; first done .
      case phd .
      + dcase (full_adder_zip true (zip ptl (zeros ns)))
        => [[c1] tl1] Hadder1 .
        by rewrite -[(c1, false::tl1).2]/(false::tl1)
                   -[tl1]/((c1, tl1).2) -Hadder1 IH /= .
      + dcase (full_adder_zip false (zip ptl (zeros ns)))
        => [[c1] tl1] Hadder1 .
        by rewrite -[(c1, true::tl1).2]/(true::(c1,tl1).2) -Hadder1
           full_adder_zip_B0 .
  Qed .

  Lemma addB1 bs:
    addB bs (from_nat (size bs) 1) = succB bs.
  Proof.
    elim : bs .
    - by rewrite /addB /adcB /= .
    - move => b bs IH .
      rewrite size_joinlsb addn1 .
      rewrite /from_nat /= -/from_nat -zeros_from_nat /joinlsb .
      rewrite /addB /adcB /full_adder zip_cons (lock zip) /= -(lock zip) .
      case : b => /= .
      + dcase (full_adder_zip true (zip bs (zeros (size bs))))
        => [[c1] tl1] Hadder1 .
        rewrite -[(c1, false::tl1).2]/(false::(c1, tl1).2) -Hadder1 .
        rewrite full_adder_zip_B1 unzip1_zip; first done .
        by rewrite size_zeros .
      + dcase (full_adder_zip false (zip bs (zeros (size bs))))
        => [[c1] tl1] Hadder1 .
        rewrite -[(c1, true::tl1).2]/(true::(c1, tl1).2) - Hadder1 .
        rewrite full_adder_zip_B0 unzip1_zip; first done .
        by rewrite size_zeros .
  Qed .
 
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

  Lemma addBC : commutative (addB).
  Proof.
    rewrite /commutative /addB .
    move => x y; by rewrite (adcBC false x y) .
  Qed .

  Ltac dcase_full_adder_zip c xs ys :=
    let Hc := fresh "c" in
    let Htl := fresh "tl" in
    let Hadder := fresh "Hadder" in                
    dcase (full_adder_zip c (zip xs ys)) => [[Hc] Htl] Hadder .

  Lemma full_adderA : forall x y z b c,
    ((full_adder b x (full_adder c y z).2).2 ==
     (full_adder b (full_adder c x y).2 z).2) &&
    ((full_adder b x (full_adder c y z).2).2 ==
     (full_adder c (full_adder b x y).2 z).2) .
  Proof .
    elim .
    - move => y z b c; by rewrite /full_adder !zip_nil .
    - move => x xs IH; case .
      + move => z b c; by rewrite /full_adder !zip_nil !zip_nil_r .
      + move => y ys; case .
        * move => b c; by rewrite /full_adder !zip_nil_r .
          move => z zs .
          case z; case y; case x;
          rewrite /full_adder !zip_cons (lock zip) /= -(lock zip) .

          - case; case;
              rewrite (lock zip) /= -(lock zip);
               dcase_full_adder_zip true ys zs;
               dcase_full_adder_zip true xs ys;
               rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                  -[(c0, _::tl0).2]/(_::(c0,tl0).2);
               rewrite !zip_cons (lock zip) /= -(lock zip);
               [ dcase_full_adder_zip true xs tl;
                 dcase_full_adder_zip true tl0 zs;
                 move : (IH ys zs true true) => /andP [/eqP Heq _]
               | dcase_full_adder_zip true xs tl;
                 dcase_full_adder_zip true tl0 zs;
                 move : (IH ys zs true true) => /andP [/eqP Heq _]
               | dcase_full_adder_zip true xs tl;
                 dcase_full_adder_zip true tl0 zs;
                 move : (IH ys zs true true) => /andP [/eqP Heq _]
               | dcase_full_adder_zip false xs tl;
                 dcase_full_adder_zip false tl0 zs;
                 move : (IH ys zs false true) => /andP [/eqP Heq _]
               ];
               move : Heq;
               rewrite /full_adder Hadder Hadder0; 
               rewrite -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                       Hadder1 Hadder2 /= => <-;
               apply /andP; done .
          - case; case; rewrite (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip false xs ys;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip true xs ys;
                dcase_full_adder_zip false xs ys
              | dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip false xs ys ];
              (rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                       -[(c0, _::tl0).2]/(_::(c0,tl0).2)
                       -[(c1, _::tl1).2]/(_::(c1,tl1).2)
            || rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                       -[(c0, _::tl0).2]/(_::(c0,tl0).2));
              rewrite !zip_cons (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip true tl0 zs;
                move : (IH ys zs true true) => /andP [/eqP Heq _];
                move : Heq
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip true tl0 zs;
                dcase_full_adder_zip false tl1 zs;
                move : (IH ys zs false true)
                => /andP [/eqP Heq0 /eqP Heq1];
                move : Heq0 Heq1
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip false tl0 zs;
                dcase_full_adder_zip true tl1 zs;
                move : (IH ys zs false true)
                => /andP [/eqP Heq0 /eqP Heq1];
                move : Heq0 Heq1
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip true tl0 zs;
                move : (IH ys zs false true)
                => /andP [_ /eqP Heq]; move : Heq ];
              (rewrite /full_adder Hadder Hadder0 Hadder1
                       -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                       -[(c1, tl1).2]/(tl1)
                       Hadder2 Hadder3 Hadder4 /= => <- <-
            || rewrite /full_adder Hadder Hadder0
                       -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                       Hadder1 Hadder2 /= => <-);
              apply /andP; done .
          - case; case; rewrite (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip false xs ys;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip true xs ys;
                dcase_full_adder_zip false xs ys
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip false xs ys ];
              (rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                       -[(c0, _::tl0).2]/(_::(c0,tl0).2)
                       -[(c1, _::tl1).2]/(_::(c1,tl1).2)
            || rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                       -[(c0, _::tl0).2]/(_::(c0,tl0).2));
              rewrite !zip_cons (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip true tl0 zs;
                move : (IH ys zs true true)
                => /andP [/eqP Heq _]; move : Heq
              | dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip true tl0 zs;
                dcase_full_adder_zip false tl1 zs;
                move : (IH ys zs true false)
                => /andP [/eqP Heq0 /eqP Heq1]; move : Heq0 Heq1
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip false tl0 zs;
                dcase_full_adder_zip true tl1 zs;
                move : (IH ys zs false true)
                => /andP [/eqP Heq0 /eqP Heq1]; move : Heq0 Heq1
              | dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip true tl0 zs;
                move : (IH ys zs true false)
                => /andP [/eqP Heq _]; move : Heq ];
              (rewrite /full_adder Hadder Hadder0 Hadder1
                       -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                       -[(c1, tl1).2]/(tl1) 
                       Hadder2 Hadder3 Hadder4 /= => <- <-
            || rewrite /full_adder Hadder Hadder0
                       -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                       Hadder1 Hadder2 /= => <-);
              apply /andP; done .
          - case; case; rewrite (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip false xs ys
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip false xs ys
              | dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip false xs ys
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip false xs ys ];
              rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                      -[(c0, _::tl0).2]/(_::(c0,tl0).2);
              rewrite !zip_cons (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip true tl0 zs;
                move : (IH ys zs false true)
                => /andP [_ /eqP Heq]
              | dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip true tl0 zs;
                move : (IH ys zs true false)
                => /andP [/eqP Heq _]
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip true tl0 zs;
                move : (IH ys zs false true)
                => /andP [_ /eqP Heq]
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip false tl0 zs;
                move : (IH ys zs false false)
                => /andP [/eqP Heq _] ];
              move : Heq;
              rewrite /full_adder Hadder Hadder0
                      -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                      Hadder1 Hadder2 /= => <-;
              apply /andP; done .
          - case; case; rewrite (lock zip) /= -(lock zip);          
              [ dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip true xs ys ];
              rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                      -[(c0, _::tl0).2]/(_::(c0,tl0).2);
              rewrite !zip_cons (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip true tl0 zs;
                move : (IH ys zs true true)
                => /andP [/eqP Heq _]
              | dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip false tl0 zs;
                move : (IH ys zs true false)
                => /andP [_ /eqP Heq]
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip false tl0 zs;
                move : (IH ys zs false true)
                => /andP [/eqP Heq _]
              | dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip false tl0 zs;
                move : (IH ys zs true false)
                => /andP [_ /eqP Heq] ];
              move : Heq;
              rewrite /full_adder Hadder Hadder0
                      -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                      Hadder1 Hadder2 /= => <-;
              apply /andP; done .
          - case; case; rewrite (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip false xs ys;
                dcase_full_adder_zip true xs ys
              | dcase_full_adder_zip true ys zs;
                dcase_full_adder_zip true xs ys;
                dcase_full_adder_zip false xs ys
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip false xs ys ];
              (rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                       -[(c0, _::tl0).2]/(_::(c0,tl0).2)
                       -[(c1, _::tl1).2]/(_::(c1,tl1).2)
            || rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                       -[(c0, _::tl0).2]/(_::(c0,tl0).2));
              rewrite !zip_cons (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip false tl0 zs;
                move : (IH ys zs false true)
                => /andP [/eqP Heq _]; move : Heq
              | dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip true tl0 zs;
                dcase_full_adder_zip false tl1 zs;
                move : (IH ys zs true false)
                => /andP [/eqP Heq0 /eqP Heq1]; move : Heq0 Heq1
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip false tl0 zs;
                dcase_full_adder_zip true tl1 zs;
                move : (IH ys zs false true)
                => /andP [/eqP Heq0 /eqP Heq1]; move : Heq0 Heq1
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip false tl0 zs;
                move : (IH ys zs false false)
                => /andP [/eqP Heq _]; move : Heq];
              (rewrite /full_adder Hadder Hadder0 Hadder1
                       -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                       -[(c1, tl1).2]/(tl1) 
                       Hadder2 Hadder3 Hadder4 /= => <- <-
            || rewrite /full_adder Hadder Hadder0
                       -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                       Hadder1 Hadder2 /= => <-);
              apply /andP; done .
          - case; case; rewrite (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip true xs ys;
                rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                        -[(c0, _::tl0).2]/(_::(c0,tl0).2)
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip false xs ys;
                dcase_full_adder_zip true xs ys;
                rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                        -[(c0, _::tl0).2]/(_::(c0,tl0).2)
                        -[(c1, _::tl1).2]/(_::(c1,tl1).2)
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip true xs ys;
                dcase_full_adder_zip false xs ys;
                rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                        -[(c0, _::tl0).2]/(_::(c0,tl0).2)
                        -[(c1, _::tl1).2]/(_::(c1,tl1).2)
              | dcase_full_adder_zip false ys zs;
                dcase_full_adder_zip false xs ys;
                rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                        -[(c0, _::tl0).2]/(_::(c0,tl0).2) ];
              rewrite !zip_cons (lock zip) /= -(lock zip);
              [ dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip false tl0 zs;
                move : (IH ys zs true false)
                => /andP [_ /eqP Heq]; move : Heq;
                rewrite /full_adder Hadder Hadder0
                        -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                        Hadder1 Hadder2 /= => <-
              | dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip true tl0 zs;
                dcase_full_adder_zip false tl1 zs;
                move : (IH ys zs true false)
                => /andP [/eqP Heq0 /eqP Heq1]; move : Heq0 Heq1;
                rewrite /full_adder Hadder Hadder0 Hadder1
                        -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                        -[(c1, tl1).2]/(tl1) 
                        Hadder2 Hadder3 Hadder4 /= => <- <-
              | dcase_full_adder_zip true xs tl;
                dcase_full_adder_zip false tl0 zs;
                dcase_full_adder_zip true tl1 zs;
                move : (IH ys zs true false)
                => /andP [/eqP Heq0 /eqP Heq1]; move : Heq0 Heq1;
                rewrite /full_adder Hadder Hadder0 Hadder1
                        -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                        -[(c1, tl1).2]/(tl1) 
                        Hadder2 Hadder3 Hadder4 /= => <- <-
              | dcase_full_adder_zip false xs tl;
                dcase_full_adder_zip false tl0 zs;
                move : (IH ys zs false false)
                => /andP [/eqP Heq _]; move : Heq;
                rewrite /full_adder Hadder Hadder0
                        -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                        Hadder1 Hadder2 /= => <- ];
              apply /andP; done .
          - case; case; rewrite (lock zip) /= -(lock zip);
            dcase_full_adder_zip false ys zs;
            dcase_full_adder_zip false xs ys;
            rewrite -[(c, _::tl).2]/(_::(c,tl).2)
                    -[(c0, _::tl0).2]/(_::(c0,tl0).2);
            rewrite !zip_cons (lock zip) /= -(lock zip);
            [ dcase_full_adder_zip true xs tl;
              dcase_full_adder_zip true tl0 zs;
              move : (IH ys zs true false) => /andP [/eqP Heq _]
            | dcase_full_adder_zip false xs tl;
              dcase_full_adder_zip false tl0 zs;
              move : (IH ys zs false false) => /andP [/eqP Heq _]
            | dcase_full_adder_zip false xs tl;
              dcase_full_adder_zip false tl0 zs;
              move : (IH ys zs false false) => /andP [/eqP Heq _]
            | dcase_full_adder_zip false xs tl;
              dcase_full_adder_zip false tl0 zs;
              move : (IH ys zs false false) => /andP [/eqP Heq _] ];
            move : Heq;
            rewrite /full_adder Hadder Hadder0
                    -[(c, tl).2]/(tl) -[(c0,tl0).2]/(tl0)
                    Hadder1 Hadder2 /= => <-;
            apply /andP; done .
  Qed .
          
  Lemma addBA : associative (@addB).
  Proof.
    rewrite /associative /addB /adcB => x y z .
    move : (@full_adderA x y z false false) => /andP [_ /eqP Heq] .
    done .
  Qed .
  
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

  Lemma to_nat_addB_zext1 p1 p2 :
    size p1 == size p2 ->
    to_nat (addB (zext 1 p1) (zext 1 p2)) == to_nat p1 + to_nat p2 .
  Proof .
    move => Hsz .
    rewrite to_nat_addB /= size_addB .
    rewrite !size_zext -(eqP Hsz) minnE .
    rewrite subKn // .
    rewrite (to_nat_zext 1 p1) (to_nat_zext 1 p2) .
    rewrite to_nat_from_nat_bounded // .
    rewrite addnS expnS mul2n addn0 /= -addnn .
    move : (to_nat_bounded p2) .
    rewrite -(ltn_add2l (2 ^ size p1)) .
    move : (to_nat_bounded p1) .
    rewrite -(ltn_add2r (to_nat p2)) .
    rewrite (eqP Hsz) .
    apply : ltn_trans .
  Qed .

  Lemma to_nat_addB_zext p1 p2 n :
    size p1 == size p2 ->
    to_nat (addB (zext n.+1 p1) (zext n.+1 p2)) == to_nat p1 + to_nat p2 .
  Proof .
    elim : n p1 p2 .
    - apply : to_nat_addB_zext1 .
    - move => n IH p1 p2 Hsz .
      rewrite !(zext_Sn (n.+1)) .
      rewrite to_nat_addB .
      rewrite to_nat_from_nat .
      rewrite (to_nat_cat (zext n.+1 p1)) (to_nat_cat (zext n.+1 p2))
              (to_nat_zeros 1) !mul0n !addn0 .
      rewrite size_addB !size_cat !size_zeros !(size_zeros 1) .
      rewrite -(eqP Hsz) minnE subKn; last by apply leqnn .
      rewrite modn_small; first by rewrite !to_nat_zext .
      move : (to_nat_bounded (zext n.+1 p2)) .
      rewrite -(ltn_add2l (2 ^ size (zext n.+1 p1))) .
      move : (to_nat_bounded (zext n.+1 p1)) .
      rewrite -(ltn_add2r (to_nat (zext n.+1 p2))) => Hlt0 Hlt1 .
      move : (ltn_trans Hlt0 Hlt1) => { Hlt0 Hlt1 } .
      rewrite !size_zext -(eqP Hsz) .
      by rewrite addn1 expnS mul2n -addnn .
  Qed .

  Lemma adcB_zext1_catB p1 p2 c :
    size p1 = size p2 ->
    (adcB c (zext 1 p1) (zext 1 p2)).2 ==
    joinmsb (adcB c p1 p2).2 (adcB c p1 p2).1 .
  Proof .
    move => Hsz .
    move : p1 p2 Hsz c .
    apply : seq_ind2 .
    - case; by rewrite /zext /carry_addB /addB /= .
    - move => q0 q1 p0 p1 Hsz Heq c .
      rewrite /addB /carry_addB /adcB /full_adder /= .
      case c; case q0; case q1;
        rewrite /= -{1}(zext0 p0) -{1}(zext0 p1) -!zext_Sn;
        [
          dcase (full_adder_zip true (zip (zext 1 p0) (zext 1 p1)))
          => [[c0] tl0] Hzextadder /=;
          dcase (full_adder_zip true (zip p0 p1))
          => [[c1] tl1] Hadder /=
        |
          dcase (full_adder_zip true (zip (zext 1 p0) (zext 1 p1)))
          => [[c0] tl0] Hzextadder /=;
          dcase (full_adder_zip true (zip p0 p1))
          => [[c1] tl1] Hadder /=
        |
          dcase (full_adder_zip true (zip (zext 1 p0) (zext 1 p1)))
          => [[c0] tl0] Hzextadder /=;
          dcase (full_adder_zip true (zip p0 p1))
          => [[c1] tl1] Hadder /=
        |
          dcase (full_adder_zip false (zip (zext 1 p0) (zext 1 p1)))
          => [[c0] tl0] Hzextadder /=;
          dcase (full_adder_zip false (zip p0 p1))
          => [[c1] tl1] Hadder /=
        |
          dcase (full_adder_zip true (zip (zext 1 p0) (zext 1 p1)))
          => [[c0] tl0] Hzextadder /=;
          dcase (full_adder_zip true (zip p0 p1))
          => [[c1] tl1] Hadder /=
        |
          dcase (full_adder_zip false (zip (zext 1 p0) (zext 1 p1)))
          => [[c0] tl0] Hzextadder /=;
          dcase (full_adder_zip false (zip p0 p1))
          => [[c1] tl1] Hadder /=
        |
          dcase (full_adder_zip false (zip (zext 1 p0) (zext 1 p1)))
          => [[c0] tl0] Hzextadder /=;
          dcase (full_adder_zip false (zip p0 p1))
          => [[c1] tl1] Hadder /=
        |
          dcase (full_adder_zip false (zip (zext 1 p0) (zext 1 p1)))
          => [[c0] tl0] Hzextadder /=;
          dcase (full_adder_zip false (zip p0 p1))
          => [[c1] tl1] Hadder /=
        ];
        rewrite eqseq_cons /=;
        rewrite -[tl0]/((c0, tl0).2)
        -[tl1]/((c1, tl1).2) -{2}[c1]/((c1, tl1).1);
        rewrite -Hzextadder -Hadder;
        exact : Heq .    
  Qed .

  Lemma addB_zext1_catB p1 p2 :
    size p1 = size p2 ->
    addB (zext 1 p1) (zext 1 p2) ==
    joinmsb (adcB false p1 p2).2 (adcB false p1 p2).1 .
  Proof .
    by apply : adcB_zext1_catB .
  Qed .

  Lemma bit_inj (bs : bitseq) :
    size bs == 1 -> ((bs == [:: false]) + (bs == [:: true])) .
  Proof .
    case : bs .
    - done .
    - move => b bs /= .
      rewrite eqSS => Hs0 .
      move : (size0nil (eqP Hs0)) => Hbs .
      rewrite Hbs .
      case : b; [right | left]; done .
  Qed .

  Lemma zext_zeros_bit n b :
    zext n [:: b] == b :: (zeros n) .
  Proof .
    elim n .
    - by rewrite /zext /zeros /= .
    - move => k IH .
      by rewrite /zext /zeros /= .
  Qed .

  Lemma adcB_carry_bitr_zext c bs :
    adcB false (zext 1 bs) (zext (size bs) [:: c]) ==
    adcB c (zext 1 bs) (zeros (size bs + 1)) .
  Proof .
    elim bs .
    - case c; by rewrite /zext /adcB /full_adder /= .
    - move => d ds IH .
      case c; case d; rewrite /adcB /full_adder;
      rewrite !size_joinlsb !addn1 zext_cons -zeros_cons !zip_cons;
      by rewrite (lock zip) /= -(lock zip) .
  Qed .

  Lemma adcB_carry_bitr c bs :
    size bs > 0 ->
    adcB false bs (zext (size bs - 1) [:: c]) ==
    adcB c bs (zeros (size bs)) .
  Proof .
    elim : bs .
    - rewrite /size; done .
    - move => b bs IH _ .
      rewrite size_joinlsb addn1 subn1 -pred_Sn .
      rewrite (eqP (zext_zeros_bit _ _)) -zeros_cons .
      case c; case b; by rewrite /adcB /full_adder /= .
  Qed .      

  Lemma adcB_carry_succB bs0 bs1 :
    size bs0 == size bs1 ->
    (adcB true bs0 bs1).2 == succB (bs0 +# bs1) .
  Proof .
    move => /eqP Hszeq; move : bs0 bs1 Hszeq; apply seq_ind2;
      first by rewrite /addB /adcB /full_adder .
    case; case => bs0 bs1 Hszeq IH;
    rewrite /addB /adcB /full_adder !zip_cons /= .
    - dcase (full_adder_zip true (zip bs0 bs1))
      => [[c0] tl0] Hadder0 // .
    - dcase (full_adder_zip true (zip bs0 bs1))
      => [[c0] tl0] Hadder0 .
      dcase (full_adder_zip false (zip bs0 bs1))
      => [[c1] tl1] Hadder1 .
      move : IH .
      rewrite /adcB /addB /full_adder
              -[tl0]/((c0,tl0).2) -Hadder0
              -[tl1]/((c1,tl1).2) -Hadder1
      => /eqP -> // .
    - dcase (full_adder_zip true (zip bs0 bs1))
      => [[c0] tl0] Hadder0 .
      dcase (full_adder_zip false (zip bs0 bs1))
      => [[c1] tl1] Hadder1 .
      move : IH .
      rewrite /adcB /addB /full_adder
              -[tl0]/((c0,tl0).2) -Hadder0
              -[tl1]/((c1,tl1).2) -Hadder1
      => /eqP -> // .
    - dcase (full_adder_zip false (zip bs0 bs1))
      => [[c0] tl0] Hadder0 // .
  Qed .

  Lemma addB_addB_zext_adcB c bs0 bs1 :
    size bs0 == size bs1 ->
    addB (addB (zext 1 bs0) (zext 1 bs1)) (zext (size bs0) [:: c]) ==
    (adcB c (zext 1 bs0) (zext 1 bs1)).2 .
  Proof .
    move => /eqP Hszeq .
    case c .
    - have : (zext (size bs0) [:: true] ==
             (size (zext 1 bs0 +# zext 1 bs1)) -bits of (1)) .
      { rewrite size_addB !size_zext -Hszeq minnE subKn;
          last by apply leqnn .
        by rewrite addn1 /from_nat /= -/from_nat
                   zext_cons /joinlsb from_natn0 zext_nil . }
      case => /eqP -> .
      rewrite addB1 (eqP (@adcB_carry_succB _ _ _)) // .
      by rewrite !size_zext -Hszeq .
    - rewrite zext_cons zext_nil zeros_cons .
      rewrite addB0 unzip1_zip /addB // .
      rewrite size_adcB size_zeros !size_zext -Hszeq minnE subKn;
        last by apply leqnn .
      by rewrite addn1 ltnSn .
  Qed .

  Lemma addB_addB_adcB c bs0 bs1 :
    size bs0 == size bs1 ->
    addB (addB (zext 1 bs0) (zext 1 bs1)) (zext (size bs0) [:: c]) ==
    joinmsb (adcB c bs0 bs1).2 (adcB c bs0 bs1).1 .
  Proof .
    move => Hss .
    rewrite (eqP (@addB_addB_zext_adcB c bs0 bs1 Hss)) .
    apply : adcB_zext1_catB (eqP Hss) .
  Qed .

  Lemma addB_zext1_high1 bs1 bs2 :
    size bs1 = size bs2 ->
    high 1 (zext 1 bs1 +# zext 1 bs2)%bits =
    (1) -bits of bool (carry_addB bs1 bs2)%bits.
  Proof.
    move=> Hs. move: (addB_zext1_catB Hs) => Hext. rewrite (eqP Hext).
    rewrite (high1_joinmsb (adcB false bs1 bs2).1 (adcB false bs1 bs2).2).
    rewrite /carry_addB. by case: ((adcB false bs1 bs2).1).
  Qed.

  Lemma addB_zext1_lown bs1 bs2 :
    size bs1 = size bs2 ->
    low (size bs1) (zext 1 bs1 +# zext 1 bs2)%bits = (bs1 +# bs2)%bits.
  Proof.
    move=> Hs. move: (addB_zext1_catB Hs) => Hext. rewrite (eqP Hext).
    move: (low_joinmsb (adcB false bs1 bs2).1 (adcB false bs1 bs2).2).
    rewrite size_adcB -Hs minnE subKn; last apply leqnn. by apply.
  Qed.

  Lemma adcB_zext1_high1 bs1 bs2 b :
    size bs1 = size bs2 ->
    high 1 (zext 1 bs1 +# zext 1 bs2 +# zext (size bs1) [:: b])%bits =
    (1) -bits of bool ((adcB (to_bool [:: b]) bs1 bs2).1)%bits.
  Proof.
    move/eqP=> Hs. rewrite (eqP (addB_addB_adcB b Hs)).
    rewrite high1_joinmsb. rewrite to_bool_bit.
      by case: ((adcB b bs1 bs2).1).
  Qed.

  Lemma adcB_zext1_lown bs1 bs2 b :
    size bs1 = size bs2 ->
    low (size bs1) (zext 1 bs1 +# zext 1 bs2 +# zext (size bs1) [:: b])%bits =
    (adcB (to_bool [:: b]) bs1 bs2).2.
  Proof.
    move/eqP=> Hs. rewrite (eqP (addB_addB_adcB b Hs)).
    have : (size bs1 = size (adcB b bs1 bs2).2).
    { by rewrite size_adcB -(eqP Hs) minnE subKn. }
    move=> ->. rewrite low_joinmsb. rewrite to_bool_bit. reflexivity.
  Qed.

  Lemma low_adcB n ps qs :
    n <= size ps -> n <= size qs ->
    forall b,
      low n (adcB b ps qs).2 = (adcB b (low n ps) (low n qs)).2  .
  Proof .
    elim : n ps qs => [ ps qs _ _ b | n IH ps qs ]; first by rewrite !low0 /addB .
    case : ps => [ | p ps ]; first by trivial .
    rewrite size_joinlsb addn1 ltnS => Hnps .
    case : qs => [ | q qs ]; first by trivial .
    rewrite size_joinlsb addn1 ltnS => Hnqs .
    rewrite !low_cons .
    move : (IH _ _ Hnps Hnqs) => {IH} IH b .
    move : IH; case b; case p; case q;
      rewrite /addB /adcB /full_adder /= => IH;
      move : (IH true) (IH false);
      dcase (full_adder_zip true (zip ps qs))
      => [[c0] tl0] Hadder0;
      dcase (full_adder_zip true (zip (low n ps) (low n qs)))
      => [[c1] tl1] Hadder1;
      dcase (full_adder_zip false (zip ps qs))
      => [[c2] tl2] Hadder2;
      dcase (full_adder_zip false (zip (low n ps) (low n qs)))
      => [[c3] tl3] Hadder3 /=;
      rewrite low_cons;
      try (by move => -> _ || by move => _ ->) .
  Qed .
      
  Lemma low_addB n ps qs :
    n <= size ps -> n <= size qs ->
    low n (ps +# qs) = (low n ps) +# (low n qs) .
  Proof .
    move => Hnps Hnqs .
    rewrite /addB .
    by rewrite (low_adcB Hnps Hnqs) .
  Qed .

  Lemma adcB_addB_addB bs1 bs2 c :
    0 < size bs1 -> size bs1 = size bs2 ->
    (adcB c bs1 bs2).2 = bs1 +# bs2 +# zext (size bs1 - 1) [:: c].
  Proof.
    move=> Hsz0 Hsz. have{1}<-: to_bool [::c] = c by case c.    
    rewrite -(adcB_zext1_lown _ Hsz). 
    have H1 : size bs1 <= size (zext 1 bs1 +# zext 1 bs2)
      by rewrite size_addB 2!size_zext Hsz minnn addn1 leqnSn.
    have H2 : size bs1 <= size (zext (size bs1) [:: c])
      by rewrite size_zext /= addnC addn1 leqnSn.
    rewrite (low_addB H1 H2) low_addB ?size_zext ?addn1 ?Hsz ?leqnSn //=.
    rewrite -{1}Hsz 2!low_zext. rewrite Hsz in Hsz0.
    rewrite -{2}(prednK Hsz0) zext_Sn subn1 low_size_cat; first reflexivity. 
    by rewrite size_zext /= addnC addn1 (prednK Hsz0).
  Qed.


  Lemma to_nat_adcB_full bs1 bs2 c :
    size bs1 = size bs2 -> 
    to_nat (adcB c bs1 bs2).2 + (adcB c bs1 bs2).1 * 2 ^ size bs1
    = c + to_nat bs1 + to_nat bs2.
  Proof.
    move/eqP=> Hsz. 
    have->: to_nat (adcB c bs1 bs2).2 + (adcB c bs1 bs2).1 * 2 ^ size bs1
            = to_nat (joinmsb (adcB c bs1 bs2).2 (adcB c bs1 bs2).1)
      by rewrite to_nat_joinmsb size_adcB (eqP Hsz) minnn addnC. 
    rewrite -(eqP (addB_addB_adcB _ Hsz)) (eqP (addB_addB_zext_adcB _ Hsz)).
    rewrite to_nat_adcB 2!to_nat_zext to_nat_from_nat_bounded; first reflexivity. 
    rewrite size_adcB 2!size_zext (eqP Hsz) minnn.
    move: (leq_b1 c) (to_nat_bounded bs1) (to_nat_bounded bs2).
    rewrite -(prednK (exp2n_gt0 (size bs1))) -(prednK (exp2n_gt0 (size bs2))) !ltnS.
    move=> Hc Hbs1 Hbs2. move: (leq_add (leq_add Hc Hbs1) Hbs2). 
    rewrite -subn1 subnKC; last exact: exp2n_gt0. rewrite (eqP Hsz). 
    rewrite -(prednK (exp2n_gt0 (size bs2 + 1))) ltnS addn1 expnS mul2n -addnn. 
    rewrite -subn1 (addnBA _ (exp2n_gt0 (size bs2))) subn1. done.
  Qed.

  Lemma to_Zpos_adcB bs1 bs2 c :
    size bs1 = size bs2 -> 
    (to_Zpos (adcB c bs1 bs2).2 + (adcB c bs1 bs2).1 * 2 ^ Z.of_nat (size bs1))%Z
    = (c + to_Zpos bs1 + to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. move: (to_nat_adcB_full c Hsz) => Hnat. 
    apply (f_equal Z.of_nat) in Hnat. move: Hnat.
    rewrite !Nat2Z.inj_add Nat2Z.inj_mul Nat2Z_inj_expn. rewrite -!to_Zpos_nat /=.
    have->: Z.of_nat c = c by case c.
    have->: Z.of_nat (adcB c bs1 bs2).1 = (adcB c bs1 bs2).1 
      by case (adcB c bs1 bs2).1.
    done.
  Qed.    

  Lemma to_Zpos_addB bs1 bs2 :
    size bs1 = size bs2 -> 
    (to_Zpos (bs1 +# bs2)%bits + (carry_addB bs1 bs2) * 2 ^ Z.of_nat (size bs1))%Z
    = (to_Zpos bs1 + to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. rewrite /addB /carry_addB (to_Zpos_adcB _ Hsz). reflexivity.
  Qed.

  Lemma full_adder_zip_cat ps0 ps1 b0 b1 c :
    size ps0 = size ps1 ->
    full_adder_zip c ((zip ps0 ps1) ++ zip [:: b0] [:: b1]) ==
    ((bool_adder (full_adder_zip c (zip ps0 ps1)).1 b0 b1).1,
     joinmsb (full_adder_zip c (zip ps0 ps1)).2
           (bool_adder (full_adder_zip c (zip ps0 ps1)).1 b0 b1).2) .
  Proof .
    move => Hszeq .
    move : ps0 ps1 Hszeq c; apply : seq_ind2;
      first by case; case b0; case b1.
    move => p0 p1 ps0 ps1 Hszeq .
    case b0; case b1 => /= IH; case p0; case p1; case => /=;
      rewrite !(eqP (IH _));
      try (by dcase_full_adder_zip false ps0 ps1 => /=);
      try (by dcase_full_adder_zip true ps0 ps1 => /=) .
  Qed .

  Lemma carry_addB_eq_msbs bs1 bs2 :
    size bs1 = size bs2 ->
    carry_addB bs1 bs2 = (msb bs1 && ~~ msb bs2 && ~~ msb (bs1 +# bs2))
                         || (~~ msb bs1 && msb bs2 && ~~ msb (bs1 +# bs2))
                         || (msb bs1 && msb bs2).
  Proof.
    case: (lastP bs1) => {bs1} [|bs1 b1]; case: (lastP bs2) => {bs2} [|bs2 b2];
    rewrite ?size_rcons //=.
    rewrite /carry_addB /addB /adcB /full_adder =>/eqP Hsz. rewrite eqSS in Hsz. 
    rewrite (zip_rcons _ _ (eqP Hsz)) -cats1.
    have->: [:: (b1, b2)] = zip [:: b1] [:: b2] by reflexivity. 
    rewrite (eqP (full_adder_zip_cat _ _ _ (eqP Hsz))) /=.
    rewrite /msb splitmsb_joinmsb !splitmsb_rcons /=.
    by case b1; case b2; case (full_adder_zip false (zip bs1 bs2)).1.
  Qed.

  Lemma adcB_fst_sbbB bs1 bs2 b :
    (adcB b bs1 bs2).1 = ~~ (sbbB (~~ b) bs1 (~~# bs2)).1 .
  Proof.
    rewrite /sbbB Bool.negb_involutive invB_involutive.
    case (adcB b bs1 bs2) => [c res]. by rewrite /= Bool.negb_involutive.
  Qed.

  Lemma adcB_snd_sbbB bs1 bs2 b :
    (adcB b bs1 bs2).2 = (sbbB (~~ b) bs1 (~~# bs2)).2 .
  Proof.
    rewrite /sbbB Bool.negb_involutive invB_involutive.
    by case (adcB b bs1 bs2). 
  Qed.


  (*---------------------------------------------------------------------------
    Properties of subtraction
  ---------------------------------------------------------------------------*)

  Lemma succB0 bs : succB (b0 :: bs) == b1 :: bs .
  Proof .
    by rewrite /succB .
  Qed .

  Lemma succB1 bs : succB (b1 :: bs) == b0 :: (succB bs) .
  Proof .
    by rewrite /succB .
  Qed .

  Lemma full_adder_zip_succB bs0 bs1 :
    size bs0 == size bs1 ->
    (full_adder_zip false (zip bs0 (succB (~~# bs1)))).2 ==
    (full_adder_zip  true (zip bs0 (~~# bs1))).2 .
  Proof .
    move => /eqP Hszeq .
    move : bs0 bs1 Hszeq .
    apply : seq_ind2 .
    - by rewrite !zip_nil .
    - move => c0 c1 cs0 cs1 Hsz IH .
      case c0; case c1; rewrite invB_cons;
      [ rewrite (eqP (@succB0 _))
      | rewrite (eqP (@succB1 _))
      | rewrite (eqP (@succB0 _))
      | rewrite (eqP (@succB1 _)) ] .
    - by rewrite !zip_cons (lock zip) /= -(lock zip) .
    - rewrite !zip_cons (lock zip) /= -(lock zip) .
      dcase (full_adder_zip false (zip cs0 (succB (~~# cs1))))
      => [[d0] tl0] => Hadder0 .
      dcase (full_adder_zip true (zip cs0 (~~# cs1)))
      => [[d1] tl1] => Hadder1 .
      by rewrite -[(d0, _::tl0).2]/(_::(d0,tl0).2)
                 -[(d1, _::tl1).2]/(_::(d1,tl1).2)
                 -Hadder0 -Hadder1 -(eqP IH) .
    - by rewrite !zip_cons (lock zip) /= -(lock zip) .
    - rewrite !zip_cons (lock zip) /= -(lock zip) .
      dcase (full_adder_zip false (zip cs0 (succB (~~# cs1))))
      => [[d0] tl0] Hadder0 .
      dcase (full_adder_zip true (zip cs0 (~~# cs1)))
      => [[d1] tl1] Hadder1 .
      by rewrite -[(d0, _::tl0).2]/(_::(d0,tl0).2)
                 -[(d1, _::tl1).2]/(_::(d1,tl1).2)
                 -Hadder0 -Hadder1 -(eqP IH) .
  Qed .      
      
  Lemma subB_equiv_addB_negB (p q : bits) :
    size p == size q -> subB p q == addB p (negB q).
  Proof.
    move => /eqP Hszeq .
    move : p q Hszeq .
    apply : seq_ind2 .
    - by rewrite /subB /addB /negB /sbbB /adcB /full_adder !zip_nil_r .
    - move => p q ps qs Hsz IH .
      rewrite /subB /sbbB /addB /adcB /negB /full_adder;
        case p; case q;
        rewrite !invB_cons;
        [ rewrite (eqP (@succB0 _))
        | rewrite (eqP (@succB1 _))
        | rewrite (eqP (@succB0 _))
        | rewrite (eqP (@succB1 _)) ];
        rewrite !zip_cons (lock zip) /= -(lock zip) .
      + dcase (full_adder_zip true (zip ps (~~# qs)))
        => [[c0] res0] => Hadder0 .
        by rewrite -![(_, _::res0).2]/(_::res0) .
      + dcase (full_adder_zip true (zip ps (~~# qs)))
        => [[c0] res0] => Hadder0 .
        dcase (full_adder_zip false (zip ps (succB (~~# qs))))
        => [[c1] res1] => Hadder1 .
        rewrite -![(_,_::_).2]/(_::_)
                -[res0]/((c0, res0).2) -[res1]/((c1, res1).2)
                -Hadder0 -Hadder1 -(eqP (@full_adder_zip_succB _ _ _));
          [ done | by rewrite Hsz ] .
      + dcase (full_adder_zip false (zip ps (~~# qs)))
        => [[c0] res0] => Hadder0 .
        by rewrite -![(_, _::res0).2]/(_::res0) .
      + dcase (full_adder_zip true (zip ps (~~# qs)))
        => [[c0] res0] => Hadder0 .
        dcase (full_adder_zip false (zip ps (succB (~~# qs))))
        => [[c1] res1] => Hadder1 .
        rewrite -![(_,_::_).2]/(_::_)
                -[res0]/((c0, res0).2) -[res1]/((c1, res1).2)
                -Hadder0 -Hadder1 -(eqP (@full_adder_zip_succB _ _ _));
          [ done | by rewrite Hsz ] .
  Qed .
      
  Lemma sbbB_zext1_catB p1 p2 c :
    size p1 = size p2 ->
    (sbbB c (zext 1 p1) (zext 1 p2)).2 ==
    joinmsb (sbbB c p1 p2).2 (sbbB c p1 p2).1 .
  Proof .
    move => Hszeq .
    rewrite /sbbB .
    move : p1 p2 Hszeq; apply : seq_ind2;
      first by case c; rewrite /sbbB !zext_nil /= .
    move => p0 p1 ps0 ps1 Hszeq .
    have : (size ps0 = size (~~# ps1)) .
    { by rewrite size_invB -Hszeq . } 
    move => Hszinveq .
    rewrite !zext_cons /sbbB /=; case c; case p0; case p1;
      rewrite /adcB /full_adder /zext !invB_cat /=
              !(zip_cat _ _ Hszinveq) .
    - rewrite !(eqP (full_adder_zip_cat _ _ _ Hszinveq)) => /= /eqP -> .
      by dcase_full_adder_zip false ps0 (~~# ps1) .
    - rewrite !(eqP (full_adder_zip_cat _ _ true Hszinveq)) => /= _ .
      dcase_full_adder_zip true ps0 (~~# ps1) => /= .
      by move : Hadder; case c0 => /= .
    - rewrite !(eqP (full_adder_zip_cat _ _ _ Hszinveq)) => /= /eqP -> .
      by dcase_full_adder_zip false ps0 (~~# ps1) .
    - rewrite !(eqP (full_adder_zip_cat _ _ _ Hszinveq)) => /= /eqP -> .
      by dcase_full_adder_zip false ps0 (~~# ps1) .
    - rewrite !(eqP (full_adder_zip_cat _ _ _ Hszinveq)) => /= /eqP -> .
      by dcase_full_adder_zip true ps0 (~~# ps1) .
    - rewrite !(eqP (full_adder_zip_cat _ _ _ Hszinveq)) => /= /eqP -> .
      by dcase_full_adder_zip true ps0 (~~# ps1) .
    - rewrite !(eqP (full_adder_zip_cat _ _ false Hszinveq)) => /= _ .
      dcase_full_adder_zip false ps0 (~~# ps1) => /= .
      by move : Hadder; case c0 => /= .
    - rewrite !(eqP (full_adder_zip_cat _ _ _ Hszinveq)) => /= /eqP -> .
      by dcase_full_adder_zip true ps0 (~~# ps1) .
  Qed .

  Lemma subB_zext1_catB p1 p2 :
    size p1 = size p2 ->
    (zext 1 p1) -# (zext 1 p2) ==
    joinmsb (sbbB false p1 p2).2 (sbbB false p1 p2).1 .
  Proof .
    by apply : sbbB_zext1_catB .
  Qed .

  
  Lemma sub0B : forall m, subB (zeros (size m)) m = negB m.
  Proof.
    move => bs .
    have : (size (zeros (size bs)) == size bs) .
    { by rewrite size_zeros . }
    move => Hszeq .
    rewrite (eqP (@subB_equiv_addB_negB _ _ Hszeq)) {Hszeq} /= .
    rewrite add0B unzip2_zip // .
    by rewrite size_negB size_zeros .
  Qed .

  Lemma succB_ones_zeros n : succB (ones n) == zeros n .
  Proof .
    elim n .
    - done .
    - move => m IH .
      by rewrite -ones_cons -zeros_cons (eqP (@succB1 _)) (eqP IH) .
  Qed .      

  Lemma negB_zeros n : -# (zeros n) == zeros n .
  Proof .
    elim n .
    - done .
    - move => m IH .
      rewrite /negB -zeros_cons invB_cons.
      by rewrite (eqP (@succB1 _)) invB_zeros (eqP (@succB_ones_zeros _)) .
  Qed .
  
  Lemma negB1_ones n :
    -# (n) -bits of (1) == ones n .
  Proof .
    case : n; first done .
    move => n; by rewrite /negB /= -zeros_from_nat invB_zeros .
  Qed .

  Lemma subB0: forall m, subB m (zeros (size m)) = m .
  Proof.
    move => bs .
    have : (size bs == size (zeros (size bs))) .
    { by rewrite size_zeros . }
    move => Hszeq .
    rewrite (eqP (@subB_equiv_addB_negB _ _ Hszeq)) {Hszeq} /= .
    rewrite (eqP (@negB_zeros _)) addB0 unzip1_zip // .
    by rewrite size_zeros .
  Qed .

  Lemma subB1 bs:
    bs -# (from_nat (size bs) 1) == predB bs .
  Proof .
    elim : bs; first by rewrite /subB /sbbB /predB .
    move => b bs .
    case b .
    - rewrite {1 2}/subB {2}/predB /sbbB /adcB /full_adder /= => _ .
      dcase_full_adder_zip true bs (~~# (size bs) -bits of (0)) .
      rewrite -zeros_from_nat in Hadder .
      move : (subB0 bs) => /= .
      by rewrite /subB /sbbB /adcB /full_adder /= Hadder => <- .
    - rewrite {2}/subB /sbbB /adcB /full_adder /= => /eqP <- .
      dcase_full_adder_zip false bs (~~# (size bs) -bits of (0)) => /= .
      rewrite -zeros_from_nat invB_zeros in Hadder .
      rewrite eqseq_cons /= .
      rewrite (eqP (@subB_equiv_addB_negB _ _ _));
        last by rewrite size_from_nat .
      by rewrite (eqP (negB1_ones _)) /addB /adcB /full_adder Hadder .
  Qed .      

  Lemma sbbB_carry_predB bs0 bs1 :
    size bs0 = size bs1 ->
    (sbbB true bs0 bs1).2 == predB (bs0 -# bs1) .
  Proof .
    move : bs0 bs1; apply : seq_ind2;
      first by rewrite /sbbB /predB .
    move => c0 c1 cs0 cs1 Hszeq .
    rewrite /predB /subB /sbbB /adcB /full_adder;
      case c0; case c1 => /=;
      dcase_full_adder_zip false cs0 (~~# cs1);
      dcase_full_adder_zip true cs0 (~~# cs1);
      done .
  Qed .
  
  Lemma subB_subB_zext_sbbB c bs0 bs1 : 
   size bs0 = size bs1 ->
   zext 1 bs0 -# zext 1 bs1 -# zext (size bs0) [:: c] ==
   (sbbB c (zext 1 bs0) (zext 1 bs1)).2 .
  Proof .
    move => Hszeq .
    have : (size (zext 1 bs0) = size (zext 1 bs1)) .
    { by rewrite !size_zext -Hszeq . }
    move => Hszexteq .
    case c .
    - rewrite (eqP (sbbB_carry_predB Hszexteq)) .
      have : (zext (size bs0) [:: true] ==
             (size (zext 1 bs0 -# zext 1 bs1)) -bits of (1)) .
      { rewrite size_subB !size_zext -Hszeq minnE subKn;
          last by apply leqnn .
        by rewrite addn1 /from_nat /= -/from_nat
                   zext_cons /joinlsb from_natn0 zext_nil . }
      case => /eqP -> .
      by rewrite subB1 .
    - have : (zext (size bs0) [:: false] ==
             (size (zext 1 bs0 -# zext 1 bs1)) -bits of (0)) .
      { rewrite size_subB !size_zext -Hszeq minnE subKn;
          last by apply leqnn .
        by rewrite addn1 /from_nat /= -/from_nat
                   zext_cons /joinlsb from_natn0 zext_nil . }
      case => /eqP -> .
      by rewrite -zeros_from_nat (subB0 (zext 1 bs0 -# zext 1 bs1)) .
  Qed .
    
  Lemma subB_subB_sbbB c bs0 bs1 :
   size bs0 = size bs1 ->
   zext 1 bs0 -# zext 1 bs1 -# zext (size bs0) [:: c] ==
   joinmsb (sbbB c bs0 bs1).2 (sbbB c bs0 bs1).1 .
  Proof .
    move => Hszeq; rewrite (eqP (subB_subB_zext_sbbB _ Hszeq)) .
    by rewrite (sbbB_zext1_catB _ Hszeq) .
  Qed .
    
  Lemma ltB_borrow_subB bs1 bs2:
    size bs1 = size bs2 ->
    (ltB bs1 bs2 <-> borrow_subB bs1 bs2).
  Proof.
    move=> Hs. split.
    - apply contrapositive.
      + case: (borrow_subB bs1 bs2); rewrite /Decidable.decidable; by [left | right].
      + move => Hinv_carry.
        move /negP /eqP /eqP: Hinv_carry.
        rewrite Bool.negb_true_iff => H.
        move: (sbbB_ltB_leB Hs).
        rewrite /borrow_subB in H.
        rewrite H /=.
        move=> HleB HltB.
        apply Logic.eq_sym in Hs. rewrite (leBNlt Hs) in HleB.
        move /negP : HleB => HleB.
        rewrite HltB in HleB.
        done.
    - move=> Hcarry.
      move: (sbbB_ltB_leB Hs).
      rewrite /borrow_subB in Hcarry.
      by rewrite Hcarry.
  Qed.

  Lemma ltB_equiv_borrow_subB bs1 bs2:
    size bs1 = size bs2 ->
    ltB bs1 bs2 = borrow_subB bs1 bs2.
  Proof.
    move=> Hs. case Hlt: (ltB bs1 bs2); case Hcarry: (borrow_subB bs1 bs2); try done.
    - apply (ltB_borrow_subB Hs) in Hlt. by rewrite Hlt in Hcarry.
    - apply (ltB_borrow_subB Hs) in Hcarry. by rewrite Hcarry in Hlt.
  Qed.

  Lemma subB_zext1_high1 bs1 bs2 :
    size bs1 = size bs2 ->
    high 1 (zext 1 bs1 -# zext 1 bs2)%bits =
    (1) -bits of bool (borrow_subB bs1 bs2)%bits.
  Proof.
    move=> Hs. rewrite /borrow_subB. rewrite (eqP (subB_zext1_catB Hs)).
    rewrite high1_joinmsb. by case: ((sbbB false bs1 bs2).1).
  Qed.

  Lemma subB_zext1_lown bs1 bs2 :
    size bs1 = size bs2 ->
    low (size bs1) (zext 1 bs1 -# zext 1 bs2)%bits = (bs1 -# bs2)%bits.
  Proof.
    move=> Hs. rewrite (eqP (subB_zext1_catB Hs)).
    move: (low_joinmsb (sbbB false bs1 bs2).1 (sbbB false bs1 bs2).2).
    rewrite size_sbbB -Hs minnE subKn; last apply leqnn. by apply.
  Qed.

  Lemma sbbB_zext1_high1 bs1 bs2 b :
    size bs1 = size bs2 ->
    high 1 (zext 1 bs1 -# zext 1 bs2 -# zext (size bs1) [:: b])%bits =
    (1) -bits of bool ((sbbB (to_bool [:: b]) bs1 bs2).1)%bits.
  Proof.
    move=> Hs. rewrite (eqP (subB_subB_sbbB b Hs)).
    rewrite high1_joinmsb. rewrite to_bool_bit. by case: ((sbbB b bs1 bs2).1).
  Qed.

  Lemma sbbB_zext1_lown bs1 bs2 b :
    size bs1 = size bs2 ->
    low (size bs1) (zext 1 bs1 -# zext 1 bs2 -# zext (size bs1) [:: b])%bits =
    (sbbB (to_bool [:: b]) bs1 bs2).2.
  Proof.
    move=> Hs. rewrite (eqP (subB_subB_sbbB b Hs)).
    have ->: size bs1 = size (sbbB b bs1 bs2).2.
    { by rewrite size_sbbB -Hs minnE subKn. }
    rewrite low_joinmsb. rewrite to_bool_bit. reflexivity.
  Qed.

  (* to be removed?
  Lemma subB_is_dropmsb_adcB_invB p q :
    size p == size q -> 
    subB p q == dropmsb (adcB true p (invB q)).2 .
  Proof .
  Admitted.
   *)

  (* this is wrong *)
  Lemma to_nat_subB : forall m n, size m = size n -> to_nat (subB m n) = to_nat m - to_nat n.
  Proof.
  Admitted.

  Lemma subB_same m : subB m m = zeros (size m).
  Proof.
  Admitted.

  Lemma to_Zpos_sbbB bs1 bs2 b :
    size bs1 = size bs2 -> 
    to_Zpos (sbbB b bs1 bs2).2 
    = ((sbbB b bs1 bs2).1 * 2 ^ Z.of_nat (size bs1) 
       + to_Zpos bs1 - to_Zpos bs2 - b)%Z.
  Proof.
    move=> Hsz. rewrite /sbbB. rewrite -[in RHS]size_invB in Hsz. 
    move: (to_Zpos_adcB (~~ b) Hsz).
    case Hadc : (adcB (~~ b) bs1 (~~# bs2)) => [c sum] /=.
    rewrite to_Zpos_invB_full Hsz size_invB.
    have->: Z.one = true by reflexivity. move/Z.add_move_r=> ->. 
    case b; case c; rewrite /negb ?Z.add_0_l ?Z.mul_1_l ?Z.mul_0_l ?Z.sub_0_r; 
      by omega.
  Qed.

  Lemma to_Zpos_subB bs1 bs2 :
    size bs1 = size bs2 -> 
    to_Zpos (bs1 -# bs2) = 
    ((borrow_subB bs1 bs2) * 2 ^ Z.of_nat (size bs1) + to_Zpos bs1 - to_Zpos bs2)%Z.
  Proof.
    rewrite /borrow_subB /subB => Hsz. by rewrite (to_Zpos_sbbB _ Hsz) Z.sub_0_r.
  Qed.

  Lemma borrow_subB_eq_msbs bs1 bs2 :
    size bs1 = size bs2 ->
    borrow_subB bs1 bs2 = (msb bs1 && msb bs2 && msb (bs1 -# bs2))
                          || (~~ msb bs1 && ~~ msb bs2 && msb (bs1 -# bs2))
                          || (~~ msb bs1 && msb bs2).
  Proof.
    case: (lastP bs1) => {bs1} [|bs1 b1]; case: (lastP bs2) => {bs2} [|bs2 b2];
    rewrite ?size_rcons //=.
    rewrite /borrow_subB /subB /sbbB /adcB /full_adder =>/eqP Hsz. 
    rewrite eqSS -(size_invB bs2) in Hsz.
    rewrite invB_rcons (zip_rcons _ _ (eqP Hsz)) -cats1.
    have->: [:: (b1, ~~ b2)] = zip [:: b1] [:: ~~ b2] by reflexivity. 
    rewrite (eqP (full_adder_zip_cat _ _ _ (eqP Hsz))) /=.
    rewrite /msb splitmsb_joinmsb !splitmsb_rcons /=.
    by case b1; case b2; case (full_adder_zip true (zip bs1 (~~# bs2))).1.
  Qed.

  Lemma sbbB_fst_adcB bs1 bs2 b :
    (sbbB b bs1 bs2).1 = ~~ (adcB (~~ b) bs1 (~~# bs2)).1 .
  Proof.
    by rewrite adcB_fst_sbbB !Bool.negb_involutive invB_involutive.
  Qed.

  Lemma sbbB_snd_adcB bs1 bs2 b :
    (sbbB b bs1 bs2).2 = (adcB (~~ b) bs1 (~~# bs2)).2 .
  Proof.
    by rewrite adcB_snd_sbbB Bool.negb_involutive invB_involutive.
  Qed.

  Lemma low_sbbB n ps qs :
    n <= size ps -> n <= size qs ->
    forall b,
      low n (sbbB b ps qs).2 = (sbbB b (low n ps) (low n qs)).2  .
  Proof .
    move => Hnps Hnqs b. rewrite /sbbB (invB_low Hnqs). rewrite -size_invB in Hnqs.
    move: (low_adcB Hnps Hnqs (~~ b)). case (adcB (~~ b) ps (~~# qs)) => c res /= ->.
    by case (adcB (~~ b) (low n ps) (low n (~~# qs))).
  Qed .

  Lemma low_subB n ps qs :
    n <= size ps -> n <= size qs ->
    low n (ps -# qs) = (low n ps) -# (low n qs) .
  Proof .
    move => Hnps Hnqs .
    rewrite /subB .
    by rewrite (low_sbbB Hnps Hnqs) .
  Qed .

  Lemma sbbB_subB_subB bs1 bs2 b :
    0 < size bs1 -> size bs1 = size bs2 ->
    (sbbB b bs1 bs2).2 = bs1 -# bs2 -# zext (size bs1 - 1) [:: b].
  Proof.
    move=> Hsz0 Hsz. have{1}<-: to_bool [:: b] = b by case b.    
    rewrite -(sbbB_zext1_lown _ Hsz). 
    have H1 : size bs1 <= size (zext 1 bs1 -# zext 1 bs2)
      by rewrite size_subB 2!size_zext Hsz minnn addn1 leqnSn.
    have H2 : size bs1 <= size (zext (size bs1) [:: b])
      by rewrite size_zext /= addnC addn1 leqnSn.
    rewrite (low_subB H1 H2) low_subB ?size_zext ?addn1 ?Hsz ?leqnSn //=.
    rewrite -{1}Hsz 2!low_zext. rewrite Hsz in Hsz0.
    rewrite -{2}(prednK Hsz0) zext_Sn subn1 low_size_cat; first reflexivity. 
    by rewrite size_zext /= addnC addn1 (prednK Hsz0).
  Qed.


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

  Lemma mulB1 p n: if (n == 0) then mulB p (from_nat n 1) = zeros (size p) else mulB p (from_nat n 1) = p.
  Proof. 
    move : (full_mulB1 p n). rewrite/mulB.
    case n; rewrite/=;intros.
    -rewrite full_mulB2/low size_zeros subnn zeros0 cats0.
     have->:(take (size p) (zeros (size p)) = take (size (zeros (size p))) (zeros (size p))) by rewrite size_zeros. by rewrite take_size.
       by rewrite full_mulB2 low_zext.
  Qed.

  Lemma joinlsb_addB ps qs :
  joinlsb false (ps +# qs) = (joinlsb false ps) +# (joinlsb false qs) .
  Proof .
    rewrite /addB /adcB /full_adder /= .
    by dcase (full_adder_zip false (zip ps qs))
    => [[c0] tl0] Hadder0 .
  Qed .

  Lemma zext_joinlsb0 n qs :
    zext n (joinlsb false qs) = joinlsb false (zext n qs) .
  Proof .
    elim : n => [ | n IH ] .
    - by rewrite !zext0 .
    - by rewrite /joinlsb !zext_cons /addB /adcB /full_adder /= .
  Qed .
    
  Lemma zext_joinlsb1 n qs :
    zext n (joinlsb true qs) =
    (zext n (joinlsb false qs)) +# (zext ((size qs) + n) [::true]) .
  Proof .
    elim : n => [ | n IH ] .
    - rewrite !zext0 addn0 .
      rewrite /addB /adcB /full_adder /= .
      dcase (full_adder_zip false (zip qs (zeros (size qs))))
      => [[c0] tl0] Hadder0 /= .
      rewrite -[tl0]/((c0, tl0).2) -Hadder0 .
      rewrite full_adder_zip_B0 unzip1_zip; first by trivial .
      by rewrite size_zeros leqnn .
    - rewrite /joinlsb !zext_cons /addB /adcB /full_adder /= .
      dcase (full_adder_zip false
              (zip (zext n.+1 qs) (zext (size qs + n.+1) [::])))
      => [[c0] tl0] Hadder0 /= .
      rewrite -[tl0]/((c0, tl0).2) -Hadder0 .
      rewrite zext_nil full_adder_zip_B0 unzip1_zip; first by trivial .
      by rewrite size_zext size_zeros .
  Qed .
    
  Lemma full_mul_joinlsbC ps qs :
    full_mul ps (joinlsb false qs) = joinlsb false (full_mul ps qs) /\
    full_mul ps (joinlsb true qs) =
    joinlsb false (full_mul ps qs) +# zext (size qs).+1 ps .
  Proof .
    elim : ps => [ | p ps [IH0 IH1] ] .
    - rewrite /= add0n; split; first trivial .
      rewrite zext_nil addB0 unzip1_zip; first trivial .
      by rewrite size_joinlsb size_from_nat size_zeros addn1 leqnn .
    - case : p => /= .
      + rewrite IH0 IH1 .
        rewrite /joinlsb; split.
        * rewrite zext_cons .
          by rewrite -joinlsb_addB /joinlsb .
        * rewrite -/joinlsb !joinlsb_addB .
          rewrite (zext_joinlsb1 (size ps).+1)
                  (zext_joinlsb1 (size qs).+1) .
          rewrite !addBA 
                  -{2}(addn1 (size ps)) -{3}(addn1 (size qs))
                  !addnA (addnC (size qs) (size ps)) .
          rewrite -(addBA _ _ (zext (size ps).+1 (joinlsb false qs))) .
          rewrite (addBC _ (zext (size ps).+1 (joinlsb false qs))) .
          by rewrite (addBA _ (zext (size ps).+1 (joinlsb false qs)) _ ) .
      + rewrite IH0 IH1 .
        split; first by trivial .
        by rewrite joinlsb_addB -zext_joinlsb0 .
  Qed .

  Lemma full_mul_joinlsb ps qs :
    full_mul ps (joinlsb false qs) = full_mul (joinlsb false ps) qs /\
   (full_mul ps (joinlsb true qs) = full_mul (joinlsb false ps) qs +#
                                    zext (size qs).+1 ps) .
  Proof .
    elim : qs => /= [|q qs] .
    - rewrite -zeros0 /joinlsb zeros_cons !full_mulB0 addn0 addn1
                      zeros_cons .
      split; first done .
      rewrite -[true::zeros 0]/(from_nat 1 1) .
      rewrite (full_mulB1 _ 1) add0B unzip2_zip; first done .
      by rewrite size_zeros size_zext addn1 ltnSn .
    - move => [IH0 IH1] .
      case : q => /= .
      + rewrite !IH1 .
        move : (full_mul_joinlsbC ps (true::qs)) => [Heq0 Heq1] .
        rewrite Heq0 Heq1 => {Heq0 Heq1} .
        rewrite -!IH1; split; first by trivial .
        by rewrite size_joinlsb addn1 .
      + rewrite !IH0 .
        move : (full_mul_joinlsbC ps (false::qs)) => [Heq0 Heq1] .
        rewrite Heq0 Heq1 => {Heq0 Heq1} .
        rewrite -!IH0; split; first by trivial .
        by rewrite size_joinlsb addn1 .
  Qed .

  Lemma full_mulBC : forall p q, full_mul p q = full_mul q p.
  Proof.
    elim => [|p ps IHp] .
    - move => q; by rewrite /= -zeros0 full_mulB0 zeros_from_nat addnC .
    - elim => [| q qs] .
      + by rewrite -!zeros0 full_mulB0 addn0 /= -zeros_from_nat .
      + case p; case q => /= <- /= .
        * move : (full_mul_joinlsb ps qs) => [Heq0 Heq1] .
          rewrite Heq1 !joinlsb_addB /= .
          rewrite (zext_joinlsb1 (size ps).+1)
                  (zext_joinlsb1 (size qs).+1) .
          rewrite -{2}(addn1 (size ps)) -{3}(addn1 (size qs)) .
          by rewrite !addnA (addnC (size qs) (size ps)) !addBA 
                     -(addBA _ _ (zext (size ps).+1 (joinlsb false qs)))
                     (addBC _ (zext (size ps).+1 (joinlsb false qs)))
                     (addBA _ (zext (size ps).+1 (joinlsb false qs)) _) .
        * move : (full_mul_joinlsb ps qs) => [Heq0 Heq1] .
          by rewrite Heq0 !joinlsb_addB /= zext_joinlsb0 .
        * move : (full_mul_joinlsb ps qs) => [Heq0 Heq1] .
          by rewrite Heq1 !joinlsb_addB /= zext_joinlsb0 .
        * move : (full_mul_joinlsb ps qs) => [Heq0 Heq1] .
          by rewrite Heq0 .
  Qed .
      
  Lemma mulBC : forall (p q: bits), size p = size q -> mulB p q = mulB q p.
  Proof.
    move => p q Hsz .
    by rewrite /mulB full_mulBC Hsz .
  Qed .
  
  Lemma low_joinlsb n b bs :
    low n.+1 (joinlsb b bs) =
    joinlsb b (low n bs) .
  Proof .    
    elim : bs => [ | c cs IH ]; first done .
    by rewrite low_cons .
  Qed .    

  Lemma joinlsb0_addB bs :
    joinlsb false (bs) = (zext 1 bs) +# (zext 1 bs) .
  Proof .
    elim : bs => [ | b bs ]; first by rewrite /addB .
    rewrite !zext_cons /addB /adcB /full_adder; case b => /= .
    - dcase (full_adder_zip true (zip (zext 1 bs) (zext 1 bs)))
      => [[c0] tl0] Hadder0 /= .
      rewrite -[tl0]/((c0, tl0).2) -Hadder0 .
      move : (@addB_addB_zext_adcB true bs bs (eq_refl (size bs))) .
      case => /eqP <- .
      move : (@addB_addB_zext_adcB false bs bs (eq_refl (size bs))) .
      case => /eqP <- .
      rewrite zext_cons zext_nil zeros_cons addB0 .
      rewrite unzip1_zip;
        last by rewrite size_addB size_zeros !size_zext
                addn1 minnE subKn ltnSn .
      case => <- .
      rewrite -[joinlsb false (true::bs)]/(false::(joinlsb true bs)) .
      move : (addB0 bs (size bs)) .
      rewrite /joinlsb /addB zext_cons /adcB /full_adder zext_nil /= .
      dcase (full_adder_zip false (zip bs (zeros (size bs))))
      => [[c1] tl1] Hadder1 /= -> .
      by rewrite unzip1_zip;
        last by rewrite size_zeros leqnn .
    - dcase (full_adder_zip false (zip (zext 1 bs) (zext 1 bs)))
      => [[c0] tl0] Hadder0 /= .
      by rewrite -[false::bs]/(joinlsb false bs) => -> .
  Qed .      
      
  Lemma mulB_cons ps m :
    (false :: ps) *# ((size ps).+1) -bits of m =
    zext 1 (ps *# ((size ps).+1) -bits of m) +#
    zext 1 (ps *# ((size ps).+1) -bits of m) .
  Proof .
    rewrite {1}/mulB /= !from_nat_dhalf -/mulB .
    rewrite low_joinlsb .
    rewrite -[low (size ps) (full_mul ps ((size ps).+1 -bits of (m)))]/
            (mulB ps (from_nat (size ps).+1 m)) .
    by rewrite joinlsb0_addB .
  Qed .

  Lemma low_zext_low n m bs :
    n <= size bs ->
    low n (zext m bs) == low n bs .
  Proof .
    elim : n bs => [ bs | n IH bs ] /=; first by rewrite !low0 .
    case : bs => [ | b bs Hle ] ; first done .
    rewrite zext_cons !low_cons .
    have : (n <= size bs) .
    { move : Hle; by rewrite size_joinlsb addn1 . }
    by move => Hnlebs; move : (IH _ Hnlebs) => /eqP -> .
  Qed .

  Lemma low_from_nat i j n :
    low i (i + j) -bits of n = i -bits of n .
  Proof .
    elim : i j n => [ j n | i IH j n ];
      first by rewrite add0n low0 /= .
    by rewrite /= low_cons /joinlsb (IH j (n./2)) .
  Qed .    

  Lemma mulB_from_natSn n m ps :
    ps *# ((size ps) + n) -bits of m =
    ps *# (size ps) -bits of m .
  Proof .
    elim : ps n => [ n | p ps IH n ];
      first by rewrite /mulB !low0 .
    rewrite !size_joinlsb /mulB .
    case : p;
      rewrite (lock from_nat) /= -(lock from_nat) .
    - rewrite !low_addB;
        [ idtac
        | rewrite size_joinlsb size_full_mul size_from_nat
                  -addnA !addn1; by apply ltn_addl
        | rewrite size_zext size_from_nat addn1;
            by apply ltn_addl
        | rewrite size_joinlsb size_full_mul size_from_nat
                  -addnA !addn1;
          apply ltn_addl; apply ltn_trans with ((size ps).+1 + n);
          [ apply ltn_addr; by apply ltnSn
          | by apply ltnSn ]
        | rewrite size_zext size_from_nat;
            by apply ltn_addl
        ] .
      rewrite low_cons low_cons .
      rewrite -[low (size ps) (full_mul ps (size ps + 1 + n) -bits of m)]/(ps *# (size ps + 1 + n) -bits of m) .
      rewrite -[low (size ps) (full_mul ps (size ps + 1) -bits of m)]/(ps *# (size ps + 1) -bits of m) .
      rewrite (IH 1) .
      rewrite -{1}(addnA _ 1 n) (IH (1 + n)) .
      have : ((size ps).+1 <= size ((size ps + 1 + n) -bits of m)) .
      { by rewrite size_from_nat addn1 ltn_addr . }
      move => Hle;
        rewrite (eqP (low_zext_low (size ps).+1 Hle)) => {Hle} .
      have : ((size ps).+1 <= size ((size ps + 1) -bits of m)) .
      { by rewrite size_from_nat addn1 . }
      move => Hle;
        rewrite (eqP (low_zext_low (size ps).+1 Hle)) => {Hle} .
      rewrite addn1 low_from_nat .
      move : (low_from_nat (size ps).+1 0 m) .
      by rewrite addn0 => -> .
    - rewrite !low_cons .
      rewrite -[low (size ps) (full_mul ps (size ps + 1 + n) -bits of (m))]/(ps *# (size ps + 1 + n) -bits of m) .
      rewrite -[low (size ps) (full_mul ps (size ps + 1) -bits of (m))]/(ps *# (size ps + 1) -bits of m) .
      move : (IH (1 + n)) .
      rewrite addnA => -> .
      by rewrite (IH 1) .
  Qed .

  Lemma addB_carry_bitr c bs :
    addB bs (zext (size bs - 1) [:: c]) ==
    (adcB c bs (zeros (size bs))).2 .
  Proof .
    dcase (0 < size bs); case => Hbs .
    - rewrite /addB .
      rewrite (eqP (@adcB_carry_bitr _ _ _)); done .
    - have : (size bs == 0) .
      { by rewrite eqn0Ngt Hbs . }
      move => {Hbs} /eqP Hbs .
      rewrite (eqP (size0 Hbs)) .
      by rewrite -[0-1]/0 zext0 /addB /= .
  Qed .

  Lemma from_natn1 n :
    0 < n -> from_nat n 1 == zext (n.-1) [::true] .
  Proof .
    move => Hn .
    rewrite -{1}(prednK Hn) /= .
    by rewrite zext_cons zext_nil from_natn0 .
  Qed .    
    
  Lemma from_natSn_from_nat n m :
    from_nat n m.+1 = from_nat n m +# from_nat n 1 .
  Proof .
    elim : n m => [ m | n IH m ]; first by rewrite /addB .
    rewrite /= uphalf_half addnC .
    dcase (odd m); case => Hodd /= .
    - rewrite addn1 (IH m./2) .
      rewrite {2}/addB /adcB /full_adder /= .
      move : (addB_carry_bitr true (from_nat n m./2)) .
      rewrite /adcB /full_adder .
      rewrite size_from_nat from_natn0 subn1 .
      dcase (full_adder_zip true (zip ((n) -bits of (m./2)) (zeros n)))
      => [[c0] tl0] Hadder0 /= .
      case => /eqP <- .
      dcase (0 < n); case => Hngt0 .
      + by rewrite (eqP (@from_natn1 _ _)) .
      + move : (eqn0Ngt n); rewrite Hngt0 /= /eqP => {Hngt0} /eqP -> .
        by rewrite /addB .
    - rewrite addn0 .
      rewrite /addB /adcB /full_adder /= .
      move : (addB0 (from_nat n m./2) n) .
      rewrite /addB /adcB /full_adder from_natn0 .
      dcase (full_adder_zip false (zip (from_nat n m./2) (zeros n)))
      => [[c0] tl0] Hadder0 /= -> .
      rewrite unzip1_zip; first by trivial .
      by rewrite size_zeros size_from_nat .
  Qed .

  Lemma mulB_addSn p m : mulB p (from_nat (size p) m.+1) = addB (mulB p (from_nat (size p) m)) p .
  Proof .
    elim : p => [ | p ps IH ]; first done .
    rewrite size_joinlsb addn1 .
    have : ((size ps).+1 = size (from_nat ((size ps).+1) (m.+1))) .
    { by rewrite size_from_nat . }
    move => Hszm1 .
    have : ((size ps).+1 = size (from_nat ((size ps).+1) (m))) .
    { by rewrite size_from_nat . }
    move => Hszm .
    case : p; rewrite (lock from_nat) /mulB /= -(lock from_nat);
      [ rewrite !low_addB;
        [ idtac
        | rewrite size_joinlsb size_full_mul size_from_nat -addnA addn1;
            by apply ltn_addl
        | rewrite size_zext size_from_nat; by apply ltn_addl
        | rewrite size_joinlsb size_full_mul size_from_nat -addnA addn1;
            by apply ltn_addl
        | rewrite size_zext size_from_nat;
            by apply ltn_addl
        ];
        rewrite {3}Hszm1 {8}Hszm !low_zext
      | idtac ];
      rewrite !low_cons;
      rewrite -[low (size ps) (full_mul ps ((size ps).+1 -bits of (m.+1)))]/(ps *# (size ps).+1 -bits of (m.+1));
      rewrite -[low (size ps) (full_mul ps ((size ps).+1 -bits of (m)))]/(ps *# (size ps).+1 -bits of m);
      move : (mulB_from_natSn 1 m.+1 ps);
      rewrite addn1 => ->;
      move : (mulB_from_natSn 1 m ps);
      rewrite addn1 => ->;
      rewrite IH .
    - rewrite from_natSn_from_nat .
      have : (true :: ps = (false :: ps) +# (from_nat (size ps).+1 1)) .
      { rewrite (eqP (@from_natn1 _ _)) /=; last by apply ltn0Sn .
        rewrite zext_cons /addB /adcB /full_adder /= zext_nil .
        move : (addB0 ps (size ps)) .
        rewrite /addB /adcB /full_adder .
        dcase (full_adder_zip false (zip ps (zeros (size ps))))
        => [[c0] tl0] Hadder0 /= -> .
        rewrite unzip1_zip; first by trivial .
        by rewrite size_zeros leqnn .
      }
      move => -> .
      rewrite !addBA -(addBA _ _ (false::ps)) (addBC _ (false::ps)) addBA .
      have : (false :: ps *# (from_nat (size ps) m) +# ps =
              (false :: (ps *# (from_nat (size ps) m))) +# (false :: ps)) .
      { rewrite /addB /adcB /full_adder /= .
        by dcase (full_adder_zip false
                                 (zip (ps *# (from_nat (size ps) m)) ps))
        => [[c0] tl0] Hadder0 /= . }
      by move => -> .
    - have : (false :: ps *# (from_nat (size ps) m) +# ps =
             (false :: (ps *# (from_nat (size ps) m))) +# (false :: ps)) .
      { rewrite /addB /adcB /full_adder /= .
        by dcase (full_adder_zip false
                                 (zip (ps *# (from_nat (size ps) m)) ps))
        => [[c0] tl0] Hadder0 /= . }
      by move => -> .
  Qed .

  Lemma mulB_addn p m1 m2: mulB p (from_nat (size p) (m1 + m2)) = addB (mulB p (from_nat (size p) m1)) (mulB p (from_nat (size p) m2)). 
  Proof.
    elim : m1 => [ | n IH ] .
    - rewrite mulB0 -zeros_from_nat add0B unzip2_zip;
        last by rewrite size_mulB size_zeros leqnn .
      by rewrite add0n .
    - rewrite addSn .
      rewrite !mulB_addSn IH .
        by rewrite -!addBA (addBC p (p *# (size p) -bits of (m2))) .
  Qed .

  Lemma mulB_muln p m1 m2 : mulB p (from_nat (size p) (m1*m2)) = mulB (mulB p (from_nat (size p) m1)) (from_nat (size p) m2).
  Proof.
    have : (size p = size (p *# (from_nat (size p) m1))) .
    { by rewrite size_mulB . }
    move => Hsz .
    elim : m2 => [ | m2 ];
      first by rewrite muln0 {3}Hsz !mulB0 size_mulB .
    rewrite mulnS .
    rewrite !mulB_addn => -> .
    by rewrite {5}Hsz mulB_addSn addBC -Hsz .
  Qed .

  Lemma succB_shlB1 ps :
    succB (shlB1 ps) = dropmsb (true::ps) .
  Proof .
    elim : ps => [ | p ps IH ] /=; first done .
    by rewrite /dropmsb /= .
  Qed .
    
  Lemma mulB2 ps :
    ps *# (from_nat (size ps) 2) = shlB1 ps .
  Proof .
    elim : ps => [ | p ps IH ] .
    - by rewrite /mulB low0 /shlB1 /dropmsb /joinlsb .
    - rewrite size_joinlsb .
      case : p; rewrite addn1 /mulB /= .
      + rewrite zext_cons low_addB;
          [ idtac
          | rewrite size_joinlsb size_full_mul size_joinlsb size_from_nat
                    (addn1 (size ps));
            apply ltn_addr; apply ltn_addl; apply ltnSn
          | rewrite size_joinlsb size_zext size_from_nat;
            apply ltn_addr; apply ltn_addl; apply ltnSn ] .
        rewrite !low_cons .
        rewrite -[joinlsb false (from_nat (size ps) 1)]/(from_nat (size ps).+1 2) .
        rewrite -[low (size ps) (full_mul ps (from_nat (size ps).+1 2))]/(ps *# (from_nat (size ps).+1 2)) -{1}addn1 .
        rewrite mulB_from_natSn IH .
        rewrite -{1}(size_from_nat (size ps) 1) .
        rewrite (eqP (@low_zext_low _ _ _ _)); last by apply leqnn .
        rewrite low_size -joinlsb_addB .
        rewrite -(size_shlB1 ps) addB1 .
        rewrite {2}/shlB1 .
        by rewrite succB_shlB1 .
      + rewrite low_cons .
        rewrite -[joinlsb false (from_nat (size ps) 1)]/(from_nat (size ps).+1 2) .
        rewrite -[low (size ps) (full_mul ps (from_nat (size ps).+1 2))]/(ps *# (from_nat (size ps).+1 2)) -addn1 .
        by rewrite mulB_from_natSn IH .
  Qed .

  Lemma size_iter_shlB1 i ps :
    size (iter i shlB1 ps) = size ps .
  Proof .
    elim : i => [ | i IH ]; first done .
    by rewrite /= size_shlB1 IH .
  Qed .

  Lemma shlB_mul2exp i (p: bits) : iter i shlB1 p = mulB p (from_nat (size p) (2^i)).
  Proof.
    elim : i => [ | i IH ] .
    - rewrite /iter expn0 /= .
      move : (mulB1 p (size p)) .
      case : p => /=; first by trivial .
      by move => p ps -> .
    - rewrite expnSr .
      rewrite mulB_muln /= -IH .
      rewrite -(size_iter_shlB1 i p) .
      by rewrite mulB2 .
  Qed .

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

  (*
    Next lemma is incorrect, try :

    Eval cbv in
        let m := [:: true] in
        let n := [:: false; true] in
        (mulB m n == (zeros (size m)),
         (m == zeros (size m)) || (n == zeros (size n))) .
   *)
  (*
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
   *)
  
  Lemma mulB0' : forall m n, mulB m (zeros n) = zeros (size m).
  Proof.
    intros. rewrite/mulB full_mulB0/low -zeros_cats take_cat size_zeros/=.
    case H : (size m < size m). rewrite (ltnn (size m)) in H. discriminate.
      by rewrite size_cat size_zeros subnDA subnn take0 sub0n !cats0.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of bitwise and
    ---------------------------------------------------------------------------*)

  Lemma and1B bs : andB (ones (size bs)) bs = bs.
  Proof.
    elim : bs; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -ones_cons .
    by rewrite /andB /andb /lift0 /lift; case b => /= -> .
  Qed .
  
  Lemma and0B bs : andB (zeros (size bs)) bs = zeros (size bs).
  Proof.
    elim : bs; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -zeros_cons .
    by rewrite /andB /andb /lift0 /lift; case b => /= -> .
  Qed .

  Lemma andB_copy_case :
    forall b (bs : bits),
      andB (copy (size bs) b) bs = if b then bs else (from_nat (size bs) 0).
  Proof.
    move=> [] bs.
    - exact: and1B.
    - rewrite -/(zeros (size bs)) from_natn0. exact: and0B.
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

  Lemma andB1 bs : andB bs (ones (size bs)) = bs.
  Proof.
    elim : bs; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -ones_cons .
    by rewrite /andB /andb /lift0 /lift; case b => /= -> .
  Qed .
    
  Lemma andB0 bs : andB bs (zeros (size bs)) = zeros (size bs).
  Proof.
    elim : bs; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -zeros_cons .
    by rewrite /andB /andb /lift0 /lift; case b => /= -> .
  Qed .
  
  (*---------------------------------------------------------------------------
    Properties of bitwise or
    ---------------------------------------------------------------------------*)

  Lemma or1B: forall (bs : bits), orB (ones (size bs)) bs = ones (size bs).
  Proof. 
    elim; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -ones_cons .
    by rewrite /orB /orb /lift0 /lift; case b => /= -> .
  Qed .

  Lemma orB0: forall (bs : bits), orB bs (zeros (size bs)) = bs.
  Proof. 
    elim; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -zeros_cons .
    by rewrite /orB /orb /lift0 /lift; case b => /= -> .
  Qed .

  Lemma or0B : forall bs, orB (zeros (size bs)) bs = bs.
  Proof.
    elim; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -zeros_cons .
    by rewrite /orB /orb /lift0 /lift; case b => /= -> .
  Qed .

  (*---------------------------------------------------------------------------
    Properties of bitwise or
    ---------------------------------------------------------------------------*)

  Lemma xor0B bs : xorB (zeros (size bs)) bs = bs.
  Proof.
    elim : bs; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -zeros_cons .
    by rewrite /xorB /xorb /lift0 /lift; case b => /= -> .
  Qed .

  Lemma xor1B bs :
    xorB (ones (size bs)) bs = invB bs.
  Proof.
    elim : bs; first done .
    move => b bs .
    rewrite size_joinlsb addn1 -ones_cons .
    by rewrite /xorB /xorb /lift0 /lift; case b => /= -> .
  Qed .
  
  Lemma xorB_copy_case : forall b bs,
      xorB (copy (size bs) b) bs = if b then (invB bs) else bs.
  Proof.
    move => [] bs.
    - by rewrite xor1B.
    - by rewrite xor0B. 
  Qed.

  Lemma xorBC: commutative (xorB).
  Proof.
    intro. rewrite/xorB. 
    elim x => [|xhd xtl IH] /=; elim => [|yhd ytl IHm] /=.
    - done.
    - rewrite /xorB /lift0 lift0n. rewrite liftn0; first done.
      intro; by rewrite Bool.xorb_false_r.
      rewrite /left_id. intros; by rewrite Bool.xorb_false_l.
    - rewrite /xorB /lift0 liftn0. rewrite lift0n; first done.
      intro; by rewrite Bool.xorb_false_l.
      rewrite /right_id. intros; by rewrite Bool.xorb_false_r.
    - by rewrite /lift0 lift_cons liftE -/lift0 (IH ytl) Bool.xorb_comm. 
  Qed.

  (*---------------------------------------------------------------------------
    Properties of signed extend 
  ---------------------------------------------------------------------------*)
  
  Lemma addB_addB_sext_adcB c bs0 bs1 :
    size bs0 == size bs1 ->
    addB (addB (sext 1 bs0) (sext 1 bs1)) (zext (size bs0) [:: c]) ==
    (adcB c (sext 1 bs0) (sext 1 bs1)).2 .
  Proof .
    move => /eqP Hszeq .
    case c .
    - have : (zext (size bs0) [:: true] ==
             (size (sext 1 bs0 +# sext 1 bs1)) -bits of (1)) .
      { rewrite size_addB !size_sext -Hszeq minnE subKn;
          last by apply leqnn .
        by rewrite addn1 /from_nat /= -/from_nat
                   zext_cons /joinlsb from_natn0 zext_nil . }
      case => /eqP -> .
      rewrite addB1 (eqP (@adcB_carry_succB _ _ _)) // .
      by rewrite !size_sext -Hszeq .
    - rewrite zext_cons zext_nil zeros_cons .
      rewrite addB0 unzip1_zip /addB // .
      rewrite size_adcB size_zeros !size_sext -Hszeq minnE subKn;
        last by apply leqnn .
      by rewrite addn1 ltnSn .
  Qed .

  (* The following statement is false. Try
     Eval cbv in ((adcB true (sext 1 [::b0]) (sext 1 [::b1])).2) .
     Eval cbv in (joinmsb (adcB true [::b0] [::b1]).2
                          (adcB true [::b0] [::b1]).1) .

  Lemma adcB_sext1_catB p1 p2 c :
    size p1 == size p2 ->
    (adcB c (sext 1 p1) (sext 1 p2)).2 ==
    joinmsb (adcB c p1 p2).2 (adcB c p1 p2).1 .
   *)

  (*
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
   *)

  (* the next lemma is incorrect, try:

    Eval cbv in
        let bs0 := [::true; false] in
        let bs1 := [::false; true] in
        (full_mul bs0 bs1, sext (size bs0) bs0 *# sext (size bs0) bs1) .
   *)
  
  Lemma mul_sext bs0 bs1 :
    full_mul bs0 bs1 ==
    ((sext (size bs0) bs0) *# (sext (size bs0) bs1))%bits .
  Admitted .


  (******************** Free Region End ********************)
  

  
  (*---------------------------------------------------------------------------
    Properties of unsigned division
  ---------------------------------------------------------------------------*)
  Fixpoint udivB_rec (n m : bits) (q r : bits): bits * bits :=
    match n with
    | [::] => (q, r)
    | nhd :: ntl => let di := dropmsb (joinlsb nhd r) in
                    let bi := negb (ltn (to_nat di) (to_nat m)) in
                    let ri := if bi then subB di m else di in
                    let qi := dropmsb (joinlsb bi q) in
                    udivB_rec ntl m qi ri
    end.

  Definition udivB (n' m : bits) : bits * bits :=
    let n := rev n' in
    if ((from_nat (size n) (to_nat m)) == zeros (size n)) then (zeros (size n), n')
    else udivB_rec n (from_nat (size n) (to_nat m)) (zeros (size n)) (zeros (size n)).

  Lemma size_uremB_rec : forall  n m q r, size m = size r -> size (udivB_rec n m q r).2 = size r.
  Proof.
    elim =>[|nhd ntl IH]m q r Hsz; first done.
    rewrite/=(IH m (dropmsb (joinlsb (~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)) q))
                 (if ~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)
                  then (dropmsb (joinlsb nhd r) -# m)%bits
                  else dropmsb (joinlsb nhd r)));
      case H : ((to_nat (dropmsb (joinlsb nhd r)) < to_nat m)); try (by rewrite/=size_dropmsb size_joinlsb addnK|| by rewrite/=size_subB size_dropmsb size_joinlsb addnK Hsz minnn).
  Qed.    

  Lemma size_uremB : forall n m , size (udivB n m).2 = size n.
  Proof.
    rewrite/udivB. intros.
    case Hm0: ((size (rev n)) -bits of (to_nat m)%bits == zeros (size (rev n))); first done. 
    rewrite size_rev size_uremB_rec; rewrite size_zeros; first done. by rewrite size_from_nat.
  Qed.  

  Lemma size_udivB_rec n m q r : size (udivB_rec n m q r).1 = size q.
  Proof.
    move : m q r.  elim n => [|nhd ntl IH]m q r/=; first done. 
    rewrite (IH m (dropmsb (joinlsb (~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)) q))
                (if ~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)
                 then (dropmsb (joinlsb nhd r) -# m)%bits
                 else dropmsb (joinlsb nhd r))).
      by rewrite size_dropmsb size_joinlsb addnK.
  Qed.  

  Lemma size_udivB n m : size (udivB n m).1 = (size n).
  Proof.
    rewrite/udivB. intros.
    case Hm0: ((size (rev n)) -bits of (to_nat m)%bits == zeros (size (rev n)));
                first by rewrite size_rev size_zeros.
    by rewrite size_rev size_udivB_rec size_zeros.
  Qed.

  
  Lemma neq_zeros_to_nat_gt0 : forall bs, ~~(bs == zeros (size bs)) -> 0 < to_nat bs.
  Proof.
    elim . done.
    move => hd tl Hnot0 . rewrite/= eqseq_cons negb_and. move/orP => [Hhd | Htl].
    - rewrite eqbF_neg Bool.negb_involutive in Hhd. by rewrite Hhd.
    - move : (Hnot0 Htl). rewrite -muln2.
      case hd. by rewrite addnC addn1 ltn0Sn.
      by rewrite -(ltn_pmul2r (ltn0Sn 1)) mul0n add0n.
  Qed.

    
  Lemma neq_zero_size_gt0 : forall m , ~~(m==zeros(size m)) -> 0 < size m.
  Proof.
    elim; done. 
  Qed.
  

  Lemma to_nat_belast_0 : forall s, to_nat (belast false (zeros s)) = 0.
  Proof.
    elim => [|ns IH]/=; first done. rewrite IH-muln2 mul0n; done.
  Qed.


  Lemma joinlsb_isb0 (mhd:bool) r: 0 < size r -> to_nat (dropmsb (joinlsb mhd r)) = 0 -> mhd = b0.
  Proof.
    case Hmhd : mhd; last done. move => Hgt0.
    rewrite to_nat_dropmsb to_nat_joinlsb size_joinlsb addn1/=. 
    move : (odd_exp 2 (size r)). have {2}->: 2 = 1.*2 by done. rewrite odd_double orbF.
    rewrite lt0n in Hgt0. rewrite (negbTE Hgt0). move => Hoddf.
    move :(odd_mod ((to_nat r).*2 + 1) Hoddf). rewrite odd_add odd_double /=.
    move => Hoddt Htonat0. by rewrite Htonat0 in Hoddt. 
  Qed.

  Lemma from_natSn1 n :
    from_nat n.+1 1 == zext n [::true] .
  Proof .
    case : n; first done .
    move => n .
    by rewrite /from_nat /= -/from_nat from_natn0
               joinlsb_false_zeros zext_zeros_bit .
  Qed.

  Lemma dropmsb_cons n b bs :
    size bs = n.+1 ->
    dropmsb (b::bs) == b::(dropmsb bs) .
  Proof .
    case bs; first done .
    move => c cs Hsz .
    by rewrite {1}/dropmsb /splitmsb /split_last /= .
  Qed .
    
  Lemma subB_joinmsb_dropmsb: forall b q n, size q = n.+1 -> (dropmsb (joinlsb b q) -# joinlsb b (zeros n))%bits = dropmsb (joinlsb false q).
  Proof.
    move => b q n Hsz .
    have : (size (dropmsb q) = n) .
    { by rewrite size_dropmsb Hsz subn1 . } 
    rewrite /joinlsb !(eqP (@dropmsb_cons _ _ _ Hsz)) .
    rewrite /subB /sbbB /adcB /full_adder; case b => /= Hszdrop;
      dcase (full_adder_zip true (zip (dropmsb q) (~~# zeros n)))
      => [[c] tl] Hadder /=;
      move : (subB0 (dropmsb q));
      by rewrite Hszdrop /subB /sbbB /adcB /full_adder /= Hadder /= => -> .
  Qed .

      
  Lemma to_nat_shlBnm : forall n m , to_nat (shlB n m) = if (n==0) then (to_nat m) else modn (to_nat m * (2^ n)) (2^ size m).
  Proof.
    elim => [|ns IH] m. done.
    rewrite/= to_nat_shlB1.
    rewrite {1}(IH m).
    case Hns: (ns == 0). by rewrite size_shlB -muln2 (eqP Hns) expn1.
    by rewrite size_shlB -muln2 expnSr mulnA modnMml.
  Qed.

  Lemma shlB1_shlB : forall bs n, shlB1 (shlB n bs) = shlB n (shlB1 bs).
  Proof.
  Admitted.

  Lemma low_dropmsb : forall bs , low (size bs).-1 bs = dropmsb bs.
  Proof.
    elim => [|bhd btl IH]. done.
    rewrite /=/low (lock take) (lock dropmsb)/=subnS subnn -subn1 sub0n cats0 -!lock.
    apply/eqP; rewrite -to_nat_inj_ss. rewrite to_nat_take ltnSn to_nat_dropmsb /= to_nat_from_nat.
    apply/eqP. done.
    by rewrite size_take ltnSn size_dropmsb/= -addn1 addnK.
  Qed.

  Lemma low_dropmsb_joinlsb : forall bs b, 0 < size bs -> b::low (size bs).-1 bs = dropmsb (joinlsb b bs).
  Proof.
    elim => [|bhd btl IH] b. done.
    move => Hsz.
    rewrite low_dropmsb.
    apply/eqP; rewrite -to_nat_inj_ss. rewrite to_nat_dropmsb to_nat_joinlsb /=. done.
    by rewrite /= size_dropmsb.
  Qed.

  Lemma udivB0 : forall n m, (udivB m (zeros n)) = (zeros (size m), m).
  Proof.
    intros; rewrite/udivB. by rewrite to_nat_zeros from_natn0 eq_refl size_rev. 
  Qed.


  Lemma udivB_rec00 : forall n(m : bits) s,
      ~~(m==zeros(size m)) -> udivB_rec (zeros n) m (zeros s) (zeros s)= (zeros s, zeros s).
  Proof.
    elim. intros; first by done.
    intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n. 
    move : (to_nat_zero m). move: H0; rewrite-eqbF_neg; move=>Hnotz; rewrite(eqP Hnotz)eqn0Ngt; move=>Htonat; rewrite Htonat/joinlsb zeros_cons dropmsb_zeros-pred_Sn. rewrite eqbF_neg in Hnotz.
    exact :(H m s Hnotz).
  Qed.
  
  Lemma udivB_rec0 : forall n (m : bits) q r ,
      ~~(m==zeros(size m)) -> udivB_rec (zeros n.+1) m q (zeros r)= (shlB n.+1 q, (zeros r)).
  Proof.
    intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n.
    move : (to_nat_zero m). move: H; rewrite-eqbF_neg; move=>Hnotz; rewrite(eqP Hnotz)eqn0Ngt; move=>Htonat; rewrite Htonat/joinlsb zeros_cons dropmsb_zeros-pred_Sn/shlB1. rewrite eqbF_neg in Hnotz.
    move: q r. elim n; first done.  intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n Htonat/joinlsb zeros_cons dropmsb_zeros-addn1-subn1 addnK.
    move :(H (dropmsb (false :: q)) r). 
    rewrite/shlB1/joinlsb. have->: ((dropmsb (false :: q) <<# n0)%bits = dropmsb (false :: (q <<# n0)%bits)).
    rewrite/shlB/shlB1. elim n0; first done. rewrite/joinlsb/=; intros; by rewrite H0.
    done.
  Qed.
          
  Lemma rev_copy : forall n (b: bool), rev (copy n b) = copy n b.
  Proof.
    elim => [| ns IH] b. done.
    rewrite/=-{1}(IH b) rev_cons revK.
    case b. by rewrite-/b1 ones_rcons. by rewrite-/b0 zeros_rcons. 
  Qed.
  
  Lemma udiv0B : forall n (m: bits), ~~(from_nat n (to_nat m) == zeros n)-> udivB (zeros n) m = (zeros n, zeros n).
  Proof.
    move => n m Hm. move : (negbTE Hm) => Hnot0. rewrite/udivB size_rev size_zeros Hnot0. 
    move : Hnot0. elim n; first done.
    move => ns Hudiv Hnot0.  rewrite rev_copy udivB_rec0; first by rewrite/shlB shlB_mul2exp mul0B.
      by rewrite size_from_nat Hnot0.
  Qed.

  Lemma udivB1_rec : forall m n q,
      ~~(m == zeros (size m)) -> 0 < n -> n = size m -> n = size q ->
      udivB_rec m (b1 :: zeros (n).-1) q (zeros n) = ((high (size m) (rev m)) ++ (low (size q - size m) q),  (shlB (size m) (zeros n))).
  Proof.
    intros. move : (neq_zero_size_gt0 H). move : H1.
    case Hm : m => [|mhd mtl]; first done.
    rewrite/= to_nat_zeros addn0. move => Hnm Hmgt0.
    have Hsznm : size mtl < n by rewrite Hnm.
    move : H0 H2 Hsznm {H Hm Hnm Hmgt0 m}. move : mtl mhd n q .
    elim => [| mthd mttl IH] mhd n q.
    - move => Hngt0 Hsznq Hsznm. rewrite /=.
      case Hmhd : mhd; rewrite/=.
      + rewrite to_nat_dropmsb to_nat_joinlsb size_joinlsb addn1/=.
        rewrite to_nat_zeros -muln2 mul0n add0n size_zeros modn_small;
          last by rewrite -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1)) Hsznm.
        rewrite/=.
        rewrite/= subB_joinmsb_dropmsb; last by rewrite -addn1 -subn1 (subnK Hngt0) size_zeros.
        rewrite -/(shlB1 (zeros n)) /joinlsb -low_dropmsb_joinlsb; last by rewrite -Hsznq Hngt0.
        by rewrite subn1.
      + rewrite to_nat_dropmsb to_nat_joinlsb to_nat_zeros -muln2 mul0n add0n mod0n/=.
        rewrite /shlB1.
        have -> : dropmsb (joinlsb false q) = false :: low (size q - 1) q.
        rewrite -cat1s -/b0. have ->: [::b0] = zeros 1 by done. rewrite -shlB_cat -/(shlB1 q). done.
        by rewrite -Hsznq Hngt0.
        done.
    - move => Hngt0 Hsznq Hsznm.
      rewrite/= to_nat_zeros -muln2 mul0n addn0 /shlB1.
      case Hmhd : mhd ; rewrite/=.
      + have Hszndjq : n = size (dropmsb (joinlsb true q)) by rewrite size_dropmsb size_joinlsb addnK.
        have Hsznm' : size mttl < n by rewrite (ltn_trans (ltnSn (size mttl)) Hsznm).
        rewrite !to_nat_dropmsb !to_nat_joinlsb !to_nat_zeros -(muln2 0) !mul0n !add0n !size_joinlsb -!subn1 !addnK !size_zeros.
        have Hexpgt1 : 1 < 2 ^ n.
        by rewrite -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1)) Hngt0.
        rewrite (modn_small Hexpgt1)/=.
        have H01: (dropmsb (joinlsb true (zeros n)) = b1 :: zeros (n - 1)).
        apply/eqP ; rewrite -to_nat_inj_ss;
          last by rewrite size_dropmsb size_joinlsb /= !size_zeros addnK -addn1 (subnK Hngt0).
        by rewrite to_nat_dropmsb to_nat_joinlsb /= !to_nat_zeros -muln2 mul0n add0n size_zeros (modn_small Hexpgt1).
        rewrite H01 subB_same to_nat_zeros -muln2 mul0n add0n size_zeros/= size_zeros. (*subn1 (ltn_predK Hngt0).*)
        move : (IH mthd n (dropmsb (joinlsb true q)) Hngt0 Hszndjq Hsznm').
        rewrite to_nat_dropmsb to_nat_joinlsb to_nat_zeros -muln2 mul0n add0n size_joinlsb size_zeros addn1/=.
        rewrite -(addn1 (n -1)) (subnK Hngt0).
        rewrite zeros_cons -(addn1 (n -1)) (subnK Hngt0) subn1. move => IHm.
        rewrite IHm.
        rewrite -/(shlB1 (zeros n <<# size mttl)) shlB_zeros -/(shlB1 (shlB1 (zeros n))) !shlB1_zeros.
        have Hc1 : n - (size mttl).+1 < n. move : (leq_subr (size mttl) n). rewrite subnS. move => Hc.
        rewrite -subn1 -(addn1 (n - size mttl - 1)) subnK; last by rewrite subn_gt0 Hsznm'. done.
        rewrite size_dropmsb size_joinlsb addnK.
        have -> : low (size q - (size mttl).+1) (dropmsb (joinlsb true q))
                  = [:: true] ++ low (size q - (size mttl).+2) q
        by (rewrite NBitsDef.low_dropmsb; last by rewrite size_joinlsb -Hsznq addn1 ltnS (ltnW Hc1));
        rewrite cat1s -/joinlsb -low_joinlsb (subnS (size q) (size mttl).+1) -Hsznq;
        generalize Hsznm; rewrite -subn_gt0; move => Hsubgt0; rewrite (ltn_predK Hsubgt0)/=.
        have -> : high (size mttl).+2 (rev [:: true, mthd & mttl])
                  = high (size mttl).+1 (rev (mthd :: mttl)) ++ [::true]
        by rewrite rev_cons high_rcons cats1.
        by rewrite catA.
      + have Hszndjr : n = size (dropmsb (joinlsb mhd (zeros n)) -# (b1 :: zeros n.-1)) by rewrite size_subB size_dropmsb size_joinlsb /= size_zeros addnK -addn1 -subn1 size_zeros (subnK Hngt0) minnn .
        have Hszndjq : n = size (dropmsb (joinlsb false q)) by rewrite size_dropmsb size_joinlsb addnK Hsznq.
        have Hsznm' : size mttl < n by rewrite (ltn_trans (ltnSn (size mttl)) Hsznm).
        move : (IH mthd n (dropmsb (joinlsb false q)) Hngt0 Hszndjq Hsznm').
        rewrite !to_nat_dropmsb !to_nat_joinlsb to_nat_zeros -!muln2 !mul0n !addn0 !mod0n/=.
        rewrite to_nat_dropmsb to_nat_joinlsb to_nat_zeros -!muln2 !mul0n !addn0 mod0n.
        rewrite mul0n add0n !size_dropmsb !size_joinlsb !addnK !size_zeros.
        have -> :(dropmsb (joinlsb false (zeros n))) = zeros n by rewrite -/(shlB1 (zeros n)) shlB1_zeros. 
        move => IHm. rewrite IHm.
        rewrite -/(shlB1 (zeros n <<# size mttl)) -/(shlB1 (shlB1 (zeros n <<# size mttl))) shlB_zeros !shlB1_zeros.
        have Hc1 : n - (size mttl).+1 < n. move : (leq_subr (size mttl) n). rewrite subnS. move => Hc.
        rewrite -subn1 -(addn1 (n - size mttl - 1)) subnK; last by rewrite subn_gt0 Hsznm'. done.
        have ->: low (size q - (size mttl).+1) (dropmsb (joinlsb false q))
        = [::false] ++ low (size q - (size mttl).+2) q
        by (rewrite NBitsDef.low_dropmsb; last by rewrite size_joinlsb -Hsznq addn1 ltnS (ltnW Hc1));
        rewrite cat1s -/joinlsb -low_joinlsb (subnS (size q) (size mttl).+1) -Hsznq;
        generalize Hsznm; rewrite -subn_gt0; move => Hsubgt0; rewrite (ltn_predK Hsubgt0)/=.
        have -> : high (size mttl).+2 (rev [:: false, mthd & mttl])
                  = high (size mttl).+1 (rev (mthd :: mttl)) ++ [::false]
        by rewrite rev_cons high_rcons cats1.
        by rewrite catA.
  Qed.

  Lemma neq_copy_rev_neq_copy m: ~~(m == zeros (size m)) -> ~~(rev m == zeros (size (rev m))).
  Proof.
    move => Hmn0.
    have Hfeq : (rev m == (rev (zeros (size m))) -> m == zeros (size m)).
    by move/eqP => Hrm; move : (f_equal rev Hrm) => Hm; rewrite 2!revK in Hm; apply/eqP.
    rewrite /zeros -(rev_copy) -/(zeros (size (rev m))) size_rev. exact : (contra Hfeq Hmn0). 
  Qed.

  Lemma udivB1: forall m, ~~(m==zeros(size m)) -> udivB m (from_nat (size m) 1) = (m, zeros (size m)).
  Proof.
    move => m Hm. rewrite /udivB.
    rewrite size_rev to_nat_from_nat. move : (neq_zero_size_gt0 Hm) => Hsz.
    generalize Hsz. rewrite -(ltn_exp2l _ _ (ltnSn 1)). rewrite expn0. move => Hgt1.
    rewrite (modn_small Hgt1).
    have ->: (size m) -bits of (1) = b1 :: (zeros (size m).-1).
    apply/eqP; rewrite -to_nat_inj_ss. rewrite to_nat_cons to_nat_zeros/= to_nat_from_nat (modn_small Hgt1); done.
    rewrite size_from_nat/= size_zeros -subn1 -addn1 (subnK Hsz); done.
    have ->: (zeros (size m) = b0::zeros (size m -1)) by rewrite zeros_cons -addn1 (subnK Hsz).
    rewrite eqseq_cons/=. 
    rewrite zeros_cons -addn1 (subnK Hsz).
    rewrite -(size_rev m) in Hsz.
    have Hsznm : size (rev m) = size (zeros (size m)) by rewrite size_rev size_zeros.
    move : (udivB1_rec (neq_copy_rev_neq_copy Hm) Hsz (eqP (eq_refl (size (rev m)))) Hsznm) => Hudivr.
    rewrite size_rev in Hudivr. rewrite Hudivr revK size_zeros subnn low0 cats0 high_size.
    have -> : zeros (size m) <<# size m = zeros (size m).
    apply/eqP; rewrite -to_nat_inj_ss; last by rewrite size_shlB .
    rewrite to_nat_shlBnm to_nat_zeros mul0n mod0n. by case m.
    done.
Qed.

  Lemma lt0B_size : forall b, ([::] <# b)%bits -> 0 < size b.
  Proof.
    elim; first done. intros; by rewrite ltn0Sn.
  Qed.

  Lemma odd_to_nat_lsb : forall b, odd (to_nat b) =lsb b.
  Proof.
    elim; first by rewrite/lsb/splitlsb/=.
    move => a l IH.
    rewrite/lsb/=odd_add odd_double-negb_eqb. case Ha : a; done.
  Qed.


  Lemma lt1_eq0 : forall (n:nat), n<1 -> n=0.
  Proof. intros. induction n; try done.
  Qed.

  Lemma rev_cons_nil : forall (hd:bool) tl, ~~ (rcons tl hd == [::]).
  Proof.
    intros. move : hd. elim tl;  done.
  Qed.
    
  Lemma rev_nil : forall (hd:bool) tl, ~~ (rev (hd :: tl) == [::]).
  Proof.
    move => hd tl. rewrite rev_cons. exact : rev_cons_nil.
  Qed.

  Lemma udivB_rec_step :
    forall m n q r, 0 < size m -> 0 < size n -> size n = size m -> size n = size r -> size n = size q ->
                    udivB_rec m n q r
                    = udivB_rec (splitlsb m).2 n ([::(~~ (((to_nat r).*2 + (lsb m)) %% 2 ^ size r < to_nat n))] ++ low (size m).-1 q) (subB (dropmsb (joinlsb (lsb m) r)) (andB (copy (size n)(~~ (((to_nat r).*2 + (lsb m)) %% 2 ^ size r < to_nat n))) n)).
  Proof.
    elim => [| mhd mtl IH] n q r. done.
    move => Hszm Hszn Hsznm Hsznr Hsznq. rewrite /=to_nat_dropmsb to_nat_joinlsb /lsb/=.
    case Hcond : (~~ (((to_nat r).*2 + mhd) %% 2 ^ size r < to_nat n)); rewrite andB_copy_case.
    rewrite -low_dropmsb_joinlsb; last by rewrite -Hsznq Hszn.
    by rewrite -Hsznq Hsznm.
    rewrite -low_dropmsb_joinlsb; last by rewrite -Hsznq Hszn.
    have ->: size n = size (dropmsb (joinlsb mhd r)) by rewrite Hsznr size_dropmsb size_joinlsb addnK.
    by rewrite from_natn0 subB0 -Hsznq Hsznm.
  Qed.

  Lemma subB_addB : forall bs1 bs2, addB (subB bs1 bs2) bs2 = bs1.
  Proof.
  Admitted.

  Lemma udivB_rec_div : 
    forall m n q r, 0 < size n -> size m <= size n -> size n = size r -> size n = size q ->
                    ~~(n == zeros (size n)) ->
                    ltB r n ->
                    (udivB_rec m n q r).1 =
                    from_nat (size m) (divn (to_nat (rev m)) (to_nat n)) ++ low (size m) r ++ low (size n - size m) q.
  Proof.
    elim => [|mhd mtl IH] n q r Hszn Hsznm Hsznr Hsznq Hnnot0 Hltrn. by rewrite div0n/= low0 Hsznq subn0 low_size cat0s.
    case Hcond : ((to_nat (dropmsb (joinlsb mhd r)) < to_nat n)).
    - have Hsznr' : size n = size (dropmsb (joinlsb mhd r)) by rewrite size_dropmsb size_joinlsb addnK Hsznr.
      have Hsznq' : size n = size (dropmsb (joinlsb false q)) by rewrite size_dropmsb size_joinlsb addnK Hsznq.

      rewrite/= Hcond (@IH n (dropmsb (joinlsb false q)) (dropmsb (joinlsb mhd r)) Hszn (ltnW Hsznm) Hsznr' Hsznq' Hnnot0).
      generalize Hsznm. rewrite /=; move => Hsznm'.
      rewrite NBitsDef.low_dropmsb; last by rewrite size_joinlsb -Hsznr addn1 ltnS (ltnW Hsznm'). 
      
    
  Admitted.
  
  Lemma udivB_to_nat : forall m n,  size m = size n -> to_nat (udivB (m) n).1 = divn (to_nat (m)) (to_nat n).
  Proof.
    intros. rewrite/udivB .
    case Hcond : ((size m) -bits of (to_nat n) == zeros (size m)); rewrite/= H from_nat_to_nat in Hcond.
    - by rewrite (eqP Hcond) !to_nat_zeros divn0 from_natn0 eq_refl/= to_nat_zeros.
    - move : (negbT Hcond) => Hnnot0. rewrite size_rev H from_nat_to_nat. move : (neq_zero_size_gt0 Hnnot0) => Hszn.
      have Hsznm : (size m <= size n). rewrite leq_eqVlt. move/eqP : H => H. by rewrite H orTb.
      have Hszr : (size n = size (zeros (size m))) by rewrite size_zeros H.
      move : (neq_zeros_to_nat_gt0 Hnnot0). rewrite -(to_nat_zeros (size m)) -ltB_to_nat; move => Hltrn.
      rewrite Hcond.
      have Hsznm' : (size (rev m) <= size n) by rewrite size_rev .
      rewrite -H.
      rewrite (@udivB_rec_div (rev m) n (zeros (size m)) (zeros (size m)) Hszn Hsznm' Hszr Hszr Hnnot0 Hltrn).
      rewrite size_rev to_nat_cat -{2}(size_zeros (size m)) -H subnn low0 low_size cats0 to_nat_zeros mul0n addn0.
      case Hn1 : ((to_nat n) == 1). rewrite revK (eqP Hn1) divn1 to_nat_from_nat_bounded; last by rewrite to_nat_bounded. done.
      have Hgt1 :(1< to_nat n) by rewrite ltn_neqAle eq_sym Hn1 andTb (neq_zeros_to_nat_gt0). 
      case Hm0 : (to_nat (m) == 0). by rewrite revK (eqP Hm0) div0n from_natn0 to_nat_zeros.
      move : (negbT Hm0) => Hmnot.
      rewrite -lt0n in Hmnot.
      move : (ltn_Pdiv Hgt1 Hmnot) => Hbd. 
      rewrite to_nat_from_nat_bounded revK //.
      exact : (ltn_trans Hbd (to_nat_bounded m)). 
  Qed.
     
  Lemma udivB_negB_negB bs1 bs2 :
    size bs1 = size bs2 -> udivB (negB bs1) (negB bs2) = ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2).
  Proof.
  Admitted.

    Lemma from_Zpos_to_Zpos bs : from_Zpos (size bs) (to_Zpos bs) = bs.
  Proof.
  Admitted.

  Lemma to_Zpos_ltB_subB bs1 bs2 :
    size bs1 = size bs2 -> negb (ltB bs1 bs2) -> to_Zpos (bs1 -# bs2) 
    = (to_Zpos bs1 - to_Zpos bs2)%Z.
  Proof.
    intros.
    rewrite (to_Zpos_subB H). SearchAbout borrow_subB.
    move/negbTE : H0 => H0.
    by rewrite -(ltB_equiv_borrow_subB H) H0 Z.mul_0_l Z.add_0_l.
  Qed.    

  
  Lemma modn_neq : forall m d, d > 0 -> d <= m-> ~~ (m %% d == m).
  Proof.
    intros.
    rewrite -(ltn_mod m) in H.
    move : (ltn_leq_trans H H0) => Hgt.
    rewrite ltn_neqAle in Hgt. move/andP : Hgt => [Hne Hle]. exact.
  Qed.


  Lemma to_nat_gt0_size : forall bs, 0 < to_nat bs -> 0 < size bs.
  Proof.
    intro bs; case bs; try done.
  Qed.    
  

  Lemma Zmod_odd' : forall m d : Z, Z.odd d = false -> Z.odd (m mod d) = Z.odd m.
  Proof.
  Admitted.

  Lemma ltB_dropmsb_joinlsb_ltB :
    forall m n b, size m = size n -> ltB m n ->
                  ltB (dropmsb (joinlsb b m) -# n) (n ++ [::(borrow_subB (dropmsb (joinlsb b m)) n)] ).
  Proof.
    intros.
    move : H0.
    rewrite !ltB_to_Zpos. move => H0.
    have Hszsdj : size (dropmsb (joinlsb b m) -# n) = size n by rewrite size_subB size_dropmsb size_joinlsb addnK H minnn.
    rewrite to_Zpos_subB; last by rewrite size_dropmsb size_joinlsb addnK H.
    have Hsznm : size (dropmsb (joinlsb b m)) = size n by rewrite size_dropmsb size_joinlsb addnK H.
    rewrite to_Zpos_dropmsb to_Zpos_joinlsb size_dropmsb size_joinlsb Nat2Z.inj_add Z.add_simpl_r addnK.
    rewrite Z.lt_sub_lt_add_r to_Zpos_cat Z.add_shuffle0 Z.add_diag -H.
    have -> : to_Zpos [:: borrow_subB (dropmsb (joinlsb b m)) n] = borrow_subB (dropmsb (joinlsb b m)) n
      by rewrite/to_Zpos/=Z.add_0_r.
    rewrite Z.add_comm -Z.add_lt_mono_r.
    case b.
    - move : (Zlt_le_succ _ _ (Zmult_lt_compat_r _ _ _ Z.lt_0_2 H0)) => Hle.
      rewrite /Z.succ in Hle.
      move : (Z.add_nonneg_nonneg _ _ (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 m) (Z.le_0_2)) Z.le_0_1) => Haux.
      move : (Z.pow_pos_nonneg _ _ (Z.lt_0_2) (Nat2Z.is_nonneg (size m))) => Haux2.
      move : (Z.mod_le _ _ Haux Haux2) => {Haux}{Haux2}Hmodle.
      move : (Z.le_trans _ _ _ Hmodle Hle) => Hle'.
      rewrite /Z.succ (Z.mul_comm 2 (to_Zpos n)).
      move : (Zle_lt_or_eq _ _ Hle') => [Hlt|Heq]; first done.
      have Haux : (Z.odd (2 ^ Z.of_nat (size m)) = false)%Z by omega.
      move : (Zmod_odd' ((to_Zpos m * 2 + true)) Haux). 
      by rewrite Z.odd_add Z.odd_mul/= andbF /= Heq Z.odd_mul/=andbF.
    - rewrite Z.add_0_r (Z.mul_comm 2 (to_Zpos n)).
      move : (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 m) (Z.le_0_2)) => Haux.
      move : (Z.pow_pos_nonneg _ _ (Z.lt_0_2) (Nat2Z.is_nonneg (size m))) => Haux2.
      move : (Z.mod_le _ _ Haux Haux2) => {Haux}{Haux2}Hmodle.
      move : (Zmult_lt_compat_r _ _ _ Z.lt_0_2 H0) => Hlt.
      exact : (Z.le_lt_trans _ _ _ Hmodle Hlt).
  Qed.

  Lemma to_Zpos_subB_cancel bs1 bs2 :
    size bs1 = size bs2 -> bs2 <=# bs1 ->
    to_Zpos (bs1 -# bs2 +# bs2) = (to_Zpos (bs1 -# bs2) + to_Zpos bs2)%Z.
  Proof.
  Admitted.

  Lemma dropmsb_joinlsb b bs : 0 < size bs -> (dropmsb (joinlsb b bs)) = joinlsb b (dropmsb bs).
  Proof.
    intro. by rewrite -(low_dropmsb_joinlsb _ H) -dropmsb_low (ltn_predK H) low_size. 
  Qed.

  Lemma shl_add_mod_mod :
    forall b a d ,
      size b <= size a -> size a = size d-> a <# d = false ->
    (((to_Zpos (b) + 2 ^ Z.of_nat (size b) * (to_Zpos (a -# d) + to_Zpos d))mod 2 ^ Z.of_nat (size d)
     mod to_Zpos d) =
    (((to_Zpos (b) + 2 ^ Z.of_nat (size b) * to_Zpos (a -# d))
      mod 2 ^ Z.of_nat (size d)) mod to_Zpos d))%Z.
  Proof.
    elim => [|bns IH] a d Hszba Hszad Had.
    - rewrite (lock Z.of_nat)/=-lock Nat2Z.inj_0 Z.pow_0_r Z.mul_1_l.
      rewrite Z.mod_small; last  admit.
      rewrite Z.mul_1_l -to_Zpos_subB_cancel; last admit; last admit.
  Admitted.

  Lemma shlB1_addB_nocarry : forall bs1  n, (to_Zpos (low n (shlB1 bs1) +# (low n (from_nat (size bs1) 1))) = to_Zpos (low n (shlB1 bs1)) + to_Zpos (low n (from_nat (size bs1) 1)))%Z.
  Proof. Admitted.


  Lemma to_Zpos_from_Zpos (bs:bits) z: (to_Zpos (from_Zpos (size (bs)) z) = z mod (2 ^ Z.of_nat (size bs)))%Z.
  Proof.
  Admitted.
       
  Lemma to_Zpos_udivB_rec_div :
    forall m n q r , size m <= size n -> size r = size n ->size q = size n ->
                    ~~(n == zeros (size n)) ->
                    ltB r n ->
                    (udivB_rec m n q r).1 =
                    (*low (size q)*) (from_Zpos (size n) (Z.div (to_Zpos (high (size m) (rev m) ++ low (size q - size m) r)) (to_Zpos n) + to_Zpos (shlB (size m) q))).
  Proof.
    elim => [|mhd mtl IH] n q r Hsznm Hsznr Hsznq Hnnot0 Hltrn .
    - 
      generalize Hltrn; rewrite ltB_to_Zpos; move => Hltz.
      move : (@to_Zpos_ge0 r) => Hrge0z.
      rewrite/=subn0 Hsznq -Hsznr low_size Zdiv_small; last by split.
      rewrite Z.add_0_l Hsznr -Hsznq from_Zpos_to_Zpos. done.
    - move : (neq_zeros_to_nat_gt0 Hnnot0).
      move : (neq_zero_size_gt0 Hnnot0) => Hszn0.
      rewrite -{1}(to_nat_zeros (size n)) -ltB_to_nat.  move => Hngt0.
      case Hcond : (to_nat (dropmsb (joinlsb mhd r)) < to_nat n).
      + rewrite /= Hcond /=. 
        have Hsznr' : size (dropmsb (joinlsb mhd r)) = size n by rewrite size_dropmsb size_joinlsb Hsznr addnK.
        generalize Hcond; rewrite -ltB_to_nat; move => Hcondlt.
        have Hsznq' : size (dropmsb (joinlsb false q)) = size n by rewrite size_dropmsb size_joinlsb Hsznq addnK.
        rewrite (IH n (dropmsb (joinlsb false q)) (dropmsb (joinlsb mhd r)) (ltnW Hsznm) Hsznr' Hsznq' Hnnot0 Hcondlt) .
        rewrite rev_cons high_rcons.
        rewrite size_dropmsb size_joinlsb addnK -{1 4}(size_rev mtl) high_size cat_rcons.
        generalize Hsznm; rewrite/= -subn_gt0; move => Hsznmsub.
        rewrite -/joinlsb -low_joinlsb subnS Hsznq (ltn_predK Hsznmsub).
        rewrite NBitsDef.low_dropmsb;
          last by rewrite size_joinlsb Hsznr addn1 ltnS leq_subr.
        rewrite -/(shlB1 q) shlB1_shlB //.
      + rewrite /= Hcond/=.
        have Hsznr' : size (dropmsb (joinlsb mhd r) -# n) = size n by rewrite size_subB size_dropmsb size_joinlsb Hsznr addnK minnn.
        have Hsznq' : size (dropmsb (joinlsb true q)) = size n by rewrite size_dropmsb size_joinlsb Hsznq addnK.
        generalize Hcond; rewrite -ltB_to_nat; move => Hcondlt.
        move : (ltB_dropmsb_joinlsb_ltB mhd Hsznr Hltrn).
        rewrite -ltB_equiv_borrow_subB; last by rewrite size_dropmsb size_joinlsb addnK Hsznr.
        rewrite Hcondlt ltB_to_Zpos to_Zpos_cat /= Z.add_0_r -ltB_to_Zpos. 
        move => Hlt.
        generalize Hlt; rewrite ltB_to_Zpos; move => Hltz.
        rewrite (IH n (dropmsb (joinlsb true q)) (dropmsb (joinlsb mhd r) -# n) (ltnW Hsznm) Hsznr' Hsznq' Hnnot0 Hlt).
        rewrite rev_cons -{1 4}(size_rev mtl) high_rcons high_size cat_rcons.
        rewrite -/joinlsb -low_joinlsb subnS.
        generalize Hsznm; rewrite/= -subn_gt0; move => Hsznmsub.
        rewrite Hsznq (ltn_predK Hsznmsub).
        rewrite size_dropmsb size_joinlsb addnK Hsznq.
        symmetry.
        rewrite -NBitsDef.low_dropmsb; last by rewrite size_joinlsb Hsznr addn1 ltnS leq_subr.
        rewrite -{1}(subB_addB (dropmsb (joinlsb mhd r)) n) shlB1_shlB.
        rewrite 2!to_Zpos_cat.
        have Haux : (dropmsb (joinlsb true q)) == succB (shlB1 q).
        rewrite -to_nat_inj_ss; last by rewrite size_dropmsb size_joinlsb addnK size_succB size_shlB1.
        rewrite to_nat_dropmsb to_nat_joinlsb.
        rewrite -addB1 to_nat_addB to_nat_shlB1 !to_nat_from_nat size_joinlsb size_addB size_shlB1 size_from_nat minnn addn1/= modnDm //.
        rewrite (eqP Haux) shlB_cat; last by rewrite size_shlB1 Hsznq (ltnW Hsznm).
        rewrite shlB_cat; last by rewrite size_succB size_shlB1 Hsznq (ltnW Hsznm).
        rewrite 2!to_Zpos_cat to_Zpos_zeros 2!Z.add_0_l size_succB size_shlB1.
        rewrite low_addB;
          [|rewrite size_subB size_dropmsb size_joinlsb addnK Hsznr minnn leq_subr//| rewrite leq_subr//]. 
        rewrite low_subB;
          [|rewrite size_dropmsb size_joinlsb addnK Hsznr leq_subr//| rewrite leq_subr//].
        rewrite to_Zpos_subB_cancel; [|by rewrite !size_low|admit].
        rewrite -addB1 low_addB; [|rewrite size_shlB1 leq_subr//|rewrite size_from_nat size_shlB1 leq_subr//].
        rewrite size_zeros size_shlB1 shlB1_addB_nocarry/=.
        generalize Hsznmsub; move/ltP => Hltp. rewrite-> Nat2Z.inj_lt in Hltp. rewrite Nat2Z.inj_0 in Hltp.
        apply (Z.pow_gt_1 2 (Z.of_nat(size n - size mtl)) Z.lt_1_2) in Hltp.
        have -> :to_Zpos (low (size q - size mtl) (size q) -bits of (1)) = 1%Z
          by rewrite Hsznq; move :(from_natn1 Hszn0) => Hnat1; rewrite (eqP Hnat1); rewrite -to_Zpos_mod_pow2 to_Zpos_zext/= Z.mod_small; last (split; try done). 
        symmetry.
        rewrite Z.mul_add_distr_r Z.mul_1_l Z.add_assoc Z.add_shuffle0.
        rewrite Z.mul_add_distr_r. 
        rewrite ->ltB_to_Zpos in Hngt0. rewrite to_Zpos_zeros in Hngt0.
        rewrite -Z_div_plus; last exact: (Z.lt_gt _ _ Hngt0).
        rewrite size_rev .
        have -> : (to_Zpos (low (size n - size mtl) n)  * 2 ^ Z.of_nat (size mtl) = to_Zpos (zeros (size mtl) ++ low (size n - size mtl) n))%Z
          by rewrite to_Zpos_cat to_Zpos_zeros Z.add_0_l size_zeros.
        admit.
  Admitted.

  
  Lemma to_Zpos_udivB : forall m n , size n = size m -> ~~(n == zeros (size n)) ->
                                     to_Zpos (udivB (rev m) n).1 = (Zdiv (to_Zpos (rev m)) (to_Zpos n)).
  Proof.
    intros. rewrite/udivB revK /=.
    case Hcond : ((size m) -bits of (to_nat n) == zeros (size m)); rewrite/= -H from_nat_to_nat in Hcond.
    - by rewrite Hcond in H0.
    - move : (negbT Hcond) => Hnnot0. rewrite -H from_nat_to_nat. move : (neq_zero_size_gt0 Hnnot0) => Hszn.
      have Hsznm : (size m <= size n). rewrite leq_eqVlt. move/eqP : H => H. by rewrite eq_sym (H) orTb.
      have Hszr : (size n = size (zeros (size n))) by rewrite size_zeros H.
      move : (neq_zeros_to_nat_gt0 Hnnot0). rewrite -(to_nat_zeros (size m)) -ltB_to_nat ; move => Hltrn.
      move/eqP : Hszr. rewrite eq_sym; move/eqP => Hszr. rewrite -H in Hltrn.
      rewrite (@to_Zpos_udivB_rec_div m n (zeros (size n)) (zeros (size n)) Hsznm Hszr Hszr Hnnot0 Hltrn).
      rewrite size_zeros -{1}(size_rev m) high_size low_zeros shlB_zeros to_Zpos_zeros Z.add_0_r.
      rewrite to_Zpos_cat to_Zpos_zeros Z.mul_0_l Z.add_0_r.
      rewrite to_Zpos_from_Zpos.
      move/negbT : Hcond => Hcond.
      move : (neq_zeros_to_nat_gt0 Hcond).
      move : (neq_zero_size_gt0 Hcond) => Hszn0.
      rewrite -{1}(to_nat_zeros (size n)) -ltB_to_nat.  move => Hngt0.
      rewrite ->ltB_to_Zpos in Hngt0.
      case Hrvm : ((rev m)== zeros (size m)).
      have Hrvmz : (to_Zpos (rev m) = 0)%Z by rewrite (eqP Hrvm) to_Zpos_zeros.
        by rewrite Hrvmz Zdiv_0_l Zmod_0_l.
      (*have Hgt0z : (0 < to_Zpos (rev m))%Z.*)
      move/negbT: Hrvm. rewrite -(size_rev m). move => Hmnot0.
      move : (neq_zeros_to_nat_gt0 Hmnot0). rewrite -(to_nat_zeros (size m)) -ltB_to_nat ; move => Hltrnb.
      rewrite ->ltB_to_Zpos in Hltrnb.
      rewrite to_Zpos_zeros in Hltrnb.
      move : (neq_zero_size_gt0 Hmnot0) => Hszm0z.
      move/ltP : Hszm0z. rewrite Nat2Z.inj_lt Nat2Z.inj_0; move => Hszm0z.
      rewrite -> (Z.pow_gt_1 2 (Z.of_nat(size (rev m))) Z.lt_1_2) in Hszm0z.
      rewrite Zmod_small. done.
      rewrite to_Zpos_zeros in Hngt0. SearchAbout (Zlt).
      split. move: (Z_div_ge0 _ _ (Z.lt_gt _ _ Hngt0) (Z.le_ge _ _ (Z.lt_le_incl _ _ Hltrnb)) ).
      exact : Z.ge_le.
      apply Z.div_lt_upper_bound; try done.
      move : (to_Zpos_bounded (rev m)); rewrite size_rev -H.
      have Haux : (2 ^ Z.of_nat (size n) <= to_Zpos n * 2 ^ Z.of_nat (size n))%Z.
      rewrite -{1}(Z.mul_1_l (2 ^ Z.of_nat (size n))). have ->: 1%Z = Z.of_nat 1 by done.
      apply (Z.mul_le_mono_nonneg_r _ _ _ (Z.pow_nonneg _ _ Z.le_0_2)).
      move : (Zlt_le_succ _ _ Hngt0). rewrite//.
      move => Hlt.
      exact : (Z.lt_le_trans _ _ _ Hlt Haux).
  Qed.

  (*---------------------------------------------------------------------------
    Properties of unsigned modulo
  ---------------------------------------------------------------------------*)
  Definition uremB bs1 bs2 := (udivB bs1 bs2).2.

    
  Lemma to_Zpos_udivB_rec_rem :
    forall m n q r , 0 < size n -> size m <= size n -> size r = size n ->
                    ~~(n == zeros (size n)) ->
                    ltB r n ->
                    (udivB_rec m n q r).2 =
                    (*from_Zpos (size n) (Zmod (to_Zpos (high (size n) (shlB (size m) ((rev m) ++ r)))) (to_Zpos n)).*)
                    from_Zpos (size n) ((Zmod ((to_Zpos (rev m) + (2 ^ Z.of_nat (size m) * to_Zpos r)) mod 2 ^ Z.of_nat (size r)) (to_Zpos n)))%Z.
  Proof.
    elim => [| mhd mtl IH] n q r Hszn Hsznm Hsznr Hnnot0 Hltrn.
    - rewrite ->(ltB_to_Zpos) in Hltrn.
      rewrite Nat2Z.inj_0 Z.pow_0_r Z.mul_1_l/=  -Hsznr to_Zpos_mod_pow2 low_size. 
      have : (0 <= to_Zpos r < to_Zpos n)%Z. split. exact : to_Zpos_ge0.
      exact  Hltrn.
      move => Hmodsm. 
      by rewrite (Zmod_small _ _ Hmodsm) from_Zpos_to_Zpos. 
    - move : (neq_zeros_to_nat_gt0 Hnnot0). rewrite -{1}(to_nat_zeros (size n)) -ltB_to_nat.  move => Hngt0.
      case Hcond : (to_nat (dropmsb (joinlsb mhd r)) < to_nat n).
      + rewrite (lock Z.of_nat) /= Hcond /=. 
        have Hsznr' : size (dropmsb (joinlsb mhd r)) = size n by rewrite size_dropmsb size_joinlsb Hsznr addnK.
        generalize Hcond; rewrite -ltB_to_nat; move => Hcondlt.
        rewrite (IH n (dropmsb (joinlsb false q)) (dropmsb (joinlsb mhd r)) Hszn (ltnW Hsznm) Hsznr' Hnnot0 Hcondlt) .
        rewrite rev_cons to_Zpos_rcons size_rev.
        rewrite (ltB_to_Zpos_eqn) in Hcondlt.
        have : (0 <= to_Zpos (dropmsb (joinlsb mhd r)) < to_Zpos n)%Z. split. exact : to_Zpos_ge0.
        rewrite<- Z.ltb_lt. by rewrite Hcondlt.
        move => Hmodsm.
        rewrite -lock -addn1 Nat2Z.inj_add (Z.pow_add_r _ _ _ (Nat2Z.is_nonneg _) (Nat2Z.is_nonneg _)).
        rewrite size_dropmsb size_joinlsb Nat2Z.inj_sub; last (apply/leP; by rewrite addn1).
        rewrite Nat2Z.inj_add Z.add_simpl_r.
        have -> :  Z.of_nat 1 = 1%Z by done. rewrite Z.pow_1_r.
        have Hszr : 0 < size r by rewrite Hsznr.
        rewrite -Z.add_assoc.
        rewrite (dropmsb_joinlsb mhd Hszr) to_Zpos_joinlsb to_Zpos_dropmsb -Zmult_mod_distr_r.
        rewrite -{4}(Z.pow_1_r 2).
        rewrite -(Z.pow_add_r 2 (Z.of_nat (size r) -1) 1 _ Z.le_0_1);
          last by (rewrite Z.sub_1_r; apply Zlt_0_le_0_pred; rewrite -Nat2Z.inj_0; apply inj_lt; apply/ltP).
        rewrite Z.sub_add (Z.mul_comm (to_Zpos r) 2) (Z.add_comm ((2 * to_Zpos r) mod 2 ^ Z.of_nat (size r)) mhd).
        rewrite Z.mul_add_distr_l.
        symmetry. rewrite -Zplus_mod_idemp_r.
        have Hszaux1 : (0 <= 2 ^ Z.of_nat (size mtl))%Z by exact : (Z.pow_nonneg 2 (Z.of_nat (size mtl)) Z.le_0_2). 
        
        have Hszaux2 : (2 ^ Z.of_nat (size mtl) < 2 ^ Z.of_nat (size r))%Z.
        generalize Hsznm; rewrite /=; move/ltP/inj_lt => Hsznm'. rewrite Hsznr.
        by exact : (Z.pow_lt_mono_r 2 (Z.of_nat (size mtl)) _ Z.lt_1_2 (Nat2Z.is_nonneg (size n)) Hsznm').
        have -> : (2 ^ Z.of_nat (size mtl) * ((2 * to_Zpos r) mod 2 ^ Z.of_nat (size r)) =
                   ((2 ^ Z.of_nat (size mtl) mod  2 ^ Z.of_nat (size r))* ((2 * to_Zpos r) mod 2 ^ Z.of_nat (size r))))%Z
          by rewrite (Z.mod_small (2 ^ Z.of_nat (size mtl)) (2 ^ Z.of_nat (size r))); last by split.
        symmetry. rewrite Z.add_assoc.
        rewrite -Zplus_mod_idemp_r -Zmult_mod 2!Zplus_mod_idemp_r.
        by rewrite (Z.mul_comm (2 ^ Z.of_nat (size mtl)) (mhd)) Z.mul_assoc Z.add_assoc.
      + rewrite (lock Z.of_nat)/= Hcond/=.
        have Hsznr' : size (dropmsb (joinlsb mhd r) -# n) = size n by rewrite size_subB size_dropmsb size_joinlsb Hsznr addnK minnn.
        generalize Hcond; rewrite -ltB_to_nat; move => Hcondlt.
        move : (ltB_dropmsb_joinlsb_ltB mhd Hsznr Hltrn) => Hlt.
        rewrite -ltB_equiv_borrow_subB in Hlt; last by rewrite size_dropmsb size_joinlsb addnK Hsznr.
        rewrite Hcondlt in Hlt.
        generalize Hlt; rewrite ltB_to_Zpos; move => Hltz; rewrite to_Zpos_cat/=Z.add_0_r in Hltz.
        generalize Hltz; rewrite -ltB_to_Zpos; move => {Hlt} Hlt.
        rewrite (IH n (dropmsb (joinlsb true q)) (dropmsb (joinlsb mhd r) -# n) Hszn (ltnW Hsznm) Hsznr' Hnnot0 Hlt).
        rewrite size_subB size_dropmsb size_joinlsb addnK Hsznr minnn -addn1 -lock .
        rewrite Nat2Z.inj_add (Z.pow_add_r _ _ _ (Nat2Z.is_nonneg _) (Nat2Z.is_nonneg _)).
        have -> :  Z.of_nat 1 = 1%Z by done. rewrite Z.pow_1_r rev_cons to_Zpos_rcons. symmetry.
        rewrite -Z.add_assoc Z.mul_comm -Z.mul_assoc size_rev -Z.mul_add_distr_l.
        rewrite (Z.add_comm mhd (2 * to_Zpos r)) (Z.mul_comm 2 (to_Zpos r)) -to_Zpos_joinlsb.
        rewrite -Zplus_mod_idemp_r -Zmult_mod_idemp_r.
        have {2}->: size n = size (joinlsb mhd r) -1 by rewrite size_joinlsb addnK Hsznr.
        have -> : ((to_Zpos (joinlsb mhd r) mod 2 ^ Z.of_nat (size (joinlsb mhd r) - 1)) = to_Zpos (dropmsb (joinlsb mhd r)))%Z.
        rewrite to_Zpos_dropmsb Nat2Z.inj_sub; last by (rewrite size_joinlsb; apply/leP; rewrite addn1).
        have -> :  Z.of_nat 1 = 1%Z by done.  done.
        have Hszaux : (size (dropmsb (joinlsb mhd r)) = size n) by rewrite size_dropmsb size_joinlsb Hsznr addnK.
        have Hcondaux : n <=# dropmsb (joinlsb mhd r). rewrite leBNlt; last by rewrite Hszaux.
        by rewrite Hcondlt.

        have Hszaux1 : (size (rev mtl) <= size (dropmsb (joinlsb mhd r)))
          by rewrite size_dropmsb size_joinlsb addnK Hsznr size_rev (ltnW Hsznm).
        have Hszaux2 : size (dropmsb (joinlsb mhd r)) = size n
          by rewrite size_dropmsb size_joinlsb addnK Hsznr .
        rewrite -{1}(subB_addB (dropmsb (joinlsb mhd r)) n) (to_Zpos_subB_cancel Hszaux Hcondaux). 
        rewrite Zplus_mod_idemp_r.
        (*rewrite (Z.mod_small (to_Zpos (rev mtl) + 2 ^ Z.of_nat (size mtl) * (to_Zpos (dropmsb (joinlsb mhd r) -# n) + to_Zpos n)) (2 ^ Z.of_nat (size n))).*)
        move : (@shl_add_mod_mod (rev mtl) (dropmsb (joinlsb mhd r)) n Hszaux1 Hszaux2 Hcondlt).
        rewrite size_rev. 
        move => {Hszaux}{Hcondaux}{Hszaux1}.
        move => Haux. rewrite -Haux. done.
  Qed.


  Lemma to_Zpos_uremB : forall m n , size n = size m -> ~~(n == zeros (size n)) ->
                                     to_Zpos (udivB (rev m) n).2 = (Zmod (to_Zpos (rev m)) (to_Zpos n)).
  Proof.
    intros. rewrite/udivB revK /=.
    case Hcond : ((size m) -bits of (to_nat n) == zeros (size m)); rewrite/= -H from_nat_to_nat in Hcond.
    - by rewrite Hcond in H0.
    - move : (negbT Hcond) => Hnnot0. rewrite -H from_nat_to_nat. move : (neq_zero_size_gt0 Hnnot0) => Hszn.
      have Hsznm : (size m <= size n). rewrite leq_eqVlt. move/eqP : H => H. by rewrite eq_sym (H) orTb.
      have Hszr : (size n = size (zeros (size n))) by rewrite size_zeros H.
      move : (neq_zeros_to_nat_gt0 Hnnot0). rewrite -(to_nat_zeros (size m)) -ltB_to_nat ; move => Hltrn.
      move/eqP : Hszr. rewrite eq_sym; move/eqP => Hszr. rewrite -H in Hltrn.
      rewrite (@to_Zpos_udivB_rec_rem m n (zeros (size n)) (zeros (size n)) Hszn Hsznm Hszr Hnnot0 Hltrn).
      rewrite to_Zpos_zeros Z.mul_0_r Z.add_0_r size_zeros H -(size_rev m) to_Zpos_mod_pow2 low_size.
      rewrite to_Zpos_from_Zpos size_rev -H.
      move/ltP : (neq_zeros_to_nat_gt0 Hnnot0) => Hltcoq. move : (inj_lt _ _ Hltcoq).
      rewrite Nat2Z.inj_0 -to_Zpos_nat.  move => Hnlt0z.
      move : (Zmod_le (to_Zpos (rev m)) (to_Zpos n) Hnlt0z (@to_Zpos_ge0 _)) => Hmodle.
      move : (to_Zpos_bounded (rev m)). rewrite size_rev -H => Hlt.
      move : (Z.le_lt_trans _ _ _ Hmodle Hlt) => Hmodsm.
      rewrite (Z.mod_small). done.
      split. move : (Z.mod_pos_bound (to_Zpos (rev m)) _ Hnlt0z) => [H1 H2].
      done. done.
  Qed.

  
  (*---------------------------------------------------------------------------
    Properties of signed division    
  ---------------------------------------------------------------------------*)
  Definition absB bs :=
    if msb bs then negB bs else bs.

  Lemma size_absB bs : size (absB bs) = size bs.
  Proof.
    rewrite /absB. case: (msb bs).
    - rewrite size_negB; reflexivity.
    - reflexivity.
  Qed.

  
  Definition sdivB bs1' bs2' : bits * bits :=
    let bs1 := absB bs1' in
    let bs2 := absB bs2' in
    if (msb bs1' == msb bs2') && negb (msb bs1') then udivB bs1 bs2
    else if (msb bs1' == msb bs2') && (msb bs1') then ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2)
         else if (msb bs1' != msb bs2') && negb (msb bs1') then (negB (udivB bs1 bs2).1, (udivB bs1 bs2).2)
              else (negB (udivB bs1 bs2).1, negB (udivB bs1 bs2).2).

  
  Lemma toZ_sdivB sb1 sb2 : to_Z sb2 <> 0%Z -> size sb1 = size sb2 -> to_Z (sdivB sb1 sb2).1 = Z.div (to_Z sb1) (to_Z sb2).
  Proof.
  Admitted.

  (*---------------------------------------------------------------------------
    Properties of signed remainder
  ---------------------------------------------------------------------------*)

  Definition sremB bs1 bs2 := (sdivB bs1 bs2).2.

  Lemma size_sremB bs1 bs2 : size (sremB bs1 bs2) = size bs1.
  Proof.
    rewrite /sremB. rewrite /sdivB. case: ((msb bs1 == msb bs2) && ~~ msb bs1) => /=.
    - rewrite size_uremB size_absB. reflexivity.
    - case: ((msb bs1 == msb bs2) && msb bs1) => /=.
      + rewrite size_negB size_uremB size_absB. reflexivity.
      + case: (~~ (msb bs1 == msb bs2) && ~~ msb bs1) => /=.
        * rewrite size_uremB size_absB. reflexivity.
        * rewrite size_negB size_uremB size_absB. reflexivity.
  Qed.

    Lemma toZ_sremB sb1 sb2 : to_Z sb2 <> 0%Z -> size sb1 = size sb2 -> to_Z (sdivB sb1 sb2).2 = Z.rem (to_Z sb1) (to_Z sb2).
  Proof.
  Admitted.
  (*---------------------------------------------------------------------------
    Properties of signed modulo
  ---------------------------------------------------------------------------*)

  Definition smodB bs1 bs2 : bits :=
  let (q_sdiv, r_sdiv) := eta_expand (sdivB bs1 bs2) in
  if (msb bs1 == msb bs2) || (r_sdiv == (zeros (size r_sdiv))) then
    r_sdiv
  else addB r_sdiv bs2.

  Lemma size_smodB bs1 bs2 :
    size (smodB bs1 bs2) =
    if (msb bs1 == msb bs2) || is_zero (eta_expand (sdivB bs1 bs2)).2
    then size bs1
    else minn (size (eta_expand (sdivB bs1 bs2)).2) (size bs2).
  Proof.
    rewrite /smodB.
    case H: ((msb bs1 == msb bs2) ||
             ((sdivB bs1 bs2).2 == zeros (size (sdivB bs1 bs2).2))).
    - case/orP: H => H.
      + rewrite H /=. rewrite size_sremB. reflexivity.
      + rewrite (eqP H) /=. rewrite zeros_is_zero orbT /=.
        rewrite size_zeros size_sremB. reflexivity.
    - move/Bool.orb_false_iff: H => [H1 H2]. rewrite H1 /=.
      have ->: is_zero (sdivB bs1 bs2).2 = false.
      { apply/negP=> H3. move/negP: H2. apply. rewrite {1}(is_zero_zeros H3).
        exact: eqxx. }
      rewrite size_addB. reflexivity.
  Qed.

  Lemma size_smodB_ss bs1 bs2 :
    size bs1 = size bs2 -> size (smodB bs1 bs2) = size bs1.
  Proof.
    move=> Hs. rewrite size_smodB.
    case: ((msb bs1 == msb bs2) || is_zero (eta_expand (sdivB bs1 bs2)).2).
    - reflexivity.
    - rewrite size_sremB Hs minnn. reflexivity.
  Qed.

    Lemma toZ_smodB sb1 sb2 : to_Z sb2 <> 0%Z -> size sb1 = size sb2 -> to_Z (smodB sb1 sb2) = Z.modulo (to_Z sb1) (to_Z sb2).
  Proof.
  Admitted.
  
  (*---------------------------------------------------------------------------
    Others
  ---------------------------------------------------------------------------*)  
  Lemma to_nat_not_zero (q : bits) : (q == zeros (size q))=false -> (to_nat q == 0)=false.  
  Proof.
    intro. apply negbT in H; rewrite -ltB0n ltB_to_nat/= in H.
    apply/eqP. rewrite-(prednK H). apply Nat.neq_succ_0. 
  Qed.


  
(*---------------------------------------------------------------------------
    Unsigned multiplication overflow detection
  ---------------------------------------------------------------------------*) 

  Fixpoint sig_bits_aux bs n : nat :=
    match bs with
    | [::] => n
    | hd :: tl => if hd then n else sig_bits_aux tl (n - 1)
    end .

  Definition sig_bits bs := sig_bits_aux (rev bs) (size bs).

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

  (*
  Lemma rev_behead : forall bs, zext (size bs - (size bs - 1)) (rev (behead bs)) = rev bs.
  Proof.
    elim =>[|bshd bstl IH]. by rewrite/=sub0n zext0.
    rewrite/=. Abort.
   *)
  
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

  
  Lemma msb_sig_bits bs : msb bs -> sig_bits bs = size bs.
  Proof.
    rewrite -(revK bs). set bsr := rev bs.
    rewrite /msb.
    elim bsr; first done.
    move =>  bsrhd bsrtl IH.
    rewrite /splitmsb/=rev_cons lastd_rcons.
    case bsrhd; last done. by rewrite sig_bits_rcons1 size_rcons.
  Qed.

  Lemma sig_bits_gt0_size bs :
    0 < sig_bits bs -> 0 < size bs .
  Proof .
    elim : bs => [ | b bs IH _ ]; first done .
    by rewrite size_joinlsb addn1 ltn0Sn .
  Qed .

  Lemma size_gt0_case bs :
    0 < size bs ->
    exists cs, (bs == cs ++ [::true]) || (bs == cs ++ [::false]) .
  Proof .
    case : bs => [ | b bs Hsz ]; first done .
    exists (belast b bs) .
    rewrite lastI -!cats1 .
    case (last b bs);
      [ by apply /orP; left |
        by apply /orP; right ].
  Qed .

  Lemma sig_bits_cons1_rec: forall n (bs : seq bool) b, size bs = n -> 0 < sig_bits bs -> (sig_bits bs).+1 = (sig_bits (b :: bs)).
  Proof .
    elim => [ bs b | n IH bs b ] .
    - move => Hsz; by rewrite (size0nil Hsz) .
    - move => Hsz Hsigbits .
      move : (size_gt0_case (sig_bits_gt0_size Hsigbits));
        case => cs; case /orP => /eqP Hcs; rewrite !Hcs .
      + by rewrite /sig_bits -!cat_cons !rev_cat /= .
      + rewrite /sig_bits -!cat_cons !rev_cat !size_cat
                /= !addn1 !subn1 /= .
        have : (0 < sig_bits cs) .
        { move : Hsigbits; rewrite Hcs /sig_bits /= .
          by rewrite rev_cat /= size_cat /= addn1 subn1 . }
        move => Hsigbitscs .
        have : (size cs = n) .
        { move : Hsz; rewrite Hcs size_cat addn1 /=; apply eq_add_S . }
        move => Hszcs .
        move : (IH cs b Hszcs Hsigbitscs) .
        by rewrite /sig_bits size_joinlsb addn1 .
  Qed .
  
  Lemma sig_bits_cons1: forall (bs : seq bool) b, 0 < sig_bits bs -> (sig_bits bs).+1 = (sig_bits (b :: bs)).
  Proof.
    move => bs b Hsigbits .
    apply : (@sig_bits_cons1_rec (size bs)); done .
  Qed .
    
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

  Lemma rev_zip_zeros T (bs : seq T) :
    rev (zip (zeros (size bs)) bs) = zip (zeros (size bs)) (rev bs) .
  Proof .
    elim : bs => [|b bs IH]; first done .
    rewrite size_joinlsb addn1 -zeros_cons zip_cons rev_cons IH .
    rewrite -zip_rcons /=;
      last by rewrite size_zeros size_rev .
    by rewrite zeros_rcons -rev_cons zeros_cons .
  Qed .

  Lemma unzip1_zip_zeros T (bs : seq T) :
    unzip1 (zip (zeros (size bs)) bs) == zeros (size bs) .
  Proof .
    elim : bs => [|b bs IH]; first done .
    by rewrite size_joinlsb addn1 -zeros_cons zip_cons /= (eqP IH) .
  Qed .

  Lemma andb_orb_all_0l_rec b bs :
    andb_orb_all_zip (zip (zeros (size bs).+1) (b::bs)) ==
    andb_orb_all_zip (zip (zeros (size bs)) bs) .
  Proof .
    rewrite {1}/andb_orb_all_zip /= .
    rewrite (eqP (@unzip1_zip_zeros _ bs)) (orb_all_0) /= .
    rewrite -/andb_orb_all_zip .
    by case (andb_orb_all_zip (zip (zeros (size bs)) bs)) .
  Qed .

  Lemma andb_orb_all_zip_0l_ss : forall bs,
      andb_orb_all_zip (zip (zeros (size bs)) bs) = false.
  Proof .
    elim => [|rb rbs]; first done .
    rewrite size_joinlsb addn1 .
    by rewrite (eqP (@andb_orb_all_0l_rec _ _)) .
  Qed .

  Lemma andb_orb_all_0l : forall bs n, andb_orb_all (zeros n) bs = false.
  Proof.
    move => bs n .
    rewrite /andb_orb_all /extzip0 extzip_zip .
    rewrite size_rev size_zeros .
    rewrite zeros_cats .
    have : (n + (size bs - n) = size (rev bs ++ copy (n - size bs) b0)) .
    { by rewrite size_cat size_copy size_rev -!maxnE maxnC . } 
    case => -> .
    by rewrite andb_orb_all_zip_0l_ss .
  Qed .

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

  Lemma sig_bits_lsb1 bs : 0 < sig_bits (b1::bs) .
  Proof .
    case : bs => [|b bs]; first done .
    dcase (sig_bits (b::bs)); case => [Hsigbits | m Hsigbits] .
    - by rewrite -(sig_bits_consb _ Hsigbits) addn1 ltn0Sn . 
    - rewrite -(sig_bits_cons1); first by apply ltn0Sn .
      by rewrite Hsigbits ltn0Sn .
  Qed .

  Lemma head0_rev_sig_bits bs :
    head false (rev bs) -> 0 < sig_bits bs .
  Proof .
    elim : bs => [|b bs IH]; first done .
    case b => H .
    - apply : sig_bits_lsb1 .
    - rewrite head_rev in H .
      by rewrite -(sig_bits_cons1 _ (IH H)) ltn0Sn .
  Qed .

  Lemma orb_all_sig_bits bs :
    orb_all bs -> 0 < sig_bits bs .
  Proof .
    elim : bs => [|b bs IH]; first done .
    case b .
    - move => _; apply sig_bits_lsb1 .
    - rewrite /orb_all Bool.orb_false_r -/orb_all => H .
      by rewrite -(sig_bits_cons1 _ (IH H)) ltn0Sn .
  Qed .      

  Lemma behead_rev (b : bool) bs :
    behead (rev (b::bs)) = rev (belast b bs) .
  Proof .
    elim : bs b => [|c cs IH]; first done .
    move => b; rewrite !rev_cons /= -/belast .
    rewrite -(IH c) /= -rev_cons /= .
    dcase (rev (c::cs)); case; last done .
    move => Hnil .
    move : (rev_nil c cs) .
    by rewrite -Hnil eq_refl /= .
  Qed .

  Lemma orb_all_false_zeros bs :
    orb_all bs = false -> bs == zeros (size bs) .
  Proof .
    elim : bs => [|b bs IH]; first done .
    case b => /= .
    - by rewrite Bool.orb_true_r .
    - rewrite Bool.orb_false_r => Horb .
      by rewrite (eqP (IH Horb)) size_zeros .
  Qed .

  (*
  Lemma andb_orb_all_zip_
  Hhd : head false (rev cs1) = false
  ============================
  andb_orb_all_zip (extzip0 cs0 (behead (rev (false :: cs1)))) ->
   *)

  Lemma rev_zeros n :
    rev (zeros n) == zeros n .
  Proof .
    elim : n => [|n /eqP IH]; first done .
    by rewrite -zeros_cons rev_cons IH zeros_rcons .
  Qed .

  Lemma behead_zeros n :
    behead (zeros n) == zeros n.-1 .
  Proof .
    elim : n => [|n /eqP IH]; first done .
    by rewrite -zeros_cons /= .
  Qed .

  Lemma andb_orb_all_true_ss : forall bs1 bs2, size bs1 = size bs2 -> andb_orb_all bs1 bs2 -> (0 < sig_bits bs1) /\ (0 < sig_bits bs2).
  Proof .
    apply : seq_ind2; first done .
    move => c0 c1 cs0 cs1 Hszeq IH .
    case c0; case c1; rewrite /andb_orb_all /= rev_cons headI /=;
      try (rewrite Bool.orb_true_r || rewrite Bool.orb_false_r);
      try (rewrite Bool.andb_true_l);
      move => H; split; try apply sig_bits_lsb1 .
    - (* case 1 *)
      move : H; dcase (head false (rev cs1)); case => Hhd;
        [ rewrite Bool.orb_true_r => _;
          by rewrite -(sig_bits_cons1 _ (head0_rev_sig_bits Hhd)) ltn0Sn
        | rewrite Bool.orb_false_r => Htl ] .
      rewrite -sig_bits_cons1; first by rewrite ltn0Sn .
      dcase (0 < sig_bits cs1); case; first done .
      move => Hn0 .
      have : (sig_bits cs1 == 0) .
      { move : Hn0; by case (sig_bits cs1) . }
      move => /eqP Hszcs1 {Hn0} .
      move : Htl .
      have : (cs1 = zeros (size cs1)) .
      { apply sig_bits_is0; trivial . }
      case => -> .
      rewrite (eqP (@rev_zeros _)) zeros_rcons
              (eqP (@behead_zeros _)) -Hszeq /= .
      by rewrite -(andb_orb_all_0r cs0 (size cs0)) 
                 /andb_orb_all (eqP (@rev_zeros _)) .
    - (* case 2 *)
      move : H; dcase (orb_all (unzip1 (extzip0 cs0 (behead (rcons (rev cs1) true)))));
        case => Horb;
        [ rewrite Bool.andb_true_l => _;
          move : Horb;
          rewrite unzip1_extzip_ss;
          [ move => Horb;
            move : (orb_all_sig_bits Horb) => Hsigbits;
            by rewrite -(sig_bits_cons1 _ Hsigbits) ltn0Sn
          | by rewrite size_behead size_rcons size_rev -Hszeq ]
        | rewrite Bool.andb_false_l Bool.orb_false_r
                  -rev_cons behead_rev ] .
      move : Horb .
      rewrite /extzip0 extzip_zip_ss;
        last by rewrite size_behead size_rcons size_rev .
      rewrite unzip1_zip; 
        last by rewrite size_behead size_rcons size_rev -Hszeq .
      move => Hcs0; move : (orb_all_false_zeros Hcs0) => /eqP -> .
      have : (size cs0 = size (rev (belast true cs1))) .
      { by rewrite size_rev size_belast -Hszeq . }
      case => -> .
      rewrite extzip_zip_ss;
        last by rewrite !size_rev !size_belast size_zeros .
      by rewrite andb_orb_all_zip_0l_ss .
    - (* case 3 *)
      move : H; dcase (orb_all (unzip1 (extzip0 cs0 (behead (rcons (rev cs1) false)))));
        case => Horb;
        [ rewrite Bool.andb_true_l => _;
          move : Horb;
          rewrite unzip1_extzip_ss;
          [ move => Horb;
            move : (orb_all_sig_bits Horb) => Hsigbits;
            by rewrite -(sig_bits_cons1 _ Hsigbits) ltn0Sn
          | by rewrite size_behead size_rcons size_rev -Hszeq ]
        | rewrite Bool.andb_false_l Bool.orb_false_r
                  -rev_cons behead_rev ] .
      move : Horb .
      rewrite /extzip0 extzip_zip_ss;
        last by rewrite size_behead size_rcons size_rev .
      rewrite unzip1_zip; 
        last by rewrite size_behead size_rcons size_rev -Hszeq .
      move => Hcs0; move : (orb_all_false_zeros Hcs0) => /eqP -> .
      have : (size cs0 = size (rev (belast false cs1))) .
      { by rewrite size_rev size_belast -Hszeq . }
      case => -> .
      rewrite extzip_zip_ss;
        last by rewrite !size_rev !size_belast size_zeros .
      by rewrite andb_orb_all_zip_0l_ss .
    - (* case 4 *)
      move : H; dcase (head false (rev cs1)); case => Hhd;
        [ rewrite Bool.andb_true_r => _;
          by rewrite -(sig_bits_cons1 _ (head0_rev_sig_bits Hhd)) ltn0Sn
        | rewrite Bool.andb_false_r Bool.orb_false_r => Htl ] .
      rewrite -sig_bits_cons1; first by rewrite ltn0Sn .
      dcase (0 < sig_bits cs1); case; first done .
      move => Hn0 .
      have : (sig_bits cs1 == 0) .
      { move : Hn0; by case (sig_bits cs1) . }
      move => /eqP Hszcs1 {Hn0} .
      move : Htl .
      have : (cs1 = zeros (size cs1)) .
      { apply sig_bits_is0; trivial . }
      case => -> .
      rewrite (eqP (@rev_zeros _)) zeros_rcons
              (eqP (@behead_zeros _)) -Hszeq /= .
      by rewrite -(andb_orb_all_0r cs0 (size cs0)) 
                 /andb_orb_all (eqP (@rev_zeros _)) .
  Qed .

  Lemma sig_bits_zeros_cat m n bs :
    0 < sig_bits ((zeros m) ++ bs ++ (zeros n)) -> 0 < sig_bits bs .
  Proof .
    dcase (sig_bits bs); case; 
      last by (intros; rewrite ltn0Sn) .
    rewrite sig_bits_is0 => -> .
    by rewrite -!zeros_addn sig_bits_zeros .
  Qed .

  Lemma andb_orb_all_true : forall bs1 bs2, andb_orb_all bs1 bs2 -> (0 < sig_bits bs1) /\ (0 < sig_bits bs2).
  Proof.
    move => bs1 bs2 .
    rewrite /andb_orb_all /extzip0 extzip_zip .
    rewrite -(rev_copy (size bs1 - size (rev bs2))) -rev_cat .
    have : (size (bs1 ++ copy (size (rev bs2) - size bs1) b0)
            = size (copy (size bs1 - size (rev bs2)) b0 ++ bs2)) .
    { by rewrite !size_rev !size_cat !size_copy
                 (addnC (size bs1 - size bs2) (size bs2))
                 -!maxnE maxnC . }
    move => Hszeq .
    move : (andb_orb_all_true_ss Hszeq) .
    rewrite {1}/andb_orb_all /extzip0 extzip_zip_ss /=;
      last by rewrite Hszeq rev_cat !size_cat !size_rev (addnC) .
    move => Hss H .
    move : (Hss H) .
    elim; split .
    - apply : (@sig_bits_zeros_cat 0 (size (rev bs2) - size bs1) bs1) .
      by rewrite zeros0 cat0s .
    - apply : (@sig_bits_zeros_cat (size bs1 - size (rev bs2)) 0 bs2) .
      by rewrite zeros0 cats0 .
  Qed .
  
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

  Lemma andb_orb_all_sig_bits2 : forall bs1 bs2, size bs1 = size bs2 -> andb_orb_all (splitlsb bs1).2 (splitlsb bs2).2 = true -> size bs1 <= (sig_bits bs1) + (sig_bits bs2) -2.
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

    
  Lemma umulo_to_nat : forall bs1 bs2, size bs1 = size bs2 -> Umulo bs1 bs2 -> to_nat bs1 * (to_nat bs2) != to_nat (mulB bs1 bs2).
  Proof.
    move => bs1 bs2 Hsz. rewrite/Umulo neq_ltn. 
    move:  (upper_bound bs1). move:  (upper_bound bs2).
    rewrite 2!ltB_to_nat 2!to_nat_joinmsb 2!mul1n 2!size_zeros 2!to_nat_zeros 2!addn0.
    move => Hbd2 Hbd1.  move : (ltn_mul Hbd1 Hbd2)=> Hmulbd. rewrite -expnD in Hmulbd. 
    move/orP=> [Haoa|Hmsb].
    - move : (andb_orb_all_sig_bits2 Hsz Haoa). 
      move : (andb_orb_all_true Haoa) => [Hgt01 Hgt02].
      move : (sig_bits_cons (splitlsb bs1).1 (splitlsb bs1).2) => Hgec1.
      move : (sig_bits_cons (splitlsb bs2).1 (splitlsb bs2).2) => Hgec2.
      move : (ltn_leq_trans Hgt01 Hgec1) => Hgtc1. move : (ltn_leq_trans Hgt02 Hgec2) => Hgtc2.
      move : (sig_bits_le (splitlsb bs1).2) => Hsz1. move : (sig_bits_le (splitlsb bs2).2) => Hsz2.
      move : (ltn_leq_trans Hgt01 Hsz1) => Hgtsz1. move : (ltn_leq_trans Hgt02 Hsz2) => Hgtsz2.
      rewrite size_splitlsb subn_gt0 in Hgtsz1; rewrite size_splitlsb subn_gt0 in Hgtsz2.
      move : (ltn_trans (ltn0Sn 0) Hgtsz1) => Hszgt01.
      move : (ltn_trans (ltn0Sn 0) Hgtsz2) =>Hszgt02.
      rewrite -/joinlsb joinlsb_splitlsb in Hgec1; last by rewrite Hszgt01.
      rewrite -/joinlsb joinlsb_splitlsb in Hgec2; last by rewrite Hszgt02.
      move => Hsub2.
      have ->: to_nat bs1 = to_nat (ucastB bs1 (sig_bits bs1)) by rewrite sig_bits_to_nat.
      have ->: to_nat bs2 = to_nat (ucastB bs2 (sig_bits bs2)) by rewrite sig_bits_to_nat.
      rewrite -/joinlsb joinlsb_splitlsb in Hgtc1; last by rewrite Hszgt01.
      rewrite -/joinlsb joinlsb_splitlsb in Hgtc2; last by rewrite Hszgt02.
      move : (ltn_addl (size bs2) Hgtsz2) => Hadd.
      move : (lower_bound Hgtc1). move : (lower_bound Hgtc2).
      rewrite 2!ltB_to_nat 2!to_nat_joinmsb 2!mul1n 2!size_zeros 2!to_nat_zeros 2!addn0.
      move => Hlbd2 Hlbd1. move : (ltn_mul Hlbd1 Hlbd2)=> Hmullbd. rewrite -expnD in Hmullbd.
      move : (leq_mod (to_nat bs1 * to_nat bs2) (2 ^ size bs1 )) =>Hleqmod.
      rewrite /ucastB to_nat_mulB to_nat_from_nat. apply /orP; right.
      move : (exp2n_gt0 (size bs1)) => Hszexpgt01.
      have Haux : (size bs1  <=((sig_bits bs1).-1 + (sig_bits bs2).-1))
        by rewrite addnC -subn1 (addnBAC _ Hgtc2) -subn1 (addnBA _ Hgtc1) 2!subn1 -subn2 addnC Hsub2.
      move : (leq_pexp2l (ltn0Sn 1) Haux) => Hexp2n.
      move : (leq_ltn_trans Hexp2n Hmullbd) => Hlt.
      case Heq1 : (sig_bits bs1 == size bs1); case Heq2 : (sig_bits bs2 == size bs2).
      + rewrite leq_eqVlt in Hleqmod. move/orP : Hleqmod => [Heqmod|Hltmod].
        move : (modn_neq Hszexpgt01 (ltnW Hlt)) => Hneq. by rewrite Heqmod in Hneq.
        exact.
      + move :(sig_bits_le bs2) => Hsigle2. 
        move : (ltn_neqAle (sig_bits bs2) (size bs2)). rewrite Heq2 Hsigle2/=. move => Hcond2.
        rewrite Hcond2.
        rewrite /low to_nat_cat to_nat_zeros mul0n to_nat_take Hcond2 addn0 (to_nat_from_nat_bounded Hbd2).
        rewrite leq_eqVlt in Hleqmod. move/orP : Hleqmod => [Heqmod|Hltmod].
        move : (modn_neq Hszexpgt01 (ltnW Hlt)) => Hneq. by rewrite Heqmod in Hneq.
        exact.
      + move :(sig_bits_le bs1) => Hsigle1. 
        move : (ltn_neqAle (sig_bits bs1) (size bs1)). rewrite Heq1 Hsigle1/=. move => Hcond1.
        rewrite Hcond1.
        rewrite /low to_nat_cat to_nat_zeros mul0n to_nat_take Hcond1 addn0 (to_nat_from_nat_bounded Hbd1).
        rewrite leq_eqVlt in Hleqmod. move/orP : Hleqmod => [Heqmod|Hltmod].
        move : (modn_neq Hszexpgt01 (ltnW Hlt)) => Hneq. by rewrite Heqmod in Hneq.
        exact.
      + move :(sig_bits_le bs1) => Hsigle1. 
        move : (ltn_neqAle (sig_bits bs1) (size bs1)). rewrite Heq1 Hsigle1/=. move => Hcond1.
        rewrite Hcond1.
        move :(sig_bits_le bs2) => Hsigle2. 
        move : (ltn_neqAle (sig_bits bs2) (size bs2)). rewrite Heq2 Hsigle2/=. move => Hcond2.
        rewrite Hcond2.
        rewrite 2!/low 2!to_nat_cat 2!to_nat_zeros 2!mul0n 2!to_nat_take Hcond1 Hcond2 (to_nat_from_nat_bounded Hbd1) (to_nat_from_nat_bounded Hbd2) 2!addn0.
        rewrite leq_eqVlt in Hleqmod. move/orP : Hleqmod => [Heqmod|Hltmod].
        move : (modn_neq Hszexpgt01 (ltnW Hlt)) => Hneq. by rewrite Heqmod in Hneq.
        exact.
    - move : (msb_sig_bits Hmsb). rewrite size_mulB size_zext. move => Hsigmul.
      apply /orP; right.
      rewrite to_nat_mulB to_nat_from_nat. 
      have Hsbgt0 : 0 < (sig_bits (zext 1 bs1 *# zext 1 bs2)) by rewrite Hsigmul addn1 ltn0Sn.
      move : (lower_bound Hsbgt0). rewrite ltB_to_nat.
      rewrite to_nat_joinmsb size_zeros Hsigmul to_nat_zeros to_nat_zext addn0 -subn1 addnK mul1n.
      rewrite to_nat_take size_full_mul !size_zext . 
      have : (0 < (size bs2) +1) by rewrite addn1 ltn0Sn. rewrite -(ltn_add2l (size bs1 +1)) addn0. move => Hcond.
      rewrite Hcond to_nat_full_mul !to_nat_zext size_full_mul !size_zext. 
      rewrite to_nat_from_nat to_nat_from_nat_bounded. move => Hexp2n.
      move : (leq_mod (to_nat bs1 * to_nat bs2) (2 ^ (size bs1 +1))) =>Hleqmod1.
      move : (ltn_leq_trans Hexp2n Hleqmod1) => Hlt.
      move : (modn_neq (exp2n_gt0 (size bs1)) (ltnW Hlt)) => Hneq.
      move : (leq_mod (to_nat bs1 * to_nat bs2) (2 ^ (size bs1))) =>Hleqmod.
      rewrite leq_eqVlt in Hleqmod. move/orP : Hleqmod => [Heqmod|Hltmod].
      rewrite Heqmod in Hneq. done.
      exact.
      move : (leq_add (sig_bits_le bs1) (sig_bits_le bs2)).
      rewrite -ltnS. move/ltnW => Hadd2. rewrite -ltnS in Hadd2.
      rewrite -(ltn_exp2l _ _ (ltnSn 1)) in Hadd2.
      rewrite 2!addn1 addnS addSn.
      exact : (ltn_trans Hmulbd Hadd2).
  Qed.
      

  (* Lemmas used in coq-cryptoline *)

  Lemma bv2z_shl_unsigned bs n :
    high n bs == zeros n ->
    to_Zpos (bs <<# n)%bits = (to_Zpos bs * 2 ^ Z.of_nat n)%Z.
  Proof. 
    move/eqP=> Hhighn. case/orP: (leq_total n (size bs)) => Hsz.
    - rewrite (shlB_cat Hsz) to_Zpos_cat to_Zpos_zeros size_zeros Z.add_0_l.
      rewrite high_zeros_to_Zpos_low_eq; last by rewrite (subKn Hsz). 
      reflexivity.
    - rewrite (shlB_oversize Hsz) to_Zpos_zeros. 
      apply (f_equal (high (size bs))) in Hhighn. 
      rewrite (high_high _ Hsz) high_size high_zeros in Hhighn.
      by rewrite Hhighn to_Zpos_zeros Z.mul_0_l.
  Qed.

  Lemma bv2z_shl_signed_high_zeros bs n :
    (high (n + 1) bs == zeros (n + 1)) ->
    to_Z (bs <<# n)%bits = (to_Z bs * 2 ^ Z.of_nat n)%Z.
  Proof.
    move/eqP=> HhSn. case/orP: (ltn_geq_total n (size bs)) => Hsz.
    - rewrite (shlB_cat (ltnW Hsz)). 
      rewrite to_Z_cat; last by rewrite size_low subn_gt0. 
      rewrite to_Zpos_zeros size_zeros Z.add_0_l. 
      have Hh1l : high 1 (low (size bs - n) bs) = [:: b0].
      { 
        rewrite high_low; [ | by rewrite subn_gt0 | exact: leq_subr].
        by rewrite (subKn (ltnW Hsz)) HhSn low_zeros. 
      }
      have Hh1bs : high 1 bs = [:: b0].
      { by rewrite -(high_high bs (leq_addl n 1)) HhSn high_zeros. }
      apply (f_equal (high n)) in HhSn. 
      rewrite (high_high bs (leq_addr 1 n)) high_zeros in HhSn.
      rewrite (high1_0_to_Z Hh1l) (high1_0_to_Z Hh1bs) high_zeros_to_Zpos_low_eq. 
      + reflexivity.
      + rewrite subKn; [done | by apply ltnW].
    - apply (f_equal (high n)) in HhSn. 
      rewrite (high_high bs (leq_addr 1 n)) high_zeros in HhSn.
      rewrite (high_oversize_zeros Hsz HhSn).
      by rewrite shlB_zeros to_Z_zeros Z.mul_0_l.
  Qed.

  Lemma bv2z_shl_signed_high_ones bs n :
    (high (n + 1) bs == ones (n + 1)) ->
    to_Z (bs <<# n)%bits = (to_Z bs * 2 ^ Z.of_nat n)%Z.
  Proof.
    move=> HhSn. move: HhSn (high_ones_le_size HhSn). 
    rewrite {3}addn1 => /eqP HhSn Hsz. rewrite (shlB_cat (ltnW Hsz)). 
    rewrite to_Z_cat; last by rewrite size_low subn_gt0. 
    rewrite to_Zpos_zeros size_zeros Z.add_0_l. 
    have Hh1l : high 1 (low (size bs - n) bs) = [:: b1].
    { 
      rewrite high_low; [ | by rewrite subn_gt0 | exact: leq_subr].
      rewrite (subKn (ltnW Hsz)) HhSn low1_lsb lsb_ones; last by rewrite addn1. 
      reflexivity.
    }
    have Hh1bs : high 1 bs = [:: b1].
    { 
      rewrite -(high_high bs (leq_addl n 1)) HhSn high1_msb.
      rewrite msb_ones; last by rewrite addn1. reflexivity. 
    }
    apply (f_equal (high n)) in HhSn. 
    rewrite (high_high bs (leq_addr 1 n)) addn1 -ones_cons high_cons in HhSn;
      last by rewrite size_ones.
    rewrite (high1_1_to_Z Hh1l) (high1_1_to_Z Hh1bs) high_ones_to_Zneg_low_eq. 
    - reflexivity. 
    - exact: leq_subr.
    - rewrite subKn; 
        [by rewrite -{2}(size_ones n) high_size in HhSn | by apply ltnW].
  Qed.

  Lemma bv2z_shl_signed bs n :
    (high (n + 1) bs == zeros (n + 1)) || (high (n + 1) bs == ones (n + 1)) ->
    to_Z (bs <<# n)%bits = (to_Z bs * 2 ^ Z.of_nat n)%Z.
  Proof.
    case/orP.
    - exact: bv2z_shl_signed_high_zeros.
    - exact: bv2z_shl_signed_high_ones.
  Qed.

  Lemma bv2z_cshl_unsigned bsh bsl n :
    size bsh = size bsl ->
    high n (bsl ++ bsh) == zeros n ->
    (to_Zpos (low (size bsl) ((bsl ++ bsh) <<# n) >># n)%bits * 2 ^ Z.of_nat n +
     to_Zpos (high (size bsh) ((bsl ++ bsh) <<# n)%bits) * 2 ^ Z.of_nat (size bsl))%Z =
    ((to_Zpos bsh * 2 ^ Z.of_nat (size bsl) + to_Zpos bsl) * 2 ^ Z.of_nat n)%Z.
  Proof.
    move=> _ Hzeros.
    rewrite [in RHS]Z.add_comm -to_Zpos_cat -(bv2z_shl_unsigned Hzeros). 
    rewrite -bv2z_shl_unsigned; last by rewrite high_shrB.
    rewrite shrB_shlB_cancel. 
    - rewrite -to_Zpos_low_high; [reflexivity | by rewrite size_shlB size_cat].
    - case/orP: (leq_total n (size bsl)) => Hn.
      + by rewrite (low_low _ Hn) low_shlB_ss.
      + by rewrite (low_shlB _ Hn) low_zeros.
  Qed.

  Lemma bv2z_cshl_signed bsh bsl n :
    size bsh = size bsl ->
    (high (n + 1) (bsl ++ bsh) == zeros (n + 1))
    || (high (n + 1) (bsl ++ bsh) == ones (n + 1)) ->
    (to_Zpos (low (size bsl) ((bsl ++ bsh) <<# n) >># n)%bits * 2 ^ Z.of_nat n +
     to_Z (high (size bsh) ((bsl ++ bsh) <<# n)%bits) * 2 ^ Z.of_nat (size bsl))%Z =
    ((to_Z bsh * 2 ^ Z.of_nat (size bsl) + to_Zpos bsl) * 2 ^ Z.of_nat n)%Z.
  Proof.
    case Hsh : (size bsh) => [| m].
    - move=> Hsl. apply Logic.eq_sym in Hsl. 
      rewrite (eqP (size0 Hsh)) (eqP (size0 Hsl)) /=. 
      by rewrite low0 high0 shrB_nil to_Z_nil to_Zpos_nil !Z.mul_0_l Z.add_0_l.
    - move: (ltn0Sn m). rewrite -Hsh => {Hsh} Hsh _ HhSn.
      rewrite [in RHS]Z.add_comm -(to_Z_cat _ Hsh) -(bv2z_shl_signed HhSn). 
      rewrite -bv2z_shl_unsigned; last by rewrite high_shrB.
      rewrite shrB_shlB_cancel. 
      + rewrite -(to_Z_low_high Hsh); 
          [reflexivity | by rewrite size_shlB size_cat].
      + case/orP: (leq_total n (size bsl)) => Hn.
        * by rewrite (low_low _ Hn) low_shlB_ss.
        * by rewrite (low_shlB _ Hn) low_zeros.
  Qed.

  Lemma bv2z_not_unsigned bs :
    to_Zpos (~~# bs)%bits = (2 ^ Z.of_nat (size bs) - Z.one - to_Zpos bs)%Z.
  Proof.
    exact: to_Zpos_invB_full.
  Qed.

  Lemma bv2z_not_signed bs :
    0 < size bs -> to_Z (~~# bs)%bits = (- to_Z bs - Z.one)%Z.
  Proof.
    case: (lastP bs) => {bs} [| bs b] //= => Hsz.
    rewrite invB_rcons !to_Z_rcons. case b => /=.
    - rewrite to_Zpos_invB Z.opp_involutive Z.sub_succ_l Z.sub_1_r Z.succ_pred. 
      reflexivity.
    - rewrite to_Zneg_invB Z.opp_succ Z.sub_1_r. reflexivity.
  Qed. 

  Lemma bv2z_add_unsigned bs1 bs2 :
    size bs1 = size bs2 -> ~~ carry_addB bs1 bs2 ->
    to_Zpos (bs1 +# bs2)%bits = (to_Zpos bs1 + to_Zpos bs2)%Z.
  Proof.
    move=> Hsz Hov. move/Z.add_move_r: (to_Zpos_addB Hsz) => ->.
    apply negbTE in Hov. rewrite Hov Z.mul_0_l Z.sub_0_r. reflexivity.
  Qed.

  Lemma bv2z_add_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Saddo bs1 bs2 ->
    to_Z (bs1 +# bs2)%bits = (to_Z bs1 + to_Z bs2)%Z.
  Proof.
    move=> Hsz. rewrite /Saddo 3!to_Z_to_Zpos size_addB Hsz minnn.
    have Hmsb : forall bs, (splitmsb bs).2 = msb bs by rewrite /msb. rewrite !Hmsb.
    move/Z.add_move_r: (to_Zpos_addB Hsz) => ->. 
    rewrite (carry_addB_eq_msbs Hsz) Hsz.
    case (msb bs1); case (msb bs2); case (msb (bs1 +# bs2)); 
      rewrite ?Z.mul_0_l ?Z.mul_1_l ?Z.sub_0_r //=; by omega. 
  Qed.

  Lemma bv2z_adds_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos (bs1 +# bs2)%bits +
     odd (carry_addB bs1 bs2) * 2 ^ Z.of_nat (size bs1))%Z =
    (to_Zpos bs1 + to_Zpos bs2)%Z.
  Proof.
    have->: odd (carry_addB bs1 bs2) = carry_addB bs1 bs2 
      by case (carry_addB bs1 bs2).
    exact: to_Zpos_addB.
  Qed.

  Lemma bv2z_adds_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Saddo bs1 bs2 ->
    to_Z (bs1 +# bs2)%bits = (to_Z bs1 + to_Z bs2)%Z.
  Proof.
    exact: bv2z_add_signed.
  Qed.

  Lemma bv2z_adc_unsigned bs1 bs2 bsc :
    0 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ carry_addB bs1 bs2 &&
    ~~ carry_addB (bs1 +# bs2)%bits (zext (size bs1 - 1) bsc) ->
    to_Zpos (adcB (to_bool bsc) bs1 bs2).2 =
    (to_Zpos bs1 + to_Zpos bs2 + to_Zpos bsc)%Z.
  Proof.
    move=> Hsz0 Hsz Hc. rewrite (size1_lsb Hc) => /andP [Hov1 Hov2].
    rewrite (adcB_addB_addB _ Hsz0 Hsz).
    have->: to_bool [:: lsb bsc] = lsb bsc by case (lsb bsc).
    rewrite (bv2z_add_unsigned _ Hov2); 
      last by rewrite size_addB -Hsz minnn size_zext /= addnC (subnK Hsz0).
    rewrite to_Zpos_zext (bv2z_add_unsigned Hsz Hov1). reflexivity.
  Qed.

  Lemma bv2z_adc_signed bs1 bs2 bsc :
    1 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Saddo bs1 bs2 &&
    ~~ Saddo (bs1 +# bs2)%bits (zext (size bs1 - 1) bsc) ->
    to_Z (adcB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 + to_Z bs2 + to_Zpos bsc)%Z.
  Proof.
    move=> Hsz1 Hsz Hc. rewrite (size1_lsb Hc) => /andP [Hov1 Hov2].
    have Hsz0 : 0 < size bs1 by apply (@ltn_trans 1). 
    rewrite (adcB_addB_addB _ Hsz0 Hsz).
    have->: to_bool [:: lsb bsc] = lsb bsc by case (lsb bsc).
    rewrite (bv2z_add_signed _ Hov2); 
      last by rewrite size_addB -Hsz minnn size_zext /= addnC (subnK Hsz0).
    rewrite to_Z_zext; last by rewrite -subn_gt0 in Hsz1.
    rewrite (bv2z_add_signed Hsz Hov1). reflexivity.
  Qed.

  Lemma bv2z_adcs_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    (to_Zpos (adcB (to_bool bsc) bs1 bs2).2 +
     odd (adcB (to_bool bsc) bs1 bs2).1 * 2 ^ Z.of_nat (size bs1))%Z =
    (to_Zpos bs1 + to_Zpos bs2 + to_Zpos bsc)%Z.
  Proof.
    move=> Hsz. case: bsc => [|c tl] //=.
    move/eqP; rewrite eqSS; move/eqP => Htl. apply size0 in Htl. 
    rewrite (eqP Htl) /= Z.add_0_r. 
    have->: odd (adcB (to_bool [::c]) bs1 bs2).1 = (adcB (to_bool [::c]) bs1 bs2).1
      by case (adcB (to_bool [::c]) bs1 bs2).1.
    rewrite (to_Zpos_adcB _ Hsz) [in RHS]Z.add_comm Z.add_assoc. by case c.
  Qed.

  Lemma bv2z_adcs_signed bs1 bs2 bsc :
    1 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Saddo bs1 bs2 && ~~ Saddo (bs1 +# bs2)%bits (zext (size bs1 - 1) bsc) ->
    to_Z (adcB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 + to_Z bs2 + to_Zpos bsc)%Z.
  Proof.
    exact: bv2z_adc_signed.
  Qed.

  Lemma bv2z_sub_unsigned bs1 bs2 :
    size bs1 = size bs2 -> ~~ borrow_subB bs1 bs2 ->
    to_Zpos (bs1 -# bs2)%bits = (to_Zpos bs1 - to_Zpos bs2)%Z.
  Proof.
    move=> Hsz Hov. by rewrite (to_Zpos_subB Hsz) (negbTE Hov) Z.mul_0_l Z.add_0_l.
  Qed.

  Lemma bv2z_sub_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Ssubo bs1 bs2 ->
    to_Z (bs1 -# bs2)%bits = (to_Z bs1 - to_Z bs2)%Z.
  Proof.
    move=> Hsz. rewrite /Ssubo 3!to_Z_to_Zpos size_subB Hsz minnn.
    have Hmsb : forall bs, (splitmsb bs).2 = msb bs by rewrite /msb. 
    rewrite !Hmsb (to_Zpos_subB Hsz) (borrow_subB_eq_msbs Hsz) Hsz.
    case (msb bs1); case (msb bs2); case (msb (bs1 -# bs2));
      rewrite ?Z.mul_0_l ?Z.mul_1_l ?Z.sub_0_r //=; by omega. 
  Qed.

  Lemma bv2z_subc_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos bs1 - to_Zpos bs2 +
     (1 - odd (adcB true bs1 (~~# bs2)).1) * 2 ^ Z.of_nat (size bs1))%Z =
    to_Zpos (adcB true bs1 (~~# bs2)).2.
  Proof.
    move=> Hsz.
    rewrite adcB_fst_sbbB adcB_snd_sbbB sub1oddb Bool.negb_involutive invB_involutive
            /negb (to_Zpos_sbbB _ Hsz) Z.sub_0_r.
    by omega.
  Qed.

  Lemma bv2z_subc_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Ssubo bs1 bs2 ->
    to_Z (adcB true bs1 (~~# bs2)).2 = (to_Z bs1 - to_Z bs2)%Z.
  Proof.
    move=> Hsz Hov. rewrite -(bv2z_sub_signed Hsz Hov) /subB /sbbB /negb. 
    by case (adcB true bs1 (~~# bs2)).
  Qed.

  Lemma bv2z_subb_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos bs1 - to_Zpos bs2 +
     odd (borrow_subB bs1 bs2) * 2 ^ Z.of_nat (size bs1))%Z =
    to_Zpos (bs1 -# bs2)%bits.
  Proof.
    move=> Hsz. rewrite (to_Zpos_subB Hsz) Z.add_comm oddb Z.add_sub_assoc.
    reflexivity.
  Qed.

  Lemma bv2z_subb_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Ssubo bs1 bs2 ->
    to_Z (bs1 -# bs2)%bits = (to_Z bs1 - to_Z bs2)%Z.
  Proof.
    exact: bv2z_sub_signed.
  Qed.

  Lemma bv2z_sbc_unsigned bs1 bs2 bsc :
    0 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ borrow_subB bs1 bs2 &&
    ~~ borrow_subB (bs1 -# bs2)%bits (zext (size bs1 - 1)  ([:: b1] -# bsc)%bits) ->
    to_Zpos (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (to_Zpos bs1 - to_Zpos bs2 - (1 - to_Zpos bsc))%Z.
  Proof.
    move=> Hsz0 Hsz Hc. rewrite (size1_lsb Hc) => /andP [Hov1 Hov2].
    rewrite adcB_snd_sbbB invB_involutive (sbbB_subB_subB _ Hsz0 Hsz).
    have->: [:: ~~ to_bool [:: lsb bsc]] = [:: b1] -# [:: lsb bsc] by case (lsb bsc).
    rewrite (bv2z_sub_unsigned _ Hov2); 
      last by rewrite size_zext !size_subB -Hsz /= !minnn addnC (subnK Hsz0).
    rewrite to_Zpos_zext (bv2z_sub_unsigned Hsz Hov1).
    have->: to_Zpos ([:: b1] -# [:: lsb bsc]) = (1 - to_Zpos [:: lsb bsc])%Z
      by case (lsb bsc).
    reflexivity.    
  Qed.

  Lemma bv2z_sbc_signed bs1 bs2 bsc :
    1 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 &&
    ~~ Ssubo (bs1 -# bs2)%bits (zext (size bs1 - 1) ([:: b1] -# bsc)%bits) ->
    to_Z (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (to_Z bs1 - to_Z bs2 - (1 - to_Zpos bsc))%Z.
  Proof.
    move=> Hsz1 Hsz Hc. rewrite (size1_lsb Hc) => /andP [Hov1 Hov2].
    have Hsz0 : 0 < size bs1 by apply (@ltn_trans 1). 
    rewrite adcB_snd_sbbB invB_involutive (sbbB_subB_subB _ Hsz0 Hsz).
    have->: [:: ~~ to_bool [:: lsb bsc]] = [:: b1] -# [:: lsb bsc] by case (lsb bsc).
    rewrite (bv2z_sub_signed _ Hov2);
      last by rewrite size_zext !size_subB -Hsz /= !minnn addnC (subnK Hsz0).
    rewrite to_Z_zext; last by rewrite -subn_gt0 in Hsz1.
    rewrite (bv2z_sub_signed Hsz Hov1). 
    have->: to_Zpos ([:: b1] -# [:: lsb bsc]) = (1 - to_Zpos [:: lsb bsc])%Z
      by case (lsb bsc).
    reflexivity.    
  Qed.

  Lemma bv2z_sbcs_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    (to_Zpos bs1 - to_Zpos bs2 - (1 - to_Zpos bsc) +
     (1 - odd (adcB (to_bool bsc) bs1 (~~# bs2)%bits).1) * 2 ^ Z.of_nat (size bs1))%Z =
    to_Zpos (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2.
  Proof.
    rewrite adcB_fst_sbbB adcB_snd_sbbB sub1oddb Bool.negb_involutive 
            invB_involutive => Hsz Hc.
    rewrite (to_Zpos_sbbB _ Hsz) (size1_lsb Hc).
    have->: Z.b2z (~~ to_bool [:: lsb bsc]) = (1 - to_Zpos [:: lsb bsc])%Z 
      by case (lsb bsc).
    by omega.
  Qed.

  Lemma bv2z_sbcs_signed bs1 bs2 bsc :
    1 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (bs1 -# bs2)%bits
                           (zext (size bs1 - 1) ([:: b1] -# bsc)%bits) ->
    to_Z (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (to_Z bs1 - to_Z bs2 - (1 - to_Zpos bsc))%Z.
  Proof.
    exact: bv2z_sbc_signed.
  Qed.

  Lemma bv2z_sbb_unsigned bs1 bs2 bsc :
    0 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ borrow_subB bs1 bs2 &&
    ~~ borrow_subB (bs1 -# bs2)%bits (zext (size bs1 - 1) bsc) ->
    to_Zpos (sbbB (to_bool bsc) bs1 bs2).2 =
    (to_Zpos bs1 - to_Zpos bs2 - to_Zpos bsc)%Z.
  Proof.
    move=> Hsz0 Hsz Hc. rewrite (size1_lsb Hc) => /andP [Hov1 Hov2].
    rewrite (sbbB_subB_subB _ Hsz0 Hsz).
    have->: to_bool [:: lsb bsc] = lsb bsc by case (lsb bsc).
    rewrite (bv2z_sub_unsigned _ Hov2); 
      last by rewrite size_subB -Hsz minnn size_zext /= addnC (subnK Hsz0).
    rewrite to_Zpos_zext (bv2z_sub_unsigned Hsz Hov1). reflexivity.
  Qed.

  Lemma bv2z_sbb_signed bs1 bs2 bsc :
    1 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (bs1 -# bs2)%bits (zext (size bs1 - 1) bsc) ->
    to_Z (sbbB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 - to_Z bs2 - to_Zpos bsc)%Z.
  Proof.
    move=> Hsz1 Hsz Hc. rewrite (size1_lsb Hc) => /andP [Hov1 Hov2].
    have Hsz0 : 0 < size bs1 by apply (@ltn_trans 1). 
    rewrite (sbbB_subB_subB _ Hsz0 Hsz).
    have->: to_bool [:: lsb bsc] = lsb bsc by case (lsb bsc).
    rewrite (bv2z_sub_signed _ Hov2); 
      last by rewrite size_subB -Hsz minnn size_zext /= addnC (subnK Hsz0).
    rewrite to_Z_zext; last by rewrite -subn_gt0 in Hsz1.
    rewrite (bv2z_sub_signed Hsz Hov1). reflexivity.
  Qed.

  Lemma bv2z_sbbs_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    (to_Zpos (sbbB (to_bool bsc) bs1 bs2).2 +
     - odd (sbbB (to_bool bsc) bs1 bs2).1 * 2 ^ Z.of_nat (size bs1))%Z =
    (to_Zpos bs1 - to_Zpos bs2 - to_Zpos bsc)%Z.
  Proof.
    move=> Hsz Hc. rewrite (size1_lsb Hc) oddb (to_Zpos_sbbB _ Hsz) Z.mul_opp_l.
    have->: Z.b2z (to_bool [:: lsb bsc]) = to_Zpos [:: lsb bsc] by case (lsb bsc).  
    case (sbbB (to_bool [:: lsb bsc]) bs1 bs2).1; rewrite ?Z.mul_0_l ?Z.mul_1_l;
      by omega.
  Qed.

  Lemma bv2z_sbbs_signed bs1 bs2 bsc :
    1 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (bs1 -# bs2)%bits (zext (size bs1 - 1) bsc) ->
    to_Z (sbbB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 - to_Z bs2 - to_Zpos bsc)%Z.
  Proof.
    exact: bv2z_sbb_signed.
  Qed.

  Lemma bv2z_mul_unsigned bs1 bs2 :
    size bs1 = size bs2 -> ~~ Umulo bs1 bs2 ->
    to_Zpos (bs1 *# bs2)%bits = (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_mul_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Smulo bs1 bs2 ->
    to_Z (bs1 *# bs2)%bits = (to_Z bs1 * to_Z bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_mull_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos (low (size bs2) (full_mul bs1 bs2)) +
     to_Zpos (high (size bs1) (full_mul bs1 bs2)) * 2 ^ Z.of_nat (size bs2))%Z =
    (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_mull_signed bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos (low (size bs2) (full_mul bs1 bs2)) +
     to_Z (high (size bs1) (full_mul bs1 bs2)) * 2 ^ Z.of_nat (size bs2))%Z =
    (to_Z bs1 * to_Z bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_mulj_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    to_Zpos (full_mul bs1 bs2) = (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_mulj_signed bs1 bs2 :
    size bs1 = size bs2 ->
    to_Z (full_mul bs1 bs2) = (to_Z bs1 * to_Z bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_split_unsigned bs n :
    (to_Zpos (bs <<# (size bs - n) >># (size bs - n))%bits +
     to_Zpos (bs >># n)%bits * 2 ^ Z.of_nat n)%Z = to_Zpos bs.
  Proof.
    case/orP: (leq_total n (size bs)) => Hsz.
    - rewrite shlB_cat; last exact: leq_subr. 
      rewrite shrB_cat size_cat size_zeros; last exact: leq_addr.
      rewrite (shrB_cat Hsz) size_low (subKn Hsz) addnC addnK.
      rewrite high_size_cat; last by rewrite size_low.
      rewrite 2!to_Zpos_cat 2!to_Zpos_zeros !Z.mul_0_l !Z.add_0_r.
      rewrite (@to_Zpos_low_high bs n ((size bs) - n)); last exact: (subnKC Hsz).
      reflexivity.
    - rewrite (shrB_oversize Hsz) to_Zpos_zeros Z.mul_0_l Z.add_0_r.
      rewrite -subn_eq0 in Hsz. rewrite (eqP Hsz) /=. reflexivity.
  Qed.

  Lemma bv2z_split_signed bs n :
    n <= size bs ->
    (to_Zpos (bs <<# (size bs - n) >># (size bs - n))%bits +
     to_Z (sarB n bs) * 2 ^ Z.of_nat n)%Z = to_Z bs.
  Proof.
    move=> Hsz. rewrite shlB_cat; last exact: leq_subr. 
    rewrite shrB_cat size_cat size_zeros; last exact: leq_addr.
    rewrite (sarB_cat Hsz) size_low (subKn Hsz) addnC addnK.
    rewrite high_size_cat; last by rewrite size_low.
    rewrite to_Zpos_cat to_Zpos_zeros Z.mul_0_l Z.add_0_r.
    move: Hsz; case: n => [| n] => Hsz.
    - rewrite low0 subn0 high_size /= cats0 Z.mul_1_r. reflexivity.
    - move: Hsz; set m := n.+1; move=> Hsz.
      rewrite to_Z_cat; last by rewrite size_copy. 
      rewrite to_Z_copy; last done.
      rewrite Z.mul_add_distr_r Z.add_assoc size_high.
      rewrite -(@to_Zpos_low_high bs m (size bs - m)); last exact: (subnKC Hsz).
      rewrite -Z.mul_assoc -Z.pow_add_r; try by apply Nat2Z.is_nonneg.
      rewrite -Nat2Z.inj_add.
      have->: (size bs - m + m)%coq_nat = size bs - m + m by reflexivity.
      rewrite (subnK Hsz) Z.mul_opp_l Z.add_opp_r to_Z_to_Zpos. reflexivity.
  Qed.

  Lemma bv2z_cast_uuu bs n :
    size bs < n -> to_Zpos (zext (n - size bs) bs) = to_Zpos bs.
  Proof.
    move=> Hsz. exact: to_Zpos_zext.
  Qed.
 
  Lemma bv2z_cast_duu bs n q r  :
    n < size bs -> Z.div_eucl (to_Zpos bs) (2 ^ Z.of_nat n) = (q, r) ->
    (to_Zpos (low n bs) + q * 2 ^ Z.of_nat n)%Z = to_Zpos bs.
  Proof.
    move=> Hsz. rewrite to_Zpos_div_eucl_pow2. case=> <- _. 
    rewrite (@to_Zpos_low_high bs n (size bs - n)); last exact: (subnKC (ltnW Hsz)).
    reflexivity.
  Qed.

  Lemma bv2z_cast_usu_eq bs q r :
    Z.div_eucl (to_Z bs) (2 ^ Z.of_nat (size bs)) = (q, r) ->
    (to_Z bs + - q * 2 ^ Z.of_nat (size bs))%Z = to_Zpos bs.
  Proof.
    move=> H.
    move: (Z.div_eucl_eq (to_Z bs) _ (@pow2_nat2z_nonzero (size bs))).
    rewrite H. rewrite eta_expand_Z_div_eucl in H. case: H => _ <- ->.
    rewrite Z.mul_comm Z.mul_opp_l Z.add_opp_r Z.add_simpl_l.
    rewrite to_Z_mod_pow2_oversize; last exact: leqnn.
    rewrite subnn sext0. reflexivity.
  Qed.

  Lemma bv2z_cast_usu_gt bs n q r :
    size bs < n ->
    Z.div_eucl (to_Z bs) (2 ^ Z.of_nat n) = (q, r) ->
    (to_Z bs + - q * 2 ^ Z.of_nat n)%Z = to_Zpos (sext (n - size bs) bs).
  Proof.
    move=> Hsz H.
    move: (Z.div_eucl_eq (to_Z bs) _ (@pow2_nat2z_nonzero n)).
    rewrite H. rewrite eta_expand_Z_div_eucl in H. case: H => _ <- ->.
    rewrite Z.mul_comm Z.mul_opp_l Z.add_opp_r Z.add_simpl_l.
    rewrite (to_Z_mod_pow2_oversize (ltnW Hsz)). reflexivity. 
  Qed.

  Lemma bv2z_cast_dsu bs n q r :
    n < size bs ->
    Z.div_eucl (to_Z bs) (2 ^ Z.of_nat n) = (q, r) ->
    (to_Zpos (low n bs) + q * 2 ^ Z.of_nat n)%Z = to_Z bs.
  Proof.
    move=> Hsz H.
    move: (Z.div_eucl_eq (to_Z bs) _ (@pow2_nat2z_nonzero n)).
    rewrite H. rewrite eta_expand_Z_div_eucl in H. case: H => _ <- ->.
    rewrite Z.mul_comm Z.add_comm (to_Z_mod_pow2 (ltnW Hsz)). reflexivity. 
  Qed.

  Lemma bv2z_cast_uus bs n :
    size bs < n ->  to_Z (zext (n - size bs) bs) = to_Zpos bs.
  Proof.
    rewrite -subn_gt0 => Hsz. exact: to_Z_zext.
  Qed.

  Lemma bv2z_cast_dus_le bs n q r q' r' :
    n <= size bs ->
    Z.div_eucl (to_Zpos bs) (2 ^ Z.of_nat n) = (q, r) ->
    Z.div_eucl r (2 ^ (Z.of_nat n - 1)) = (q', r') ->
    (to_Z (low n bs) + (q + q') * 2 ^ Z.of_nat n)%Z = to_Zpos bs.
  Proof.
    case: n => [|n] => Hsz.
    - rewrite low0 /= Z.mul_1_r 2!eta_expand_Z_div_eucl Z.div_1_r Zdiv_0_r. 
      case=> <- _ [] <- _. by rewrite Z.add_0_r.
    - rewrite {2}Nat2Z.inj_succ Z.sub_1_r Z.pred_succ => H1 H2.
      move: (Z.div_eucl_eq (to_Zpos bs) _ (@pow2_nat2z_nonzero n.+1)).
      move: (Z.div_eucl_eq r _ (@pow2_nat2z_nonzero n)).
      rewrite H1 H2 => -> ->.
      rewrite Z.mul_add_distr_r Z.add_comm Z.mul_comm -Z.add_assoc Z.add_cancel_l.
      rewrite Nat2Z.inj_succ (Z.pow_succ_r _ _ (Nat2Z.is_nonneg n)). 
      rewrite (Z.mul_comm 2) Z.mul_assoc -Zplus_diag_eq_mult_2 -Z.add_assoc.
      rewrite [in RHS]Z.mul_comm Z.add_cancel_l.
      move: H1 H2. rewrite eta_expand_Z_div_eucl to_Zpos_mod_pow2; case => _ <-.
      rewrite to_Zpos_div_eucl_pow2; case=> <- <-. rewrite size_low subSnn. 
      rewrite (@to_Z_low_high (low n.+1 bs) n 1); [|done|by rewrite size_low addn1].
      rewrite -[in RHS](Z.add_0_r (to_Zpos (low n (low n.+1 bs)))). 
      rewrite Z.add_comm -Z.add_assoc Z.add_cancel_l.
      rewrite high1_msb; case (msb (low n.+1 bs)).
      + have{1}->: [:: true] = ones 1 by reflexivity. 
        rewrite Z.mul_1_l to_Z_ones; last done. 
        rewrite Z.mul_comm -Z.opp_eq_mul_m1 Z.add_opp_diag_l. reflexivity.
      + done.
  Qed.

  Lemma bv2z_cast_dus_eq bs q r q' r' :
    Z.div_eucl (to_Zpos bs) (2 ^ Z.of_nat (size bs)) = (q, r) ->
    Z.div_eucl r (2 ^ (Z.of_nat (size bs) - 1)) = (q', r') ->
    (to_Z bs + (q + q') * 2 ^ Z.of_nat (size bs))%Z = to_Zpos bs.
  Proof.
    have->: to_Z bs = to_Z (low (size bs) bs) by rewrite low_size.
    by apply bv2z_cast_dus_le.
  Qed.

  Lemma bv2z_cast_dus_lt bs n q r q' r' :
    n < size bs ->
    Z.div_eucl (to_Zpos bs) (2 ^ Z.of_nat n) = (q, r) ->
    Z.div_eucl r (2 ^ (Z.of_nat n - 1)) = (q', r') ->
    (to_Z (low n bs) + (q + q') * 2 ^ Z.of_nat n)%Z = to_Zpos bs.
  Proof.
    move=> Hsz; by apply (bv2z_cast_dus_le (ltnW Hsz)).
  Qed.

  Lemma bv2z_cast_uss bs n :
    size bs < n ->
    to_Z (sext (n - size bs) bs) = to_Z bs.
  Proof.
    move=> Hsz; exact: to_Z_sext.
  Qed.

  Lemma bv2z_cast_dss bs n q r q' r' :
    n < size bs ->
    Z.div_eucl (to_Z bs) (2 ^ Z.of_nat n) = (q, r) ->
    Z.div_eucl r (2 ^ (Z.of_nat n - 1)) = (q', r') ->
    (to_Z (low n bs) + (q + q') * 2 ^ Z.of_nat n)%Z = to_Z bs.
  Proof.
    case: n => [|n] => Hsz.
    - rewrite low0 /= Z.mul_1_r 2!eta_expand_Z_div_eucl Z.div_1_r Zdiv_0_r. 
      case=> <- _ [] <- _. by rewrite Z.add_0_r.
    - apply (ltn_trans (ltnSn n)) in Hsz.
      rewrite {2}Nat2Z.inj_succ Z.sub_1_r Z.pred_succ => H1 H2.
      move: (Z.div_eucl_eq (to_Z bs) _ (@pow2_nat2z_nonzero n.+1)).
      move: (Z.div_eucl_eq r _ (@pow2_nat2z_nonzero n)).
      rewrite H1 H2 => -> ->.
      rewrite Z.mul_add_distr_r Z.add_comm Z.mul_comm -Z.add_assoc Z.add_cancel_l.
      rewrite Nat2Z.inj_succ (Z.pow_succ_r _ _ (Nat2Z.is_nonneg n)). 
      rewrite (Z.mul_comm 2) Z.mul_assoc -Zplus_diag_eq_mult_2 -Z.add_assoc.
      rewrite [in RHS]Z.mul_comm Z.add_cancel_l.
      move: H1 H2. rewrite eta_expand_Z_div_eucl (to_Z_mod_pow2 Hsz); case => _ <-.
      rewrite to_Zpos_div_eucl_pow2; case=> <- <-. rewrite size_low subSnn. 
      rewrite (@to_Z_low_high (low n.+1 bs) n 1); [|done|by rewrite size_low addn1].
      rewrite -[in RHS](Z.add_0_r (to_Zpos (low n (low n.+1 bs)))). 
      rewrite Z.add_comm -Z.add_assoc Z.add_cancel_l.
      rewrite high1_msb; case (msb (low n.+1 bs)).
      + have{1}->: [:: true] = ones 1 by reflexivity. 
        rewrite Z.mul_1_l to_Z_ones; last done. 
        rewrite Z.mul_comm -Z.opp_eq_mul_m1 Z.add_opp_diag_l. reflexivity.
      + done.
  Qed.
SearchAbout modn.
End Lemmas.
 