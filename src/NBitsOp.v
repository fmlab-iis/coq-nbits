
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

  Lemma full_adder_zip_carry_inv bs :
    (full_adder_zip true (zip bs (~~# bs))).1 && 
    ~~ (full_adder_zip false (zip bs (~~# bs))).1 .
  Proof .
    elim : bs; first done .
    move => b bs .
    case b => /=;
      dcase (full_adder_zip true (zip bs (~~# bs)))
      => [[h0] tl0];
      dcase (full_adder_zip false (zip bs (~~# bs)))
      => [[h1] tl1] /=; done .
  Qed .      

  Corollary sbbB_ltB_leB (bs1 bs2: bits):
    size bs1 = size bs2 ->
    if (sbbB false bs1 bs2).1 then ltB bs1 bs2 else leB bs2 bs1.
  Proof .
    move : bs1 bs2; apply : seq_ind2; first done .
    move => c0 c1 cs0 cs1 Hsz .
    rewrite /leB !ltB_cons -!Hsz !subnn !zext0 .
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
      try (rewrite Hadder0 Hadder1 /= || rewrite Hadder1 /=) .
    - rewrite !Bool.andb_true_r !Bool.andb_false_r !Bool.orb_false_l .
      case /orP .
      + case => /eqP ->; apply /orP; by left .
      + case => ->; by rewrite Bool.orb_true_r .
    - by rewrite !Bool.andb_true_r .
    - rewrite !Bool.andb_false_r !Bool.orb_false_l .
      case /orP .
      * move => /eqP Heq; move : Hadder0 Hadder1 .
        rewrite Heq => Hadder0 Hadder1 .
        move : (full_adder_zip_carry_inv cs0) .
        by rewrite Hadder0 Hadder1 .
      * done .
    - rewrite !Bool.andb_false_r !Bool.orb_false_l .
      case /orP .
      + case => /eqP ->; apply /orP; by left .
      + case => ->; by rewrite Bool.orb_true_r .
    - rewrite !Bool.andb_false_r !Bool.orb_false_l .
      case /orP .
      + case => /eqP ->; apply /orP; by left .
      + case => ->; by rewrite Bool.orb_true_r .
    - by rewrite !Bool.andb_true_r .
    - rewrite !Bool.andb_true_r .
      case /orP .
      * case => /eqP ->; apply /orP; by left .
      * admit .
    - rewrite !Bool.andb_false_r !Bool.orb_false_l .
      case /orP .
      + case => /eqP ->; apply /orP; by left .
      + case => ->; by rewrite Bool.orb_true_r .
    - by rewrite !Bool.andb_false_r !Bool.orb_false_l .
    - by rewrite !Bool.andb_false_r !Bool.orb_false_l .
    - case => ->; apply /orP; by right .
    - case => ->; apply /orP; by right .
  Admitted .


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


  (*---------------------------------------------------------------------------
    Properties of addition
    ---------------------------------------------------------------------------*)

  Lemma zip_cons A B c0 c1 cs0 cs1 :
    @zip A B (c0::cs0) (c1::cs1) = (c0, c1)::(zip cs0 cs1) .
  Proof .
    by rewrite {1}/zip /= -/zip .
  Qed .

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


  (*---------------------------------------------------------------------------
    Properties of subtraction
  ---------------------------------------------------------------------------*)

  Lemma invB_cons p ps :
    invB (p::ps) == (~~ p)::(invB ps) .
  Proof .
    by case p => /= .
  Qed .

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
      case c0; case c1; rewrite (eqP (@invB_cons _ _));
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
        rewrite !(eqP (@invB_cons _ _));
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
      rewrite /negB -zeros_cons (eqP (@invB_cons _ _)) .
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
  Admitted.
  
  
  Lemma udivB0 : forall n m, (udivB m (zeros n)) = (zeros (size m), m).
  Proof.
    intros; rewrite/udivB. by rewrite to_nat_zeros from_natn0 eq_refl size_rev. 
  Qed.


  Lemma udivB_rec0_aux : forall n(m : bits) s,
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

  Lemma udivB_mulAC : forall d m n, (udivB d m).2 = zeros (size d) -> udivB m (mulB d n) = udivB (mulB m n) d.
  Proof.
  Admitted.
  

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
  
  Lemma neq0_eq0_sizel : forall n (b : bits), b!=zeros (size b) -> from_nat n (to_nat b) == zeros n -> n < size b.
  Proof.
  (*   elim => [|ns IH] b/=; first by (rewrite-ltB0n eq_refl; move=> [Hneq Ht{Ht}]; exact (lt0B_size Hneq)). *)
  (*   move=>[Hneq Heq]. move : (IH (droplsb b)) => Hm. *)
  (*   have -> : (ns.+1 = ns +1) by rewrite addn1. rewrite addnC -ltn_subRL -size_droplsb. *)
  (*   apply Hm; last rewrite to_nat_droplsb. *)
  (*   move : Hneq. rewrite-!to_nat_zero to_nat_droplsb-!lt0n half_gt0. move => Hgt0. *)
  (*   case Hoddb: (odd (to_nat b)); first by rewrite Hoddb eqseq_cons andFb in Heq. *)
  (*   rewrite Hoddb/joinlsb eqseq_cons andTb in Heq. *)
  (*   rewrite -Nat.even_succ-Nat.negb_odd in Hoddb.  *)
  (*   move: (negbFE Hoddb)=>Hodd{Hoddb}. rewrite-Nats.ssrodd_odd in Hodd. rewrite-(ltn_add2r 1)2!addn1 in Hgt0. move : (odd_gt2 Hodd Hgt0)=> Hodd2.  move : (ltn_sub2r Hgt0 Hodd2). by rewrite!subn1/=.  *)
  (*   rewrite eqseq_cons in Heq. move/andP : Heq=>[Hb0 Hzeq]. done. *)
  (* Qed *)
  Admitted.

  Lemma to_nat_belast_0 : forall s, to_nat (belast false (zeros s)) = 0.
  Proof.
    elim => [|ns IH]/=; first done. rewrite IH-muln2 mul0n; done.
  Qed.

  Lemma lt1_eq0 : forall (n:nat), n<1 -> n=0.
  Proof. intros. induction n; try done.
  Qed.

  Lemma from_natSn1 n :
    from_nat n.+1 1 == zext n [::true] .
  Proof .
    case : n; first done .
    move => n .
    by rewrite /from_nat /= -/from_nat from_natn0
               joinlsb_false_zeros zext_zeros_bit .
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
  
  Lemma udivB1: forall p, udivB p (from_nat (size p) 1) = (p, from_nat (size p) 0).
  Proof.
  Admitted.
  
  Lemma shrB_div2exp:  forall i p , (iter i shrB1 p, from_nat (size p) 0) = udivB p (from_nat (size p) (2^ i)%nat).
  Proof.
  Admitted.
  
  Lemma udivB_def: forall q d r, ltB r d -> (udivB (addB (mulB q d) r) d).2 = r.
  Proof.
  Admitted.
  
  Lemma udivB_rec_to_nat : forall nhd ntl m q r, to_nat (udivB_rec (nhd::ntl) m q r).1 = addn (div.divn (addn (to_nat (shlB (size ntl).+1 r)) (to_nat (nhd::ntl))) (to_nat m)) (to_nat q).
  Proof.
  Admitted.
  
  Lemma udivB_to_nat : forall p q,  to_nat (udivB p q).1 = (div.divn (to_nat p) (to_nat (from_nat (size p) (to_nat q)))).
  Proof.
  Admitted.  

  Lemma uremB_to_nat : forall p q , to_nat (udivB p q).2 = (div.modn (to_nat p) (to_nat q)).
  Proof.  
  Admitted.

  
  Lemma udivB_negB_negB bs1 bs2 :
    udivB (negB bs1) (negB bs2) = ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2).
  Proof.
  Admitted.

  (*
  Lemma msb_negB bs :
    msb (negB bs) = ~~ (msb bs).
  Proof.
  Admitted.
   *)

  (*---------------------------------------------------------------------------
    Properties of unsigned modulo
  ---------------------------------------------------------------------------*)
  Definition uremB bs1 bs2 := (udivB bs1 bs2).2.

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


  Definition Nat_dvdn n m := Nat.modulo n m == 0. 

  Lemma modn_mod : forall n m , 0 < m -> div.modn n m = Nat.modulo n m.
  Proof.
  Admitted.

      
  Lemma divn_div : forall n m,  0 < m -> div.divn n m = Nat.div n m.
  Proof.
  Admitted.

  
  Definition sdivB bs1' bs2' : bits * bits :=
    let bs1 := absB bs1' in
    let bs2 := absB bs2' in
    if (msb bs1' == msb bs2') && negb (msb bs1') then udivB bs1 bs2
    else if (msb bs1' == msb bs2') && (msb bs1') then ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2)
         else if (msb bs1' != msb bs2') && negb (msb bs1') then (negB (udivB bs1 bs2).1, (udivB bs1 bs2).2)
              else (negB (udivB bs1 bs2).1, negB (udivB bs1 bs2).2).
  
  Lemma toZ_udiv ub1 ub2 : to_nat ub2 <> 0 -> size ub1 = size ub2 -> to_Zpos (udivB ub1 ub2).1 = Z.div (to_Zpos ub1) (to_Zpos ub2).
  Proof.
    move => Hnot0 Hsz12 .
    rewrite !to_Zpos_nat -(div_Zdiv _ _ Hnot0) udivB_to_nat Hsz12 (to_nat_from_nat_bounded (to_nat_bounded ub2)).
    rewrite ->Nat2Z.inj_iff. rewrite divn_div. done.
    rewrite lt0n. by move/eqP : Hnot0.
  Qed.
  
  Lemma toZ_sdivB sb1 sb2: to_Z (sdivB sb1 sb2).1 = Z.div (to_Z sb1) (to_Z sb2).
  Proof.
    rewrite {2 3}/to_Z /sdivB /absB.
    case Hspmsb1 : (splitmsb sb1) => [tl1 msb1].
    case Hspmsb2 : (splitmsb sb2) => [tl2 msb2]. rewrite /msb Hspmsb1 Hspmsb2/=.
    case Hmsb1 : (msb1); case Hmsb2 : (msb2).
    - rewrite udivB_negB_negB /= Zdiv_opp_opp.
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

  Lemma modn_neq : forall m d, d > 0 -> d <= m-> ~~ (m %% d == m).
  Proof.
    intros.
    rewrite -(ltn_mod m) in H.
    move : (ltn_leq_trans H H0) => Hgt.
    rewrite ltn_neqAle in Hgt. move/andP : Hgt => [Hne Hle]. exact.
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

  Lemma to_Zpos_shlB1 bs :
    to_Zpos (shlB1 bs) = ((to_Zpos bs * 2) mod (2 ^ Z.of_nat (size bs)))%Z.
  Proof.
    rewrite /shlB1 to_Zpos_dropmsb to_Zpos_joinlsb size_joinlsb. 
    by rewrite Nat2Z.inj_add /= Z.add_simpl_r Z.add_0_r. 
  Qed.

  Lemma bv2z_shl_unsigned bs n :
    high n bs == zeros n ->
    to_Zpos (bs <<# n)%bits = (to_Zpos bs * 2 ^ Z.of_nat n)%Z.
  Proof.
    elim: n => [| n IHn].
    - by rewrite /= Z.mul_1_r. 
    - move/eqP=> HhighSn. 
      have Hhighn : high n bs == zeros n by rewrite (high_zeros_le _ HhighSn).
      rewrite /=. 
      have ->: Z.pow_pos 2 (Pos.of_succ_nat n) = (2 ^ Z.of_nat n.+1)%Z by trivial.
      rewrite to_Zpos_shlB1 (IHn Hhighn) size_shlB -Z.mul_assoc. 
      have ->: (2 ^ Z.of_nat n * 2)%Z = (2 * 2 ^ Z.of_nat n)%Z by rewrite Z.mul_comm.
      rewrite -Z.pow_succ_r; last exact: Nat2Z.is_nonneg.
      rewrite -Nat2Z.inj_succ Z.mod_small; first reflexivity.
      split.
      + apply Z.mul_nonneg_nonneg; [ exact: to_Zpos_ge0 | by apply Z.pow_nonneg ].
      + by apply high_zeros_to_Zpos_mul_pow2_bounded.
  Qed.

  Lemma bv2z_shl_signed bs n :
    (high (n + 1) bs == zeros (n + 1)) || (high (n + 1) bs == ones (n + 1)) ->
    to_Z (bs <<# n)%bits = (to_Z bs * 2 ^ Z.of_nat n)%Z.
  Proof.
  Admitted.

  Lemma to_Zpos_low_high bs n m :
    n + m = size bs -> 
    to_Zpos bs = (to_Zpos (low n bs) + to_Zpos (high m bs) * 2 ^ Z.of_nat n)%Z.
  Proof.
    move=> Hsz. by rewrite -{1}(cat_low_high Hsz) to_Zpos_cat size_low.
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

  Lemma bv2z_cshl_unsigned bsh bsl n :
    size bsh = size bsl ->
    high n (bsl ++ bsh) == zeros n ->
    (to_Zpos (low (size bsl) ((bsl ++ bsh) <<# n) >># n)%bits * 2 ^ Z.of_nat n +
     to_Zpos (high (size bsh) ((bsl ++ bsh) <<# n)%bits) * 2 ^ Z.of_nat (size bsl))%Z =
    ((to_Zpos bsh * 2 ^ Z.of_nat (size bsl) + to_Zpos bsl) * 2 ^ Z.of_nat n)%Z.
  Proof.
    move=> Hsz Hzeros.
    rewrite [in RHS]Z.add_comm -to_Zpos_cat -(bv2z_shl_unsigned Hzeros). 
    rewrite -bv2z_shl_unsigned; last by rewrite high_shrB.
    rewrite shrB_shlB_cancel. 
    - rewrite -to_Zpos_low_high; [reflexivity | by rewrite size_shlB size_cat].
    - case Hn : (n <= size bsl).
      + by rewrite (low_low _ Hn) low_shlB_ss.
      + apply negbT in Hn; rewrite leqNgt negbK in Hn; apply ltnW in Hn. 
        by rewrite (low_shlB _ Hn) low_zeros.
  Qed.

  Lemma bv2z_cshl_signed bsh bsl n :
    size bsh = size bsl ->
    (high (n + 1) (bsl ++ bsh) == zeros (n + 1))
    || (high (n + 1) (bsl ++ bsh) == ones (n + 1)) ->
    (to_Zpos (low (size bsl) ((bsl ++ bsh) <<# n) >># n)%bits * 2 ^ Z.of_nat n +
     to_Z (high (size bsh) ((bsl ++ bsh) <<# n)%bits) * 2 ^ Z.of_nat (size bsl))%Z =
    ((to_Z bsh * 2 ^ Z.of_nat (size bsl) + to_Zpos bsl) * 2 ^ Z.of_nat n)%Z.
  Proof.
  Admitted.

  Lemma bv2z_not_unsigned bs :
    to_Zpos (~~# bs)%bits = (2 ^ Z.of_nat (size bs) - Z.one - to_Zpos bs)%Z.
  Proof.
  Admitted.

  Lemma bv2z_not_signed bs :
    to_Z (~~# bs)%bits = (- to_Z bs - Z.one)%Z.
  Proof.
  Admitted.

  Lemma bv2z_add_unsigned bs1 bs2 :
    size bs1 = size bs2 -> ~~ carry_addB bs1 bs2 ->
    to_Zpos (bs1 +# bs2)%bits = (to_Zpos bs1 + to_Zpos bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_add_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Saddo bs1 bs2 ->
    to_Z (bs1 +# bs2)%bits = (to_Z bs1 + to_Z bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_adds_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos (bs1 +# bs2)%bits +
     odd (carry_addB bs1 bs2) * 2 ^ Z.of_nat (size bs1))%Z =
    (to_Zpos bs1 + to_Zpos bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_adds_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Saddo bs1 bs2 ->
    to_Z (bs1 +# bs2)%bits = (to_Z bs1 + to_Z bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_adc_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ carry_addB bs1 bs2 && ~~ carry_addB (bs1 +# bs2)%bits bsc ->
    to_Zpos (adcB (to_bool bsc) bs1 bs2).2 =
    (to_Zpos bs1 + to_Zpos bs2 + to_Zpos bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_adc_signed bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Saddo bs1 bs2 && ~~ Saddo (bs1 +# bs2)%bits bsc ->
    to_Z (adcB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 + to_Z bs2 + to_Zpos bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_adcs_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    (to_Zpos (adcB (to_bool bsc) bs1 bs2).2 +
     odd (adcB (to_bool bsc) bs1 bs2).1 * 2 ^ Z.of_nat (size bs1))%Z =
    (to_Zpos bs1 + to_Zpos bs2 + to_Zpos bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_adcs_signed bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Saddo bs1 bs2 && ~~ Saddo (bs1 +# bs2)%bits bsc ->
    to_Z (adcB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 + to_Z bs2 + to_Zpos bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_sub_unsigned bs1 bs2 :
    size bs1 = size bs2 -> ~~ borrow_subB bs1 bs2 ->
    to_Zpos (bs1 -# bs2)%bits = (to_Zpos bs1 - to_Zpos bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_sub_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Ssubo bs1 bs2 ->
    to_Z (bs1 -# bs2)%bits = (to_Z bs1 - to_Z bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_subc_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos bs1 - to_Zpos bs2 +
     (1 - odd (carry_addB bs1 (-# bs2)%bits)) * 2 ^ Z.of_nat (size bs1))%Z =
    to_Zpos (bs1 +# -# bs2)%bits.
  Proof.
  Admitted.

  Lemma bv2z_subc_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Ssubo bs1 bs2 ->
    to_Z (bs1 +# -# bs2)%bits = (to_Z bs1 - to_Z bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_subb_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos bs1 - to_Zpos bs2 +
     odd (borrow_subB bs1 bs2) * 2 ^ Z.of_nat (size bs1))%Z =
    to_Zpos (bs1 -# bs2)%bits.
  Proof.
  Admitted.

  Lemma bv2z_subb_signed bs1 bs2 :
    size bs1 = size bs2 -> ~~ Ssubo bs1 bs2 ->
    to_Z (bs1 -# bs2)%bits = (to_Z bs1 - to_Z bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_sbc_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ borrow_subB bs1 bs2 && ~~ borrow_subB (bs1 -# bs2)%bits ([:: b1] -# bsc)%bits ->
    to_Zpos (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (to_Zpos bs1 - to_Zpos bs2 - (1 - to_Zpos bsc))%Z.
  Proof.
  Admitted.

  Lemma bv2z_sbc_signed bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (bs1 -# bs2)%bits ([:: b1] -# bsc)%bits ->
    to_Z (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (to_Z bs1 - to_Z bs2 - (1 - to_Zpos bsc))%Z.
  Proof.
  Admitted.

  Lemma bv2z_sbcs_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    (to_Zpos bs1 - to_Zpos bs2 - (1 - to_Zpos bsc) +
     (1 - odd (adcB (to_bool bsc) bs1 (~~# bs2)%bits).1) * 2 ^ Z.of_nat (size bs1))%Z =
    to_Zpos (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2.
  Proof.
  Admitted.

  Lemma bv2z_sbcs_signed bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (bs1 -# bs2)%bits ([:: b1] -# bsc)%bits ->
    to_Z (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (to_Z bs1 - to_Z bs2 - (1 - to_Zpos bsc))%Z.
  Proof.
  Admitted.

  Lemma bv2z_sbb_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ borrow_subB bs1 bs2 && ~~ borrow_subB (bs1 -# bs2)%bits bsc ->
    to_Zpos (sbbB (to_bool bsc) bs1 bs2).2 =
    (to_Zpos bs1 - to_Zpos bs2 - (1 - to_Zpos bsc))%Z.
  Proof.
  Admitted.

  Lemma bv2z_sbb_signed bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (bs1 -# bs2)%bits bsc ->
    to_Z (sbbB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 - to_Z bs2 - (1 - to_Zpos bsc))%Z.
  Proof.
  Admitted.

  Lemma bv2z_sbbs_unsigned bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    (to_Zpos (sbbB (to_bool bsc) bs1 bs2).2 +
     - odd (sbbB (to_bool bsc) bs1 bs2).1 * 2 ^ Z.of_nat (size bs1))%Z =
    (to_Zpos bs1 - to_Zpos bs2 - to_Zpos bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_sbbs_signed bs1 bs2 bsc :
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (bs1 -# bs2)%bits bsc ->
    to_Z (sbbB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 - to_Z bs2 - to_Zpos bsc)%Z.
  Proof.
  Admitted.

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
  Admitted.

  Lemma bv2z_split_signed bs n :
    (to_Zpos (bs <<# (size bs - n) >># (size bs - n))%bits +
     to_Z (sarB n bs) * 2 ^ Z.of_nat n)%Z = to_Z bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_uuu bs n :
    size bs < n -> to_Zpos (zext (n - size bs) bs) = to_Zpos bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_duu bs n q r  :
    n < size bs -> Z.div_eucl (to_Zpos bs) (2 ^ Z.of_nat n) = (q, r) ->
    (to_Zpos (low n bs) + q * 2 ^ Z.of_nat n)%Z = to_Zpos bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_usu_eq bs q r :
    Z.div_eucl (to_Z bs) (2 ^ Z.of_nat (size bs)) = (q, r) ->
    (to_Z bs + - q * 2 ^ Z.of_nat (size bs))%Z = to_Zpos bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_usu_gt bs n q r :
    size bs < n ->
    Z.div_eucl (to_Z bs) (2 ^ Z.of_nat n) = (q, r) ->
    (to_Z bs + - q * 2 ^ Z.of_nat n)%Z = to_Zpos (sext (n - size bs) bs).
  Proof.
  Admitted.

  Lemma bv2z_cast_dsu bs n q r :
    n < size bs ->
    Z.div_eucl (to_Z bs) (2 ^ Z.of_nat n) = (q, r) ->
    (to_Zpos (low n bs) + q * 2 ^ Z.of_nat n)%Z = to_Z bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_uus bs n :
    size bs < n ->  to_Z (zext (n - size bs) bs) = to_Zpos bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_dus_eq bs q r q' r' :
    Z.div_eucl (to_Zpos bs) (2 ^ Z.of_nat (size bs)) = (q, r) ->
    Z.div_eucl r (2 ^ (Z.of_nat (size bs) - 1)) = (q', r') ->
    (to_Z bs + (q + q') * 2 ^ Z.of_nat (size bs))%Z = to_Zpos bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_dus_lt bs n q r q' r' :
    n < size bs ->
    Z.div_eucl (to_Zpos bs) (2 ^ Z.of_nat n) = (q, r) ->
    Z.div_eucl r (2 ^ (Z.of_nat n - 1)) = (q', r') ->
    (to_Z (low n bs) + (q + q') * 2 ^ Z.of_nat n)%Z = to_Zpos bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_uss bs n :
    size bs < n ->
    to_Z (sext (n - size bs) bs) = to_Z bs.
  Proof.
  Admitted.

  Lemma bv2z_cast_dss bs n q r q' r' :
    n < size bs ->
    Z.div_eucl (to_Z bs) (2 ^ Z.of_nat n) = (q, r) ->
    Z.div_eucl r (2 ^ (Z.of_nat n - 1)) = (q', r') ->
    (to_Z (low n bs) + (q + q') * 2 ^ Z.of_nat n)%Z = to_Z bs.
  Proof.
  Admitted.

End Lemmas.
