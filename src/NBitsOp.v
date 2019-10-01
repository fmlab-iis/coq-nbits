
From Coq Require Import ZArith Arith List.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq.
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
                else b1::(succB tl)
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

  Fixpoint full_mul (bs1 bs2 : bits) : bits :=
    match bs1 with
    | [::] => from_nat (size bs1 + size bs2) 0
    | hd::tl =>
      if hd then addB (joinlsb false (full_mul tl bs2)) (zext (size bs1) bs2)
      else joinlsb false (full_mul tl bs2)
    end.

  Definition mulB (bs1 bs2 : bits) : bits := low (size bs1) (full_mul bs1 bs2).

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

  Local Open Scope bits_scope.

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

End Lemmas.
