
From Coq Require Import ZArith Arith List Decidable Lia.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq div.
From nbits Require Import NBitsDef AuxLemmas Compatibility.

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

  Definition sltB (bs1 bs2: bits) :=
    let (tbs1, sign1) := eta_expand (splitmsb bs1) in
    let (tbs2, sign2) := eta_expand (splitmsb bs2) in
    let ult_tl := ltB tbs1 tbs2 in
    ((sign1 == sign2) && ult_tl) || (sign1 && ~~sign2).

  Definition sleB (bs1 bs2: bits) := (bs1 == bs2) || (sltB bs1 bs2).

  Definition sgtB (bs1 bs2: bits) := sltB bs2 bs1.

  Definition sgeB (bs1 bs2: bits) := sleB bs2 bs1.

  (* Rotate to left (to higher bits) *)
  Definition rolB1 (bs : bits) : bits := dropmsb (joinlsb (msb bs) bs).
  Definition rolB (n : nat) (bs : bits) : bits := iter n rolB1 bs.

  (* Rotate to right (to lower bits) *)
  Definition rorB1 (bs : bits) : bits := droplsb (joinmsb bs (lsb bs)).
  Definition rorB (n : nat) (bs : bits) : bits := iter n rorB1 bs.

  Definition shrB1 (bs : bits) : bits := droplsb (joinmsb bs b0).

  Definition shrB (n : nat) (bs : bits) : bits := iter n shrB1 bs.

  (* `shrBB bs ns` is the same as `shrB (to_nat ns) bs` but is more efficient *)
  Definition shrBB (bs : bits) (ns : bits) : bits :=
    let szbs := size bs in
    let szns := size ns in
    let log2szbs := Nat.log2_up szbs in
    if szbs <= 1 then
      if ns == zeros szns
      then bs
      else zeros szbs
    else if szns <= log2szbs then
           shrB (to_nat ns) bs
         else
           (* size bs > 1 -> log2szbs > 0 *)
           let zero_hi := zeros (szns - log2szbs) in
           let ns_hi := high (szns - log2szbs) ns in
           if ns_hi == zero_hi
           then let ns_lo := low log2szbs ns in
                shrB (to_nat ns_lo) bs
           else let zero := from_nat szbs 0 in
                zero.

  Definition sarB1 (bs : bits) : bits := droplsb (joinmsb bs (msb bs)).

  Definition sarB (n : nat) (bs : bits) : bits := iter n sarB1 bs.

  (* `sarBB bs ns` is the same as `sarB (to_nat ns) bs` but is more efficient *)
  Definition sarBB (bs : bits) (ns : bits) : bits :=
    let szbs := size bs in
    let szns := size ns in
    let log2szbs := Nat.log2_up szbs in
    let msb_bs := msb bs in
    if szbs <= 1 then
      if ns == zeros szns
      then bs
      else copy szbs msb_bs
    else if szns <= log2szbs then
           sarB (to_nat ns) bs
         else
           (* size bs > 1 -> log2szbs > 0 *)
           let zero_hi := zeros (szns - log2szbs) in
           let ns_hi := high (szns - log2szbs) ns in
           if ns_hi == zero_hi
           then let ns_lo := low log2szbs ns in
                sarB (to_nat ns_lo) bs
           else copy szbs msb_bs.

  Definition shlB1 (bs : bits) := dropmsb (joinlsb false bs).

  Definition shlB (n : nat) (bs : bits) : bits := iter n shlB1 bs.

  (* `shlBB bs ns` is the same as `shlB (to_nat ns) bs` but is more efficient *)
  Definition shlBB (bs : bits) (ns : bits) : bits :=
    let szbs := size bs in
    let szns := size ns in
    let log2szbs := Nat.log2_up szbs in
    if szbs <= 1 then
      if ns == zeros szns
      then bs
      else zeros szbs
    else if szns <= log2szbs then
           shlB (to_nat ns) bs
         else
           (* size bs > 1 -> log2szbs > 0 *)
           let zero_hi := zeros (szns - log2szbs) in
           let ns_hi := high (szns - log2szbs) ns in
           if ns_hi == zero_hi
           then let ns_lo := low log2szbs ns in
                shlB (to_nat ns_lo) bs
           else let zero := from_nat szbs 0 in
                zero.

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

  (*---------------------------------------------------------------------------
    Aux Properties
    ---------------------------------------------------------------------------*)

  Lemma zip_nil S T (p:seq T) : @zip S T [::] p = [::].
  Proof.
    case p; done. Qed.

  Lemma zip_nil_r S T (p:seq S) : @zip S T p [::] = [::].
  Proof.
    case p; done. Qed.

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

  Lemma msb_cons b bs :
    0 < size bs -> msb (b :: bs) = msb bs.
  Proof.
    case (lastP bs) => {bs} [//= | bs x _]. by rewrite -rcons_cons 2!msb_rcons.
  Qed.

  Lemma is_zero_equiv_zeros bs : is_zero bs <-> bs = zeros (size bs).
  Proof.
    split; first exact: is_zero_zeros. move=> ->; exact: zeros_is_zero.
  Qed.

  Lemma is_zero_eq_zeros bs : is_zero bs = (bs == zeros (size bs)).
  Proof.
    case H0 : (is_zero bs); case H0s : (bs == zeros (size bs)); try done.
    - move/eqP in H0. rewrite eqb_id in H0. apply is_zero_equiv_zeros in H0.
      rewrite {1}H0 eqxx in H0s. assumption.
    - move/eqP in H0s. apply is_zero_equiv_zeros in H0s. rewrite H0s in H0.
      by rewrite H0.
  Qed.

  Lemma zeros_msb_dropmsb bs :
    (bs == zeros (size bs)) =
    (msb bs == false) && (dropmsb bs == zeros (size bs - 1)).
  Proof.
    case (lastP bs) => {bs} [//= | bs b].
    rewrite -is_zero_eq_zeros is_zero_rcons.
    rewrite msb_rcons dropmsb_joinmsb size_rcons subn1 -pred_Sn.
    by rewrite is_zero_eq_zeros andbC.
  Qed.

  Lemma neq_zeros_cons b bs :
    ~~ (b :: bs == zeros (size bs).+1) = ((b == b1) || ~~ (bs == zeros (size bs))).
  Proof.
    rewrite -2!is_zero_eq_zeros is_zero_cons Bool.negb_andb eqbF_neg
              Bool.negb_involutive eqb_id.
    reflexivity.
  Qed.

  Lemma neq_ones_cons b bs :
    ~~ (b :: bs == ones (size bs).+1) = ((b == b0) || ~~ (bs == ones (size bs))).
  Proof.
    rewrite /= eqseq_cons Bool.negb_andb eqbF_neg eqb_id. reflexivity.
  Qed.

  Lemma splitmsb_size1 bs : size bs = 1 -> (splitmsb bs).1 = [::].
  Proof.
    intros. have Hsz : 0 < size bs by rewrite H.
    rewrite -(joinmsb_splitmsb Hsz).
    move : (size_splitmsb bs); rewrite H subnn; move => H0; rewrite (size0nil H0)//.
  Qed.

  Lemma msb1_to_Z_lt0 bs : msb bs <-> (to_Z bs < 0)%Z.
  Proof.
    rewrite to_Z_to_Zpos. case (msb bs); split; try done.
    - rewrite Z.mul_1_l Z.lt_sub_0 => _. exact: to_Zpos_bounded.
    - rewrite Z.mul_0_l Z.sub_0_r => H. apply Z.lt_nge in H.
      apply/negP => _. apply H. exact: to_Zpos_ge0.
  Qed.

  Lemma msb1_to_Z_lt0' bs : 0 < size bs -> msb bs -> (to_Z bs < 0)%Z.
  Proof.
    intros. rewrite -(joinmsb_splitmsb H) -/(msb bs) H0 to_Z_rcons Z.opp_neg_pos.
    by apply Z.add_nonneg_pos; [apply to_Zneg_ge0 | lia].
  Qed.

  Lemma msb_1_size_gt0 bs : msb bs -> 0 < size bs.
  Proof.
    by case bs.
  Qed.

  Lemma Zmod_Zmod_lt z m n:
    (0 < m)%Z -> (0 < n)%Z ->
    (z mod (m * n) mod m = z mod m)%Z.
  Proof.
    intros. rewrite Z.rem_mul_r; [| lia | lia].
    rewrite (Z.mul_comm m ((z / m) mod n)) Z_mod_plus; last lia. by rewrite Zmod_mod //.
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

  Lemma to_nat_gt0_size : forall bs, 0 < to_nat bs -> 0 < size bs.
  Proof.
    intro bs; case bs; try done.
  Qed.

  Lemma Zmod_odd' : forall m d : Z,
      d <> 0%Z -> Z.odd d = false -> Z.odd (m mod d) = Z.odd m.
  Proof.
    move=> m d Hd H.
    rewrite [in RHS](Z.div_mod m d Hd) Z.add_comm Z.odd_add_mul_even; first done.
    by rewrite -Z.even_spec -Z.negb_odd H.
  Qed.

  Lemma to_Z_from_Zpos_1 n : 1 < n -> to_Z (from_Zpos n 1) = 1%Z.
  Proof.
    case: n => [//= | n Hn].
    rewrite /from_Zpos -/from_Zpos /Z.odd /Z.div2 -zeros_from_Zpos.
    have->: joinlsb true (zeros n) = [:: true] ++ zeros n by reflexivity.
    rewrite ltnS in Hn. rewrite to_Z_cat; last by rewrite size_zeros.
    rewrite to_Z_zeros Z.mul_0_l Z.add_0_r. reflexivity.
  Qed.

  Lemma implyF_isF (b : bool) : (b -> false) -> b = false.
  Proof.
    case b; last by reflexivity.
    have{1}->: true = ~~ false by reflexivity. move=> H. apply contraT in H. done.
  Qed.

  Lemma ones_msb_dropmsb bs :
    0 < size bs ->
    (bs == ones (size bs)) = (msb bs == true) && (dropmsb bs == ones (size bs - 1)).
  Proof.
    case (lastP bs) => {bs} [//= | bs b _].
    rewrite size_rcons -ones_rcons msb_rcons dropmsb_joinmsb subn1 -pred_Sn andbC.
    exact: eqseq_rcons.
  Qed.

  Lemma from_Zpos_from_nat_1 n : 0 < n ->(from_Zpos n 1) = (from_nat n 1).
  Proof.
    intros.
    apply to_Zpos_inj_ss; first by rewrite size_from_nat size_from_Zpos.
    rewrite to_Zpos_from_Zpos_1; last by rewrite H.
    rewrite to_Zpos_nat to_nat_from_nat.
    rewrite modn_small; first done.
      by rewrite -{1}(expn0 2) ltn_exp2l; [rewrite H|done].
  Qed.

  Lemma msb_diff_eqF bs1 bs2 : ~~ (msb bs1 == msb bs2) -> (bs1 == bs2) = false.
  Proof.
    case (lastP bs1) => {bs1} [|bs1 b1]; case (lastP bs2) => {bs2} [|bs2 b2] //=.
    - move=> _. rewrite -Bool.negb_true_iff (eq_sym [::]) rev_cons_nil. reflexivity.
    - move=> _. rewrite -Bool.negb_true_iff rev_cons_nil. reflexivity.
    - rewrite !msb_rcons eqseq_rcons. case b1; case b2; by rewrite ?andbF.
  Qed.


  (*---------------------------------------------------------------------------
    Size after operations
    ---------------------------------------------------------------------------*)

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

  Lemma size_full_adder : forall p q c, size (full_adder c p q).2 = minn (size p) (size q).
  Proof.
    elim => [|phd ptl IH] q c.
      by rewrite min0n /full_adder zip_nil/=.
        by rewrite size_full_adder_zip /=.
  Qed.

  Lemma size_adcB : forall p q c, size (adcB c p q).2 = minn (size p) (size q).
  Proof. rewrite /adcB. exact : size_full_adder. Qed.

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

  Lemma size_rolB1 bs : size (rolB1 bs) = size bs.
  Proof.
    rewrite /rolB1. rewrite size_dropmsb size_joinlsb. rewrite addn1 subn1.
    exact: Nat.pred_succ.
  Qed.

  Lemma size_rolB n (bs : bits) : size (rolB n bs) = size bs.
  Proof. elim: n => [| n IH] //=. by rewrite size_rolB1 IH. Qed.

  Lemma size_rorB1 bs : size (rorB1 bs) = size bs.
  Proof.
    rewrite /rorB1. rewrite size_droplsb size_joinmsb. rewrite addn1 subn1.
    exact: Nat.pred_succ.
  Qed.

  Lemma size_rorB n (bs : bits) : size (rorB n bs) = size bs.
  Proof. elim: n => [| n IH] //=. by rewrite size_rorB1 IH. Qed.

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

  Lemma size_iter_shlB1 i ps :
    size (iter i shlB1 ps) = size ps .
  Proof .
    elim : i => [ | i IH ]; first done .
    by rewrite /= size_shlB1 IH .
  Qed .

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

  Lemma size_joinlsb T b (bs : seq T) :
    size (joinlsb b bs) = (size bs) + 1 .
  Proof .
      by rewrite /= addn1 .
  Qed .

  Lemma size_unzip (bsp: seq (bool*bool)) : size (unzip1 bsp) = size (unzip2 bsp).
  Proof.
    elim bsp; first done. intros. by rewrite/=H.
  Qed.

  (*---------------------------------------------------------------------------
    Lemmas about comparison operations
    ---------------------------------------------------------------------------*)

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

  (* ltB semantics *)

  Lemma to_nat_ltB_ss (bs1 bs2 : bits) :
    size bs1 = size bs2 ->
    ltB bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Proof.
    elim: bs1 bs2 => [| hd1 tl1 IH1] [| hd2 tl2] //=. move/eqP. rewrite eqSS=> /eqP Hs.
    rewrite (ltB_cons_ss _ _ Hs). rewrite (IH1 _ Hs).
    rewrite b2n_cons_ltn. rewrite (to_nat_inj_ss Hs). reflexivity.
  Qed.

  Lemma to_nat_ltB (bs1 bs2 : bits) : ltB bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Proof.
    rewrite -(ltB_zext (size bs2 - size bs1) (size bs1 - size bs2)).
    rewrite to_nat_ltB_ss; last exact: size_zext_mkss.
    rewrite !to_nat_zext. reflexivity.
  Qed.

  Lemma to_Zpos_ltB (bs1 bs2 : bits) : ltB bs1 bs2 <-> (to_Zpos bs1 < to_Zpos bs2)%Z.
  Proof.
    rewrite to_nat_ltB !to_Zpos_nat -(Nat2Z.inj_lt). split; by move/ltP.
  Qed.

  Lemma to_Zpos_ltB_eqn (bs1 bs2 : bits) :
    ltB bs1 bs2 = (to_Zpos bs1 <? to_Zpos bs2)%Z.
  Proof.
    case HltB : (ltB bs1 bs2); case Hltb : (to_Zpos bs1 <? to_Zpos bs2)%Z; try done.
    - apply to_Zpos_ltB, Z.ltb_lt in HltB. by rewrite -HltB -Hltb.
    - apply Z.ltb_lt, to_Zpos_ltB in Hltb. by rewrite -HltB -Hltb.
  Qed.

  (* ltB_rev semantics *)

  Lemma to_nat_ltB_rev_ss (bs1 bs2 : bits) :
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

  Lemma to_nat_ltB_rev bs1 bs2 : ltB_rev bs1 bs2 = (to_nat bs1 < to_nat bs2).
  Proof.
    rewrite -ltB_rev_zext. rewrite to_nat_ltB_rev_ss; last exact: size_zext_mkss.
    rewrite !to_nat_zext. reflexivity.
  Qed.

  Lemma ltB_rev_ltB (bs1 bs2 : bits) : ltB_rev bs1 bs2 = ltB bs1 bs2.
  Proof. rewrite to_nat_ltB_rev to_nat_ltB. reflexivity. Qed.

  Lemma ltB_trans (bs1 bs2 bs3 : bits) : ltB bs1 bs2 -> ltB bs2 bs3 -> ltB bs1 bs3.
  Proof. rewrite !to_nat_ltB. exact: ltn_trans. Qed.

  Lemma eqB_ltB_gtB_cases (bs1 bs2 : bits) :
    (zext (size bs2 - size bs1) bs1 == zext (size bs1 - size bs2) bs2)
    || (ltB bs1 bs2) || (ltB bs2 bs1).
  Proof.
    move: (leq_gtn_total (to_nat bs1) (to_nat bs2)). rewrite leq_eqVlt.
    rewrite -2!to_nat_ltB. case/orP; [case/orP|].
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

  Lemma ltB_rcons_ss bs1 bs2 b1 b2 :
    size bs1 = size bs2 ->
    (rcons bs1 b1 <# rcons bs2 b2) = (~~ b1 && b2) || ((bs1 <# bs2) && (b1 == b2)).
  Proof.
    move=> Hsz.
    rewrite -2!ltB_rev_ltB /ltB_rev /extzip0 !extzip_zip_ss ?size_rcons ?Hsz //=.
    by rewrite !rev_zip ?size_rcons ?Hsz //= 2!rev_rcons /= (andbC (_ == _)).
  Qed.

  Lemma ltBNeqB bs1 bs2 : bs1 <# bs2 -> bs1 <> bs2.
  Proof.
    move=> Hlt Heq. apply ltB_eqF in Hlt. rewrite Heq eqxx in Hlt. discriminate.
  Qed.

  Lemma neq_zeros_gt0 bs : ~~ (bs == zeros (size bs)) = (zeros (size bs) <# bs)%Z.
  Proof.
    by rewrite ltB_zeros_l ltB0n.
  Qed.

  (* leB semantics *)

  Lemma to_nat_leB (bs1 bs2 : bits) :
    size bs1 = size bs2 -> leB bs1 bs2 = (to_nat bs1 <= to_nat bs2).
  Proof.
    rewrite /leB leq_eqVlt to_nat_ltB => Hsz. by rewrite (to_nat_inj_ss Hsz).
  Qed.

  Lemma to_Zpos_leB (bs1 bs2 : bits) :
    size bs1 = size bs2 -> leB bs1 bs2 <-> (to_Zpos bs1 <= to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. rewrite (to_nat_leB Hsz) !to_Zpos_nat -(Nat2Z.inj_le).
    split; by move/leP.
  Qed.

  Lemma to_Zpos_leB_eqn (bs1 bs2 : bits) :
    size bs1 = size bs2 -> leB bs1 bs2 = (to_Zpos bs1 <=? to_Zpos bs2)%Z.
  Proof.
    move=> Hsz.
    case HleB : (leB bs1 bs2); case Hleb : (to_Zpos bs1 <=? to_Zpos bs2)%Z; try done.
    - apply (to_Zpos_leB Hsz), Z.leb_le in HleB. by rewrite -HleB -Hleb.
    - apply Z.leb_le, (to_Zpos_leB Hsz) in Hleb. by rewrite -HleB -Hleb.
  Qed.

  (* gtB semantics *)

  Lemma to_nat_gtB_ss (bs1 bs2 : bits) :
    size bs1 = size bs2 -> gtB bs1 bs2 = (to_nat bs1 > to_nat bs2).
  Proof.
    move=> Hsz; apply Logic.eq_sym in Hsz. by rewrite /gtB to_nat_ltB_ss.
  Qed.

  Lemma to_nat_gtB (bs1 bs2 : bits) : gtB bs1 bs2 = (to_nat bs1 > to_nat bs2).
  Proof. by rewrite /gtB to_nat_ltB. Qed.

  Lemma to_Zpos_gtB (bs1 bs2 : bits) : gtB bs1 bs2 <-> (to_Zpos bs1 > to_Zpos bs2)%Z.
  Proof.
    rewrite /gtB to_Zpos_ltB. split; [exact: Z.lt_gt | exact: Z.gt_lt].
  Qed.

  Lemma to_Zpos_gtB_eqn (bs1 bs2 : bits) :
    gtB bs1 bs2 = (to_Zpos bs1 >? to_Zpos bs2)%Z.
  Proof.
    by rewrite /gtB to_Zpos_ltB_eqn Z.gtb_ltb.
  Qed.

  (* geB semantics *)

  Lemma to_nat_geB (bs1 bs2 : bits) :
    size bs1 = size bs2 -> geB bs1 bs2 = (to_nat bs1 >= to_nat bs2).
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. rewrite /geB. exact: to_nat_leB.
  Qed.

  Lemma to_Zpos_geB (bs1 bs2 : bits) :
    size bs1 = size bs2 -> geB bs1 bs2 <-> (to_Zpos bs1 >= to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. rewrite /geB (to_Zpos_leB Hsz).
    split; [exact: Z.le_ge | exact: Z.ge_le].
  Qed.

  Lemma to_Zpos_geB_eqn (bs1 bs2 : bits) :
    size bs1 = size bs2 -> geB bs1 bs2 = (to_Zpos bs1 >=? to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz.
    by rewrite /geB (to_Zpos_leB_eqn Hsz) Z.geb_leb.
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

  Lemma leBB bs1 : leB bs1 bs1.
  Proof. rewrite to_Zpos_leB; last done. exact: Z.le_refl. Qed.


  Lemma leB_ltB_trans bs1 bs2 bs3 : bs1 <=# bs2 -> bs2 <# bs3 -> bs1 <# bs3.
  Proof.
    rewrite /leB. case/orP; last exact: ltB_trans. by move/eqP=> ->.
  Qed.

  Lemma ltB_leB_trans bs1 bs2 bs3 : bs1 <# bs2 -> bs2 <=# bs3 -> bs1 <# bs3.
  Proof.
    rewrite /leB => Hlt. case/orP; last exact: ltB_trans. by move/eqP=> <-.
  Qed.

  Lemma leB_neq_ltB bs1 bs2 : bs1 <=# bs2 -> ~~ (bs1 == bs2) -> bs1 <# bs2.
  Proof.
    rewrite /leB => Hle Hneq. apply negbTE in Hneq. rewrite Hneq orFb in Hle. done.
  Qed.

  Lemma ltB_leB_incl bs1 bs2 : bs1 <# bs2 -> bs1 <=# bs2.
  Proof.
    rewrite /leB. case (bs1 <# bs2); [rewrite orbT |]; done.
  Qed.

  Lemma leB_trans bs1 bs2 bs3 : bs1 <=# bs2 -> bs2 <=# bs3 -> bs1 <=# bs3.
  Proof.
    rewrite /leB. case/orP; move => H1; case/orP; intro H2.
    rewrite (eqP H1) (eqP H2) eq_refl//.
    rewrite (eqP H1) H2 orbT//.
    rewrite -(eqP H2) H1 orbT//.
    rewrite (ltB_trans H1 H2) orbT//.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of signed comparison
    ---------------------------------------------------------------------------*)

   Lemma to_Z_sltB (bs1 bs2 : bits) :
    size bs1 = size bs2 -> sltB bs1 bs2 <-> (to_Z bs1 < to_Z bs2)%Z.
  Proof.
    case (lastP bs1); case (lastP bs2) => {bs1 bs2}.
    - rewrite /sltB /to_Z //=.
    - move=> bs2 b2. rewrite /= size_rcons; discriminate.
    - move=> bs1 b1. rewrite /= size_rcons; discriminate.
    - move=> bs2 b2 bs1 b1.
      rewrite !size_rcons /sltB /to_Z !splitmsb_rcons /= => /eqP.
      rewrite eqSS => /eqP Hsz. case b1; case b2 => /=.
      + rewrite orbF to_Zpos_ltB.
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
      + by rewrite orbF to_Zpos_ltB.
  Qed.

  Lemma to_Z_sltB_eqn (bs1 bs2 : bits) :
    size bs1 = size bs2 -> sltB bs1 bs2 = (to_Z bs1 <? to_Z bs2)%Z.
  Proof.
    move=> Hsz.
    case HsltB : (sltB bs1 bs2); case Hltb : (to_Z bs1 <? to_Z bs2)%Z; try done.
    - apply (to_Z_sltB Hsz), Z.ltb_lt in HsltB. by rewrite -HsltB -Hltb.
    - apply Z.ltb_lt, (to_Z_sltB Hsz) in Hltb. by rewrite -HsltB -Hltb.
  Qed.

  Lemma to_Z_sleB (bs1 bs2 : bits) :
    size bs1 = size bs2 -> sleB bs1 bs2 <-> (to_Z bs1 <= to_Z bs2)%Z.
  Proof.
    move=> Hsz; rewrite /sleB; split.
    - case Hlt : (sltB bs1 bs2).
      + move=> _. apply (to_Z_sltB Hsz) in Hlt. exact: Z.lt_le_incl.
      + case Heq : (bs1 == bs2) => //= _.
        move/eqP: Heq => <-; exact: Z.le_refl.
    - move=> Hle. apply Z.le_lteq in Hle. case: Hle => [Hlt | Heq].
      + apply (to_Z_sltB Hsz) in Hlt. by rewrite Hlt orbT.
      + by rewrite (to_Z_inj_ss Hsz Heq) eqxx.
  Qed.

  Lemma to_Z_sleB_eqn (bs1 bs2 : bits) :
    size bs1 = size bs2 -> sleB bs1 bs2 = (to_Z bs1 <=? to_Z bs2)%Z.
  Proof.
    move=> Hsz.
    case HsleB : (sleB bs1 bs2); case Hleb : (to_Z bs1 <=? to_Z bs2)%Z; try done.
    - apply (to_Z_sleB Hsz), Z.leb_le in HsleB. by rewrite -HsleB -Hleb.
    - apply Z.leb_le, (to_Z_sleB Hsz) in Hleb. by rewrite -HsleB -Hleb.
  Qed.

  Lemma to_Z_sgtB (bs1 bs2 : bits) :
    size bs1 = size bs2 -> sgtB bs1 bs2 <-> (to_Z bs1 > to_Z bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. rewrite /sgtB (to_Z_sltB Hsz).
    split; [exact: Z.lt_gt | exact: Z.gt_lt].
  Qed.

  Lemma to_Z_sgtB_eqn (bs1 bs2 : bits) :
    size bs1 = size bs2 -> sgtB bs1 bs2 = (to_Z bs1 >? to_Z bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz.
    by rewrite /sgtB (to_Z_sltB_eqn Hsz) Z.gtb_ltb.
  Qed.

  Lemma to_Z_sgeB (bs1 bs2 : bits) :
    size bs1 = size bs2 -> sgeB bs1 bs2 <-> (to_Z bs1 >= to_Z bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz. rewrite /sgeB (to_Z_sleB Hsz).
    split; [exact: Z.le_ge | exact: Z.ge_le].
  Qed.

  Lemma to_Z_sgeB_eqn (bs1 bs2 : bits) :
    size bs1 = size bs2 -> sgeB bs1 bs2 = (to_Z bs1 >=? to_Z bs2)%Z.
  Proof.
    move=> Hsz. apply Logic.eq_sym in Hsz.
    by rewrite /sgeB (to_Z_sleB_eqn Hsz) Z.geb_leb.
  Qed.

  Lemma ltB_sltB_same bs1 bs2 :
    size bs1 = size bs2 -> msb bs1 == msb bs2 -> ltB bs1 bs2 = sltB bs1 bs2.
  Proof.
    move=> Hsz Hmsb.
    rewrite to_Zpos_ltB_eqn (to_Z_sltB_eqn Hsz) !to_Z_to_Zpos Hsz (eqP Hmsb).
    case Hlt : (to_Zpos bs1 <? to_Zpos bs2)%Z; apply Logic.eq_sym.
    - apply Z.ltb_lt in Hlt. rewrite Z.ltb_lt -Z.sub_lt_mono_r. exact: Hlt.
    - apply Z.ltb_ge in Hlt. rewrite Z.ltb_ge -Z.sub_le_mono_r. exact: Hlt.
  Qed.

  Lemma sltB_diff bs1 bs2 :
    msb bs1 = b1 -> msb bs2 = b0 -> sltB bs1 bs2.
  Proof.
    rewrite /sltB /msb => -> -> //=.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of rotation to left and to right
    ---------------------------------------------------------------------------*)

  Lemma rolB1_concat_extract bs :
    1 < size bs ->
    rolB1 bs = extract (size bs - 1) (size bs - 1) bs ++ extract (size bs - 2) 0 bs.
  Proof.
    move=> Hsz. rewrite /rolB1 extract_msb (extract_dropmsb Hsz) /= /joinlsb.
    rewrite dropmsb_joinlsb; last by auto. reflexivity.
  Qed.

  Lemma rolB_nil n : rolB n [::] = [::].
  Proof. elim: n => [| n IH] //=. by rewrite IH. Qed.

  Lemma rolB_singleton n b : rolB n [:: b] = [:: b].
  Proof. elim: n => [| n IH] //=. by rewrite IH. Qed.

  Lemma rolBSn_rolBn_rolB1 n bs : rolB n.+1 bs = rolB n (rolB1 bs).
  Proof. rewrite /rolB. exact: iterSr. Qed.

  Lemma rorB1_concat_extract bs :
    1 < size bs ->
    rorB1 bs = extract (size bs - 1) 1 bs ++ extract 0 0 bs.
  Proof.
    move=> Hsz. rewrite /rorB1 extract_lsb (extract_droplsb Hsz) cats1.
    rewrite droplsb_joinmsb; last by auto. reflexivity.
  Qed.

  Lemma rorB_nil n : rorB n [::] = [::].
  Proof. elim: n => [| n IH] //=. by rewrite IH. Qed.

  Lemma rorB_singleton n b : rorB n [:: b] = [:: b].
  Proof. elim: n => [| n IH] //=. by rewrite IH. Qed.

  Lemma rorBSn_rorBn_rorB1 n bs : rorB n.+1 bs = rorB n (rorB1 bs).
  Proof. rewrite /rorB. exact: iterSr. Qed.

  (*---------------------------------------------------------------------------
    Properties of inversion
  ---------------------------------------------------------------------------*)

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

  Lemma dropmsb_invB bs : dropmsb (invB bs) = invB (dropmsb bs).
  Proof.
    case (lastP bs) => {bs} [//= | bs b].
    rewrite invB_rcons !dropmsb_joinmsb. reflexivity.
  Qed.

  Lemma droplsb_invB bs : droplsb (invB bs) = invB (droplsb bs).
  Proof. case: bs => [| b bs] //=. Qed.

  Lemma invB_joinmsb bs b : invB (joinmsb bs b) = joinmsb (invB bs) (~~ b).
  Proof. exact: invB_rcons. Qed.

  Lemma invB_joinlsb b bs : invB (joinlsb b bs) = joinlsb (~~ b) (invB bs).
  Proof. exact: invB_cons. Qed.

  (* invB semantics *)

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

  (*---------------------------------------------------------------------------
    Properties of logic shift right
    ---------------------------------------------------------------------------*)

  Lemma shrB_add bs i j :
    shrB i (shrB j bs) = shrB (i + j) bs .
  Proof .
      by rewrite /shrB iter_add .
  Qed .

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

  Lemma shrB1_is_shrB bs : shrB1 bs = shrB 1 bs.
  Proof. reflexivity. Qed.

  Lemma shrB1_shrB_succ bs n : shrB1 (shrB n bs) = shrB (n.+1) bs.
  Proof. reflexivity. Qed.

  Lemma shrB_shrB1_succ bs n : shrB n (shrB1 bs) = shrB (n.+1) bs.
  Proof.
    rewrite shrB1_is_shrB. rewrite shrB_add. rewrite addn1. reflexivity.
  Qed.

  Lemma shrB1_shrB_comm bs n : shrB1 (shrB n bs) =  shrB n (shrB1 bs).
  Proof.
    rewrite !shrB1_is_shrB. rewrite !shrB_add. rewrite addnC. reflexivity.
  Qed.

  (* shrB1 semantics *)

  Lemma to_nat_shrB1 : forall bs, to_nat (shrB1 bs) = div.divn (to_nat bs) 2.
  Proof.
    elim => [|bhd btl IH]/=. done.
      by rewrite/shrB1 to_nat_droplsb to_nat_joinmsb mul0n add0n/=-muln2-div.divn2.
  Qed.

  Lemma to_Zpos_shrB1 bs : to_Zpos (shrB1 bs) = (Z.div (to_Zpos bs) 2)%Z.
  Proof.
    elim bs => [|bshd bstl IH]; first done.
    rewrite /shrB1 droplsb_joinmsb// droplsb_joinlsb /= Z.mul_comm Z.add_b2z_double_div2 to_Zpos_rcons Z.mul_0_l.
    by rewrite Z.add_0_r.
  Qed.

  Lemma to_Z_shrB1 bs : to_Z (shrB1 bs) = Z.div (to_Zpos bs) 2%Z.
  Proof.
    rewrite !to_Z_to_Zpos msb_shrB1 size_shrB1 to_Zpos_shrB1 Z.mul_0_l Z.sub_0_r//.
  Qed.

  (* shrB semantics *)

  Lemma to_nat_shrB : forall n bs, to_nat (shrB n bs) = div.divn (to_nat bs) (2^n).
  Proof.
    intros.
    elim n => [|ns IH]/=. by rewrite div.divn1.
      by rewrite to_nat_shrB1 IH-div.divnMA expnS mulnC.
  Qed.

  Lemma to_Zpos_shrB : forall n bs, to_Zpos (shrB n bs) = Z.div (to_Zpos bs) (2 ^ Z.of_nat n).
  Proof.
    intros.
    rewrite /shrB. move : n bs. elim => [|ns IH] bs. rewrite Z.pow_0_r Z.div_1_r//.
    rewrite (lock Z.of_nat)/= -lock to_Zpos_shrB1 IH Z.div_div//; last exact : (Z.neq_sym _ _ (Z.lt_neq _ _ (pow2_nat2z_gt0 ns))).
    rewrite -{2}(Z.pow_1_r 2) -Z.pow_add_r//; last apply Nat2Z.is_nonneg.
    rewrite -addn1 Nat2Z.inj_add//.
  Qed.

  Lemma to_Z_shrB : forall n bs, 0 < n -> to_Z (shrB n bs) = Z.div (to_Zpos bs) (2 ^ Z.of_nat n).
  Proof.
    intros. rewrite to_Z_to_Zpos. move : H; case Hn : n => [|ns] Hs; first discriminate.
    rewrite (lock Z.of_nat) /= -lock msb_shrB1 Z.mul_0_l shrB1_shrB_succ to_Zpos_shrB Z.sub_0_r//.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of arithmetic shift right
    ---------------------------------------------------------------------------*)

  Lemma sarB_add bs i j :
    sarB i (sarB j bs) = sarB (i + j) bs .
  Proof .
      by rewrite /sarB iter_add .
  Qed .

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

  Lemma sarB1_is_sarB bs : sarB1 bs = sarB 1 bs.
  Proof. reflexivity. Qed.

  Lemma sarB1_sarB_succ bs n : sarB1 (sarB n bs) = sarB (n.+1) bs.
  Proof. reflexivity. Qed.

  Lemma sarB_sarB1_succ bs n : sarB n (sarB1 bs) = sarB (n.+1) bs.
  Proof.
    rewrite sarB1_is_sarB. rewrite sarB_add. rewrite addn1. reflexivity.
  Qed.

  Lemma sarB1_sarB_comm bs n : sarB1 (sarB n bs) =  sarB n (sarB1 bs).
  Proof.
    rewrite !sarB1_is_sarB. rewrite !sarB_add. rewrite addnC. reflexivity.
  Qed.

  Lemma sarB1_msb0 bs : msb bs = false -> sarB1 bs = shrB1 bs.
  Proof. rewrite /sarB1 /shrB1. by move=> ->. Qed.

  Lemma sarB1_msb1 bs : msb bs = true -> sarB1 bs = invB (shrB1 (invB bs)).
  Proof.
    rewrite /sarB1 /shrB1 => Hmsb.
    rewrite -droplsb_invB invB_joinmsb invB_involutive Hmsb. reflexivity.
  Qed.

  Lemma sarB_msb0 n bs : msb bs = false -> sarB n bs = shrB n bs.
  Proof.
    elim: n => [| n IH] //=.
    move=> Hmsb. rewrite (IH Hmsb) {IH} sarB1_msb0; first reflexivity.
    case: n => [| n] //=. exact: msb_shrB1.
  Qed.

  Lemma sarB_msb1 n bs : msb bs = true -> sarB n bs = invB (shrB n (invB bs)).
  Proof.
    elim: n => [| n IH] /=.
    - rewrite invB_involutive. reflexivity.
    - move=> Hmsb.
      rewrite (IH Hmsb) {IH} sarB1_msb1; first by rewrite invB_involutive.
      move: Hmsb; case: (lastP bs) => {bs} [| bs b] //=.
      rewrite msb_rcons => ->.
      rewrite -msb_invB; last by rewrite size_shrB size_invB size_rcons.
      case: n => [| n] /=.
      + rewrite -msb_invB; last by rewrite size_rcons.
        rewrite msb_rcons. reflexivity.
      + by rewrite msb_shrB1.
  Qed.

  (* sarB1 semantics *)

  Lemma to_Z_sarB1 bs : 1 < size bs -> to_Z (sarB1 bs) = (Z.div (to_Z bs) 2)%Z.
  Proof.
    intros.
    rewrite /sarB1 (droplsb_joinmsb (msb bs) (ltnW H)).
    have Haux : [::msb bs] == [::(msb (droplsb bs))] by rewrite -!high1_msb (high_droplsb H).
    rewrite eqseq_cons eq_refl andbT in Haux. rewrite (eqP Haux).
    rewrite /joinmsb -cats1 -{1}(sext0 (droplsb bs)) -sext_Sn to_Z_sext.
    rewrite 2!to_Z_to_Zpos -(eqP Haux) size_droplsb to_Zpos_droplsb Nat2Z.inj_sub; last (apply/leP; rewrite (ltnW H)//).
    rewrite Z.pow_sub_r;
      [rewrite Z.pow_1_r|lia|split; [apply Nat2Z.is_nonneg|rewrite -Nat2Z.inj_le; apply/leP; rewrite (ltnW H)//]].
    case (msb bs); last rewrite !Z.mul_0_l !Z.sub_0_r//.
    rewrite !Z.mul_1_l.
    have -> : (2 ^ Z.of_nat (size bs) = 2 ^ Z.of_nat (size bs - 1) * 2)%Z.
    {
      rewrite -{3}(Z.pow_1_r 2) -Z.pow_add_r//; last apply Nat2Z.is_nonneg.
      rewrite Nat2Z.inj_sub; last (apply/leP; rewrite (ltnW H)//).
      rewrite Z.sub_simpl_r//.
    }
    rewrite -!Z.add_opp_r -Z.mul_opp_l Z_div_plus// Z_div_mult//.
  Qed.

  (* sarB semantics *)
  Lemma to_Z_sarB n bs : 1 < size bs -> to_Z (sarB n bs) = (Z.div (to_Z bs) (2 ^ Z.of_nat n))%Z.
  Proof.
    rewrite /sarB. move : n bs. elim => [|ns IH] bs Hsz.
    - rewrite Z.pow_0_r Z.div_1_r //.
    - move : (IH bs Hsz) => IHm.
      rewrite (lock Z.of_nat)/= -lock to_Z_sarB1; last rewrite -/(sarB ns bs) size_sarB//.
      rewrite IHm -addn1 Z.div_div//; last (exact : (Z.neq_sym _ _ (Z.lt_neq _ _ (pow2_nat2z_gt0 ns)))).
      rewrite -{2}(Z.pow_1_r 2) -Z.pow_add_r//; last apply Nat2Z.is_nonneg.
      rewrite Nat2Z.inj_add//.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of shift left
    ---------------------------------------------------------------------------*)

  Lemma shlB_add bs i j :
    shlB i (shlB j bs) = shlB (i + j) bs .
  Proof .
      by rewrite /shlB iter_add .
  Qed .

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

  Lemma shlB1_shlB bs n : shlB1 (shlB n bs) = shlB n (shlB1 bs).
  Proof.
    elim: n; first done .
    move => n IH /= .
    by rewrite IH .
  Qed .

  Lemma shlB1_is_shlB bs : shlB1 bs = shlB 1 bs.
  Proof. reflexivity. Qed.

  Lemma shlB1_shlB_succ bs n : shlB1 (shlB n bs) = shlB (n.+1) bs.
  Proof. reflexivity. Qed.

  Lemma shlB_shlB1_succ bs n : shlB n (shlB1 bs) = shlB (n.+1) bs.
  Proof.
    rewrite shlB1_is_shlB. rewrite shlB_add. rewrite addn1. reflexivity.
  Qed.

  Lemma shlB1_shlB_comm bs n : shlB1 (shlB n bs) =  shlB n (shlB1 bs).
  Proof.
    rewrite !shlB1_is_shlB. rewrite !shlB_add. rewrite addnC. reflexivity.
  Qed.

  Lemma succB_shlB1 ps :
    succB (shlB1 ps) = dropmsb (true::ps) .
  Proof .
    elim : ps => [ | p ps IH ] /=; first done .
    by rewrite /dropmsb /= .
  Qed .

  Lemma shrBB_shrB bs ns : shrBB bs ns = shrB (to_nat ns) bs.
  Proof.
    rewrite /shrBB. case Hszbs_le1: (size bs <= 1);
                      last case Hszns: (size ns <= Nat.log2_up (size bs)).
    - case Hns: (ns == zeros (size ns)).
      + rewrite (eqP Hns). rewrite to_nat_zeros /=. reflexivity.
      + rewrite shrB_oversize; first reflexivity. rewrite -to_nat_zero in Hns.
        move/idP/negP: Hns => Hns. rewrite -lt0n in Hns. exact: (leq_trans Hszbs_le1 Hns).
    - reflexivity.
    - have Hs: (Nat.log2_up (size bs)) + (size ns - Nat.log2_up (size bs)) = size ns.
      { move/idP/negP: Hszns. rewrite -ltnNge => Hszns. rewrite (subnKC (ltnW Hszns)).
        reflexivity. }
      case Hzeros: (high (size ns - Nat.log2_up (size bs)) ns ==
                    zeros (size ns - Nat.log2_up (size bs))).
      + rewrite -(cat_low_high Hs). rewrite low_size_cat; last by rewrite size_low.
        rewrite (eqP Hzeros). rewrite to_nat_cat. rewrite to_nat_zeros mul0n addn0.
        reflexivity.
      + rewrite from_natn0. rewrite shrB_oversize; first reflexivity.
        rewrite -(cat_low_high Hs). rewrite to_nat_cat. rewrite size_low. move/idP/negP: Hzeros.
        replace (size ns - Nat.log2_up (size bs))
          with (size (high (size ns - Nat.log2_up (size bs)) ns)) at 2;
          last by rewrite size_high; reflexivity.
        move=> Hzeros. move: (neq_zeros_to_nat_gt0 Hzeros) => Hgt0.
        move/idP/negP: Hszbs_le1. rewrite -ltnNge => Hszbs_gt1.
        have Hszbs_gt0: (0 < size bs) by apply: (ltn_trans _ Hszbs_gt1).
        move/ltP: Hszbs_gt0 => Hszbs_gt0.
        move: (Nat.log2_log2_up_spec _ Hszbs_gt0) => [_ /leP H2]. rewrite -expn_pow in H2.
        rewrite -{1}(add0n (size bs)). apply: leq_add; first done.
        rewrite -{1}(mul1n (size bs)). exact: (leq_mul Hgt0 H2).
  Qed.

  Lemma sarBB_sarB bs ns : sarBB bs ns = sarB (to_nat ns) bs.
  Proof.
    rewrite /sarBB. case Hszbs_le1: (size bs <= 1);
                      last case Hszns: (size ns <= Nat.log2_up (size bs)).
    - case Hns: (ns == zeros (size ns)).
      + rewrite (eqP Hns). rewrite to_nat_zeros /=. reflexivity.
      + rewrite sarB_oversize; first reflexivity. rewrite -to_nat_zero in Hns.
        move/idP/negP: Hns => Hns. rewrite -lt0n in Hns. exact: (leq_trans Hszbs_le1 Hns).
    - reflexivity.
    - have Hs: (Nat.log2_up (size bs)) + (size ns - Nat.log2_up (size bs)) = size ns.
      { move/idP/negP: Hszns. rewrite -ltnNge => Hszns. rewrite (subnKC (ltnW Hszns)).
        reflexivity. }
      case Hzeros: (high (size ns - Nat.log2_up (size bs)) ns ==
                    zeros (size ns - Nat.log2_up (size bs))).
      + rewrite -(cat_low_high Hs). rewrite low_size_cat; last by rewrite size_low.
        rewrite (eqP Hzeros). rewrite to_nat_cat. rewrite to_nat_zeros mul0n addn0.
        reflexivity.
      + rewrite sarB_oversize; first reflexivity.
        rewrite -(cat_low_high Hs). rewrite to_nat_cat. rewrite size_low. move/idP/negP: Hzeros.
        replace (size ns - Nat.log2_up (size bs))
          with (size (high (size ns - Nat.log2_up (size bs)) ns)) at 2;
          last by rewrite size_high; reflexivity.
        move=> Hzeros. move: (neq_zeros_to_nat_gt0 Hzeros) => Hgt0.
        move/idP/negP: Hszbs_le1. rewrite -ltnNge => Hszbs_gt1.
        have Hszbs_gt0: (0 < size bs) by apply: (ltn_trans _ Hszbs_gt1).
        move/ltP: Hszbs_gt0 => Hszbs_gt0.
        move: (Nat.log2_log2_up_spec _ Hszbs_gt0) => [_ /leP H2]. rewrite -expn_pow in H2.
        rewrite -{1}(add0n (size bs)). apply: leq_add; first done.
        rewrite -{1}(mul1n (size bs)). exact: (leq_mul Hgt0 H2).
  Qed.

  Lemma shlBB_shlB bs ns : shlBB bs ns = shlB (to_nat ns) bs.
  Proof.
    rewrite /shlBB. case Hszbs_le1: (size bs <= 1);
                      last case Hszns: (size ns <= Nat.log2_up (size bs)).
    - case Hns: (ns == zeros (size ns)).
      + rewrite (eqP Hns). rewrite to_nat_zeros /=. reflexivity.
      + rewrite shlB_oversize; first reflexivity. rewrite -to_nat_zero in Hns.
        move/idP/negP: Hns => Hns. rewrite -lt0n in Hns. exact: (leq_trans Hszbs_le1 Hns).
    - reflexivity.
    - have Hs: (Nat.log2_up (size bs)) + (size ns - Nat.log2_up (size bs)) = size ns.
      { move/idP/negP: Hszns. rewrite -ltnNge => Hszns. rewrite (subnKC (ltnW Hszns)).
        reflexivity. }
      case Hzeros: (high (size ns - Nat.log2_up (size bs)) ns ==
                    zeros (size ns - Nat.log2_up (size bs))).
      + rewrite -(cat_low_high Hs). rewrite low_size_cat; last by rewrite size_low.
        rewrite (eqP Hzeros). rewrite to_nat_cat. rewrite to_nat_zeros mul0n addn0.
        reflexivity.
      + rewrite from_natn0. rewrite shlB_oversize; first reflexivity.
        rewrite -(cat_low_high Hs). rewrite to_nat_cat. rewrite size_low. move/idP/negP: Hzeros.
        replace (size ns - Nat.log2_up (size bs))
          with (size (high (size ns - Nat.log2_up (size bs)) ns)) at 2;
          last by rewrite size_high; reflexivity.
        move=> Hzeros. move: (neq_zeros_to_nat_gt0 Hzeros) => Hgt0.
        move/idP/negP: Hszbs_le1. rewrite -ltnNge => Hszbs_gt1.
        have Hszbs_gt0: (0 < size bs) by apply: (ltn_trans _ Hszbs_gt1).
        move/ltP: Hszbs_gt0 => Hszbs_gt0.
        move: (Nat.log2_log2_up_spec _ Hszbs_gt0) => [_ /leP H2]. rewrite -expn_pow in H2.
        rewrite -{1}(add0n (size bs)). apply: leq_add; first done.
        rewrite -{1}(mul1n (size bs)). exact: (leq_mul Hgt0 H2).
  Qed.

  (* shlB1 semantics *)
  Lemma to_nat_shlB1 : forall (p: bits), to_nat (shlB1 p) = div.modn ((to_nat p).*2) (2^size p).
  Proof. move => p. by rewrite /shlB1 to_nat_dropmsb to_nat_joinlsb size_joinlsb-subn1 addnK addn0-muln2.
  Qed.

  Lemma to_Zpos_shlB1 bs :
    to_Zpos (shlB1 bs) = ((to_Zpos bs * 2) mod (2 ^ Z.of_nat (size bs)))%Z.
  Proof.
    rewrite /shlB1 to_Zpos_dropmsb to_Zpos_joinlsb size_joinlsb.
    by rewrite Nat2Z.inj_add /= Z.add_simpl_r Z.add_0_r.
  Qed.

  (* shlB semantics *)

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

  Lemma to_nat_shlBnm : forall n m , to_nat (shlB n m) = modn (to_nat m * (2^ n)) (2^ size m).
  Proof.
    elim => [|ns IH] m. rewrite expn0 muln1 -to_nat_mod//.
    rewrite/= to_nat_shlB1.
    rewrite {1}(IH m).
    by rewrite size_shlB -muln2 expnSr mulnA modnMml.
  Qed.

  Lemma to_Zpos_shlB : forall n bs,
    to_Zpos (bs <<# n)%bits = ((to_Zpos bs * 2 ^ Z.of_nat n) mod 2 ^ Z.of_nat (size bs))%Z.
  Proof.
    elim => [|ns IH] bs.
    - rewrite Z.pow_0_r Z.mul_1_r (Z.mod_small _ _ (conj (@to_Zpos_ge0 bs) (to_Zpos_bounded bs)))//.
    - rewrite (lock Z.of_nat) /= -lock to_Zpos_shlB1 size_shlB IH Zmult_mod_idemp_l -Z.mul_assoc -{2}(Z.pow_1_r 2).
      rewrite -Z.pow_add_r//; last apply Nat2Z.is_nonneg.
      rewrite -addn1 Nat2Z.inj_add//.
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

  Lemma adcB0 bs : adcB false bs (zeros (size bs)) = (false, bs).
  Proof.
    elim: bs => [//= | b bs IH]. rewrite /adcB /full_adder /=. case b.
    all : have->: full_adder_zip false (zip bs (zeros (size bs))) =
                  adcB false bs (zeros (size bs)) by reflexivity.
    all : by rewrite IH.
  Qed.

  Lemma joinlsb0_addB1_nocarry bs :
    lsb bs = b0 -> carry_addB bs (from_nat (size bs) 1) = false.
  Proof.
    case: bs => [//= | b bs]. rewrite /lsb /= from_natn0 => ->.
    rewrite /carry_addB /joinlsb /adcB /full_adder /=.
    have->: full_adder_zip false (zip bs (zeros (size bs))) =
            adcB false bs (zeros (size bs)) by reflexivity.
    by rewrite adcB0.
  Qed.

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

  Lemma joinlsb_addB_distr_l ps qs b :
    joinlsb b (ps +# qs) = joinlsb b ps +# joinlsb false qs.
  Proof.
    rewrite /addB /adcB /full_adder /=.
    case b; by case (full_adder_zip false (zip ps qs)).
  Qed.

  Lemma joinlsb_addB_distr_r ps qs b :
    joinlsb b (ps +# qs) = joinlsb false ps +# joinlsb b qs.
  Proof.
    rewrite /addB /adcB /full_adder /=.
    case b; by case (full_adder_zip false (zip ps qs)).
  Qed.

  (* adcB semantics *)

  Lemma to_nat_adcB' p1 p2 c : (adcB c p1 p2).2 = from_nat (size (adcB c p1 p2).2) (c + to_nat p1 + to_nat p2).
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
    rewrite to_nat_adcB'. rewrite size_adcB!to_nat_from_nat size_from_nat=> //.
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

  (* addB semantics *)

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

  Lemma to_Zpos_addB bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos (bs1 +# bs2)%bits + (carry_addB bs1 bs2) * 2 ^ Z.of_nat (size bs1))%Z
    = (to_Zpos bs1 + to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. rewrite /addB /carry_addB (to_Zpos_adcB _ Hsz). reflexivity.
  Qed.

  Lemma to_Zpos_zext_addB bs1 bs2 :
    size bs1 = size bs2 ->
    to_Zpos (low (size bs1) ((zext 1 bs1) +# (zext 1 bs2))) = to_Zpos (bs1 +# bs2).
  Proof.
    intros. rewrite (eqP (addB_zext1_catB H)) /joinmsb -cats1 -(minnn (size bs1)) {2}H -(size_adcB bs1 bs2 b0) low_size_cat//.
  Qed.

  Lemma to_Zpos_addB' bs1 bs2 :
    size bs1 = size bs2 ->
    to_Zpos (addB bs1 bs2) = ((to_Zpos bs1 + to_Zpos bs2) mod 2 ^ Z.of_nat (size bs1))%Z.
  Proof.
    intros. rewrite -(to_Zpos_zext_addB H) -to_Zpos_mod_pow2.
    rewrite (eqP (addB_zext1_catB H)) to_Zpos_rcons size_adcB -H minnn (to_Zpos_adcB b0 H)//.
  Qed.

  Lemma addB_zeros_cats h1 h2 n :
    size h1 = size h2 ->
    (zeros n ++ h1) +# (zeros n ++ h2) = zeros n ++ (h1 +# h2).
  Proof.
    intros. apply to_Zpos_inj_ss; first rewrite size_addB !size_cat size_addB !size_zeros H !minnn//.
    have Hsz : size (zeros n ++ h1) = size (zeros n ++ h2). rewrite !size_cat !size_zeros H//.
    rewrite /addB. rewrite to_Zpos_addB' !size_cat size_zeros H//.
    rewrite !to_Zpos_cat !to_Zpos_zeros !size_zeros !Z.add_0_l -Z.mul_add_distr_r addnC Nat2Z.inj_add Z.pow_add_r; try apply Nat2Z.is_nonneg.
    rewrite Zmult_mod_distr_r Z.mul_cancel_r; last apply Z.neq_sym, Z.lt_neq, pow2_nat2z_gt0.
    rewrite -H (to_Zpos_addB' H)//.
  Qed.

  Lemma leB_addB bs1 bs2 bs3 : size bs1 = size bs2 -> size bs2 = size bs3 ->
                               leB bs1 bs2 -> carry_addB bs2 bs3 = false -> leB bs1 (bs2 +# bs3).
  Proof.
    intros. move : (to_Zpos_addB H0); rewrite H2 Z.mul_0_l Z.add_0_r; move => Hadd.
    rewrite to_Zpos_leB; last rewrite size_addB H0 minnn H//.
    rewrite Hadd. move : H1; rewrite to_Zpos_leB; last done. move => H1.
    rewrite -(Z.add_0_r (to_Zpos bs1)).
    apply Z.add_le_mono; [done|apply to_Zpos_ge0].
  Qed.


  (*---------------------------------------------------------------------------
    Properties of successor
  ---------------------------------------------------------------------------*)

   Lemma leB_succB bs1 bs2 : 0 < size bs1 -> size bs1 = size bs2 ->
                            leB (succB (shlB1 bs1)) bs2 -> leB (shlB1 bs1) bs2.
  Proof.
    intros.
    move : (leB_joinlsb1 false (leBB (dropmsb bs1))).
    rewrite -/joinlsb -!(dropmsb_joinlsb _ H) -succB_shlB1 -/(shlB1 bs1); move => H2.
    exact : (leB_trans H2 H1).
  Qed.

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

  Lemma msb_succB_dropmsb_not1s bs :
    ~~ (dropmsb bs == ones (size bs - 1)) -> msb (succB bs) = msb bs.
  Proof.
    elim: bs => [//= | b bs]. case (lastP bs) => {bs} [//= | bs x].
    rewrite dropmsb_joinmsb size_rcons subn1 -pred_Sn msb_rcons => IH.
    rewrite (eqP (@dropmsb_cons (size bs) b _ _)); last by rewrite size_rcons.
    rewrite dropmsb_joinmsb /size -/size subn1 -pred_Sn size_rcons.
    rewrite -[in RHS]rcons_cons msb_rcons neq_ones_cons => /orP [].
    - move/eqP=> -> /=. by rewrite -rcons_cons msb_rcons.
    - move=> Hnot1s. case b => //=; last by rewrite -rcons_cons msb_rcons.
      rewrite msb_cons; last by rewrite size_succB size_rcons.
      exact: IH.
  Qed.

  Lemma msb_succB_dropmsb_1s bs :
    0 < size bs -> dropmsb bs == ones (size bs - 1) -> msb (succB bs) = ~~ msb bs.
  Proof.
    case (lastP bs) => {bs} [//= | bs x _].
    rewrite dropmsb_joinmsb size_rcons subn1 -pred_Sn msb_rcons.
    elim: bs => [| b bs IH].
    - rewrite /= => _. by case x.
    - rewrite /= eqseq_cons => /andP [/eqP-> Hbs] /=.
      rewrite msb_cons; last by rewrite size_succB size_rcons.
      exact: IH.
  Qed.

  Lemma succB_ones_zeros n : succB (ones n) == zeros n .
  Proof .
    elim n .
    - done .
    - move => m IH .
      by rewrite -ones_cons -zeros_cons (eqP (@succB1 _)) (eqP IH) .
  Qed .

  (* succB semantics *)

  Lemma from_nat_succB bs : succB bs = from_nat (size bs) (to_nat bs).+1.
  Proof.
    rewrite from_natSn_from_nat from_nat_to_nat addB1. reflexivity.
  Qed.

  Lemma from_Zpos_succB bs : succB bs = from_Zpos (size bs) (to_Zpos bs + 1).
  Proof.
    elim: bs => [| b bs IH] //=.
    rewrite Z.add_comm Z.add_assoc {1}Z.mul_comm.
    rewrite Z.odd_add_mul_2 Z.div2_div Z_div_plus; last done.
    case: b.
    - rewrite IH.
      have->: (1 + Z.b2z true = 2)%Z by reflexivity.
      rewrite Z.div_same; last done.
      by rewrite Z.add_comm.
    - have->: (1 + Z.b2z false = 1)%Z by reflexivity.
      by rewrite /= from_Zpos_to_Zpos.
  Qed.

  Lemma to_Zpos_succB bs :
    to_Zpos (succB bs) = ((to_Zpos bs + 1) mod 2 ^ Z.of_nat (size bs))%Z.
  Proof.
    move: (@to_Zpos_ge0 bs) => Hbs.
    rewrite from_Zpos_succB to_Zpos_from_Zpos; last by lia.
    reflexivity.
  Qed.


  (*---------------------------------------------------------------------------
    Properties of subtraction
  ---------------------------------------------------------------------------*)

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

  Lemma negB1_ones_zpos n:
    -# (from_Zpos n 1) == ones n .
  Proof .
    case : n; first done .
    move => n; by rewrite /negB /= -zeros_from_Zpos invB_zeros .
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

  Lemma subB_same m : subB m m = zeros (size m).
  Proof.
    elim : m; first done .
    move => b bs .
    rewrite /subB .
    case : b; rewrite /sbbB /adcB /full_adder /=;
      dcase (full_adder_zip true (zip bs (~~# bs)))
      => [[c] ret] Hadder;
      by rewrite -[(_,ret).2]/(ret)
                 -[(_, false::ret).2]/(false::ret) => -> /= .
  Qed .

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

  Lemma subB_addB : forall bs1 bs2, 0 < size bs1 -> size bs1 = size bs2 ->
                                    addB (subB bs1 bs2) bs2 = bs1.
  Proof.
    intros.
    rewrite /addB /subB sbbB_snd_adcB/= adcB_addB_addB; try rewrite size_adcB size_invB -H0 minnn //.
    rewrite (adcB_addB_addB _ H _); last rewrite size_invB -H0 //.
    apply/eqP; rewrite -to_nat_inj_ss;
      last by rewrite !size_addB !size_invB !size_zext/= addnC (subnK H) H0 !minnn.
    rewrite addBC.
    have -> : [:: false] = zeros 1 by done.
    rewrite zext_zero (subnK H) add0B unzip2_zip;
    last by rewrite size_zeros !size_addB !size_invB !size_zext/= addnC (subnK H) H0 !minnn.
    rewrite -2!addBA (addBC (~~# bs2) ((zext (size bs1 - 1) [:: true]) +# bs2)).
    rewrite -addBA.
    rewrite to_nat_addB.
    rewrite !size_addB !size_invB !size_zext/= addnC -H0 (subnK H) H0 !minnn.
    rewrite to_nat_addB.
    rewrite !size_addB !size_invB !size_zext/= (addnC 1 (size bs2 - 1)) -H0 (subnK H) H0 !minnn.
    rewrite to_nat_zeros -muln2 mul0n addn0.
    rewrite to_nat_addB.
    rewrite size_addB size_invB minnn.
    rewrite to_nat_invB.
    rewrite (addnC (to_nat bs2) (2 ^ size bs2 - 1 - to_nat bs2)) subn1.
    rewrite -addnABC; [|rewrite -ltnS (ltn_predK (exp2n_gt0 _)) to_nat_bounded//|rewrite leqnn//].
    rewrite subnn addn0.
    have Haux : (2 ^ size bs2).-1 < (2 ^ size bs2)
      by rewrite -{2}(subn0 (2 ^ size bs2)) -subn1 ltn_sub2l; [|rewrite exp2n_gt0|rewrite (ltnSn _)].
    rewrite (to_nat_from_nat_bounded Haux).
    rewrite (addnC 1 (2 ^ size bs2).-1) addn1 (ltn_predK (exp2n_gt0 _)).
    rewrite (to_nat_from_nat  (size bs2) (2 ^ size bs2)) modnn addn0 -H0.
    by rewrite to_nat_from_nat to_nat_mod modn_mod.
  Qed.

  (* sbbB semantics *)

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
      by lia.
  Qed.

  (* subB semantics *)

  Lemma to_Zpos_subB bs1 bs2 :
    size bs1 = size bs2 ->
    to_Zpos (bs1 -# bs2) =
    ((borrow_subB bs1 bs2) * 2 ^ Z.of_nat (size bs1) + to_Zpos bs1 - to_Zpos bs2)%Z.
  Proof.
    rewrite /borrow_subB /subB => Hsz. by rewrite (to_Zpos_sbbB _ Hsz) Z.sub_0_r.
  Qed.

  Lemma to_Zpos_subB' bs1 bs2 :
    size bs1 = size bs2 ->
    to_Zpos (bs1 -# bs2) =
    ((to_Zpos bs1 - to_Zpos bs2) mod 2 ^ Z.of_nat (size bs1))%Z.
  Proof.
    move=> Hsz.
    rewrite -(low_size (subB _ _)) size_subB -Hsz minnn.
    rewrite -to_Zpos_mod_pow2 (to_Zpos_subB Hsz).
    rewrite -Z.add_sub_assoc Z.add_comm Z.mod_add; last exact: pow2_nat2z_nonzero.
    reflexivity.
  Qed.

  Lemma ltB_msb_subB bs1 bs2 :
    size bs1 = size bs2 -> msb bs1 == msb bs2 ->
    bs1 <# bs2 -> msb (bs2 -# bs1) = b0.
  Proof.
    move=> Hsz Hmsb Hlt. apply ltB_leB_incl in Hlt. move: Hmsb Hlt.
    rewrite (leBNlt Hsz). symmetry in Hsz.
    rewrite (ltB_equiv_borrow_subB Hsz) (borrow_subB_eq_msbs Hsz).
    by case (msb bs1); case (msb bs2); case (msb (bs2 -# bs1)).
  Qed.

  Lemma ltB_subB_nonzero bs1 bs2 :
    size bs1 = size bs2 -> bs1 <# bs2 -> ~~ (bs2 -# bs1 == zeros (size bs1)).
  Proof.
    move=> Hsz Hlt. move: (ltB_leB_incl Hlt). rewrite (leBNlt Hsz).
    apply to_Zpos_ltB, Z.lt_0_sub in Hlt.
    symmetry in Hsz. rewrite (ltB_equiv_borrow_subB Hsz) => Hb. apply negbTE in Hb.
    move: (to_Zpos_subB Hsz) Hlt. rewrite Hb Z.mul_0_l Z.add_0_l => <-.
    case H : (bs2 -# bs1 == zeros (size bs1)); last by trivial.
    rewrite (eqP H) to_Zpos_zeros. done.
  Qed.

  Lemma ltB_dropmsb_subB_nonzero bs1 bs2 :
    size bs1 = size bs2 -> msb bs1 == msb bs2 ->
    bs1 <# bs2 -> ~~ (dropmsb (bs2 -# bs1) == zeros (size bs1 - 1)).
  Proof.
    move=> Hsz Hmsb Hlt. move: (ltB_msb_subB Hsz Hmsb Hlt) => Hmsb_sub.
    move: (ltB_subB_nonzero Hsz Hlt).
    have->: size bs1 = size (bs2 -# bs1) by rewrite size_subB Hsz minnn.
    generalize dependent (bs2 -# bs1) => {Hsz Hmsb Hlt} bs Hmsb Hbs.
    move: (neq_zero_size_gt0 Hbs) => Hsz. move: Hmsb Hbs.
    rewrite (zeros_msb_dropmsb bs) => -> /=. done.
  Qed.

  Lemma leB_msb_subB bs1 bs2 :
    size bs1 = size bs2 -> msb bs1 == msb bs2 ->
    bs1 <=# bs2 -> msb (bs2 -# bs1) = b0.
  Proof.
    move=> Hsz. rewrite (leBNlt Hsz). symmetry in Hsz.
    rewrite (ltB_equiv_borrow_subB Hsz) (borrow_subB_eq_msbs Hsz).
    by case (msb bs1); case (msb bs2); case (msb (bs2 -# bs1)).
  Qed.

  Lemma msb_ltB_aux bs : bs <# joinmsb (zeros (size bs - 1)) b1 <-> msb bs = b0.
  Proof.
    case (lastP bs) => {bs} [//= | bs b].
    rewrite size_rcons subn1 -pred_Sn msb_rcons to_Zpos_ltB.
    rewrite 2!to_Zpos_rcons to_Zpos_zeros Z.add_0_l Z.mul_1_l size_zeros.
    split.
    - case b; last by trivial.
      rewrite Z.mul_1_l -{2}(Z.add_0_l (2 ^ _)) -Z.add_lt_mono_r => Hlt0.
      move: (@to_Zpos_ge0 bs) => Hge0. discriminate (Z.le_lt_trans _ _ _ Hge0 Hlt0).
    - case b; first by discriminate.
      rewrite Z.mul_0_l Z.add_0_r => _. exact: to_Zpos_bounded.
  Qed.

  Lemma msb_ltB bs1 bs2 :
    size bs1 = size bs2 -> msb bs2 = b0 -> ltB bs1 bs2 -> msb bs1 = b0.
  Proof.
    move=> Hsz. rewrite (ltB_equiv_borrow_subB Hsz) /borrow_subB /sbbB. move: Hsz.
    case: (lastP bs1) => {bs1} [|bs1 b1]; case: (lastP bs2) => {bs2} [|bs2 b2];
    rewrite ?size_rcons //=.
    move/eqP. rewrite eqSS -(size_invB bs2) !msb_rcons => /eqP Hsz ->.
    rewrite /adcB /full_adder (invB_rcons) (zip_rcons _ _ Hsz) -cats1 /=.
    have->: [:: (b1, true)] = zip [:: b1] [:: true] by reflexivity.
    rewrite (eqP (full_adder_zip_cat _ _ _ Hsz)) /=.
    by case b1; case (full_adder_zip true (zip bs1 (~~# bs2))).1.
  Qed.

  Lemma msb_leB bs1 bs2 :
    size bs1 = size bs2 -> msb bs2 = b0 -> leB bs1 bs2 -> msb bs1 = b0.
  Proof.
    rewrite /leB => Hsz Hmsb2 /orP [Heq | Hlt].
    - by rewrite (eqP Heq).
    - exact: (msb_ltB Hsz Hmsb2 Hlt).
  Qed.

  Lemma ltB_subB2l ps qs rs :
    size ps = size qs -> size qs = size rs ->
    ps <# qs -> qs <=# rs -> rs -# qs <# rs -# ps.
  Proof.
    move=> Hsz1 Hsz2 Hpq Hqr. move: (eq_trans Hsz1 Hsz2) => Hsz3.
    symmetry in Hsz2, Hsz3.
    rewrite to_Zpos_ltB (to_Zpos_subB Hsz2) (to_Zpos_subB Hsz3).
    rewrite -(ltB_equiv_borrow_subB Hsz2) -(ltB_equiv_borrow_subB Hsz3).
    move: (ltB_leB_trans Hpq Hqr) => Hpr. apply ltB_leB_incl in Hpr.
    rewrite (leBNlt (Logic.eq_sym Hsz3)) in Hpr. apply negbTE in Hpr.
    rewrite (leBNlt (Logic.eq_sym Hsz2)) in Hqr. apply negbTE in Hqr.
    rewrite Hpr Hqr Z.mul_0_l Z.add_0_l.
    apply Z.sub_le_lt_mono; first exact: Z.le_refl.
    by rewrite -to_Zpos_ltB.
  Qed.

  Lemma ltB_subBr bs1 bs2 :
    size bs1 = size bs2 ->
    zeros (size bs2) <# bs2 -> bs2 <=# bs1 -> bs1 -# bs2 <# bs1.
  Proof.
    move=> Hsz. rewrite -{3}(subB0 bs1) -Hsz. apply ltB_subB2l; last by rewrite Hsz.
    by rewrite size_zeros.
  Qed.

  (* subB  *)

  Lemma to_Z_subB bs1 bs2 :
    size bs1 = size bs2 ->
    (msb bs1 && ~~(msb bs2) && (msb (bs1 -# bs2))) || (~~ (msb bs1) && (msb bs1) && ~~(msb (bs1 -# bs2))) ->
    to_Z (bs1 -# bs2) = (to_Z bs1 - to_Z bs2)%Z.
  Proof.
    move => Hsz Hmc.
    case Hm : (msb bs1 == msb bs2).
    - case Hslt : (sltB bs1 bs2);
        rewrite -(ltB_sltB_same Hsz Hm) in Hslt;
        move : (borrow_subB_eq_msbs Hsz);
        rewrite to_Z_to_Zpos size_subB Hsz minnn// (to_Zpos_subB Hsz) -(ltB_equiv_borrow_subB Hsz) Hslt;
        rewrite 2!to_Z_to_Zpos -(eqP Hm) Hsz Z.sub_sub_distr -Z.add_sub_swap Z.sub_add.
      rewrite Z.mul_1_l.
      case Hm1 : (msb bs1)=>/=;
        rewrite !orbF => Hms;
        rewrite -Hms Z.mul_1_l -Z.sub_add_distr (Z.add_comm (to_Zpos bs2) (2 ^ Z.of_nat (size bs2))) Z.sub_add_distr Z.add_comm Z.add_simpl_r//.
      rewrite Z.mul_0_l Z.add_0_l.
      case Hm1 : (msb bs1)=>/=;
        rewrite !orbF => Hms;
        rewrite -Hms Z.mul_0_l Z.sub_0_r//.
    - move : Hm Hmc; move : (borrow_subB_eq_msbs Hsz); rewrite !to_Z_to_Zpos (to_Zpos_subB Hsz).
      case Hm1 : (msb bs1); case Hm2 : (msb bs2); try done; rewrite !andFb !orFb !andTb !orbF => Hb _ Hmc; rewrite Hb Hmc !Z.mul_0_l !Z.mul_1_l Z.sub_0_r size_subB -Hsz minnn.
      rewrite Z.add_0_l; by lia.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of negation
    ---------------------------------------------------------------------------*)

  Lemma negB_involutive bs : negB (negB bs) = bs.
  Proof.
    elim: bs => [| b bs IH] //=. rewrite /negB /=. case b => /=.
    - by rewrite invB_involutive.
    - rewrite -[in RHS]IH. reflexivity.
  Qed.

  Lemma negB_zeros' bs :
    (bs == zeros (size bs)) <-> (-# bs == zeros (size (negB bs))) .
  Proof.
    case Hz : (bs == zeros (size bs));
    [move : (f_equal negB (eqP Hz)); move => Hng; rewrite Hng size_negB size_zeros negB_zeros//
    |split; [done
            |intro; move : (f_equal negB (eqP H)); rewrite negB_involutive (eqP (negB_zeros _)) size_negB//;
                                                           move => H'; rewrite H' size_zeros eq_refl// in Hz]].
  Qed.
  Lemma msb_negB bs :
    ~~ (dropmsb bs == zeros (size bs - 1)) -> ~~ msb bs = (msb (negB bs)).
  Proof.
    case (lastP bs) => {bs} [//= | bs b] Hnot0.
    rewrite msb_invB; last by rewrite size_rcons.
    rewrite /negB msb_succB_dropmsb_not1s; first reflexivity.
    rewrite dropmsb_joinmsb size_rcons subn1 -pred_Sn in Hnot0.
    rewrite invB_rcons dropmsb_joinmsb size_rcons subn1 -pred_Sn size_invB.
    rewrite -{1}(invB_involutive bs) in Hnot0. apply/eqP => H1.
    rewrite H1 invB_ones eqxx in Hnot0. discriminate.
  Qed.

  Lemma msb_negB_dropmsb_0 bs :
    dropmsb bs == zeros (size bs - 1) -> msb bs = (msb (negB bs)).
  Proof.
    case (lastP bs) => {bs} [//= | bs b] H0.
    rewrite -[in LHS](invB_involutive (rcons bs b)).
    rewrite -msb_invB; last by rewrite size_invB size_rcons.
    rewrite msb_succB_dropmsb_1s; first reflexivity.
    - by rewrite size_invB size_rcons.
    - rewrite invB_rcons dropmsb_joinmsb size_rcons subn1 -pred_Sn size_invB.
      rewrite dropmsb_joinmsb size_rcons subn1 -pred_Sn in H0.
      rewrite {1}(eqP H0) invB_zeros eqxx. done.
  Qed.

  Lemma dropmsb_0_negB_id bs :
    dropmsb bs == zeros (size bs - 1) -> negB bs = bs.
  Proof.
    case (lastP bs) => {bs} [//= | bs x].
    rewrite dropmsb_joinmsb size_rcons subn1 -pred_Sn.
    elim: bs => [/= | b bs IH].
    - move=> _. rewrite /negB /=. by case x.
    - rewrite /= eqseq_cons /negB invB_cons => /andP [/eqP-> Hbs] /=.
      rewrite -[in RHS](IH Hbs). reflexivity.
  Qed.

  Lemma neq_zeros_to_Z_gt0 bs : ~~ (bs == zeros (size bs)) -> (zeros (size bs) <# bs)%Z.
  Proof.
    by rewrite ltB_zeros_l ltB0n.
  Qed.

  Lemma neq_zeros_to_Z_neq0 bs : ~~ (bs == zeros (size bs)) -> (to_Z bs <> 0)%Z.
  Proof.
    move=> Hb Hz. rewrite {1}(to_Z0 Hz) eqxx in Hb. discriminate.
  Qed.

  Lemma neq_zeros_to_Zpos_neq0 bs : ~~ (bs == zeros (size bs)) -> (to_Zpos bs <> 0)%Z.
  Proof.
    move=> Hb Hz. rewrite -(to_Zpos_zeros (size bs)) in Hz. have Hsz : size bs = size (zeros (size bs)) by rewrite size_zeros.
    move/eqP : (to_Zpos_inj_ss Hsz Hz) => H. by rewrite H in Hb.
  Qed.

  Lemma neq_zeros_to_Zpos_gt0 bs : ~~ (bs == zeros (size bs)) -> (0 < to_Zpos bs)%Z.
  Proof.
    rewrite -ltB0n -(ltB_zeros_l (size bs)) to_Zpos_ltB to_Zpos_zeros//.
  Qed.

  Lemma high1_1_to_Zpos_gt0 bs : high 1 bs = [:: b1] -> (0 < to_Zpos bs)%Z.
  Proof.
    case (lastP bs) => {bs} [//= | bs b]. rewrite high1_rcons.
    move/eqP. rewrite eqseq_cons => /andP [/eqP-> _].
    rewrite to_Zpos_rcons. apply Z.add_nonneg_pos; first exact: to_Zpos_ge0.
    rewrite Z.mul_1_l. apply Z.pow_pos_nonneg; [done | exact: Nat2Z.is_nonneg].
  Qed.

  Lemma dropmsb_negB bs : dropmsb (-# bs) = -# (dropmsb bs).
  Proof.
    elim: bs => [//= | b bs IH]. rewrite /negB. case Hsz : (size bs) => [|n].
    - rewrite (eqP (size0 Hsz)) /=. by case b.
    - rewrite (eqP (dropmsb_cons _ Hsz)) !invB_cons /succB -/succB. case b => /=.
      + rewrite -size_invB in Hsz. rewrite (eqP (dropmsb_cons _ Hsz)) dropmsb_invB.
        reflexivity.
      + rewrite -size_invB -size_succB in Hsz. rewrite (eqP (dropmsb_cons _ Hsz)) IH.
        reflexivity.
  Qed.

  Lemma dropmsb_negB_nonzeros bs :
    ~~ (dropmsb bs == zeros (size bs - 1)) ->
    ~~ (dropmsb (-# bs) == zeros (size bs - 1)).
  Proof.
    rewrite dropmsb_negB. rewrite -size_dropmsb. generalize (dropmsb bs) => bs'.
    apply contraNN. rewrite -{1}(size_negB _); by rewrite <-negB_zeros'.
  Qed.

  Lemma negB_from_Zpos_1 bs :
    bs == from_Zpos (size bs) 1 -> -# bs == ones (size bs).
  Proof.
    move=> /eqP ->. case: bs => [//= | b bs].
    by rewrite /negB /= -zeros_from_Zpos size_zeros invB_zeros.
  Qed.

  Lemma neq_ones_negB bs :
    ~~ (bs == ones (size bs)) -> ~~ (-# bs == from_Zpos (size bs) 1).
  Proof.
    apply contraNN. rewrite -{3}(negB_involutive bs).
    have->: size bs = size (-# bs) by rewrite size_negB.
    exact: negB_from_Zpos_1.
  Qed.

  Lemma to_Z_sgn_msb bs : ~~ (bs == zeros (size bs)) ->
                          Z.sgn (to_Z bs) = if (msb bs) then (-1)%Z else 1%Z.
  Proof.
    intros. rewrite to_Z_to_Zpos.
    move : (to_Zpos_bounded bs); rewrite -Z.lt_sub_0; move => Hlt0.
    case Hm :(msb bs).
    - rewrite Z.mul_1_l. exact : (Z.sgn_neg _ Hlt0).
    - rewrite Z.mul_0_l Z.sub_0_r.
      move/neq_zeros_to_Z_gt0 : H.
      rewrite to_Zpos_ltB to_Zpos_zeros; move => Hlt0z.
      apply (Z.sgn_pos _ Hlt0z).
  Qed.

  (* Semantics of negB *)

  Lemma to_Zpos_negB bs :
    to_Zpos (negB bs) = ((- to_Zpos bs) mod 2 ^ Z.of_nat (size bs))%Z.
  Proof.
    rewrite -sub0B to_Zpos_subB size_zeros //= to_Zpos_zeros Z.add_0_r.
    rewrite -ltB_equiv_borrow_subB; last by rewrite size_zeros.
    case Hbs0 : (bs == zeros (size bs)).
    - move/eqP in Hbs0.
      rewrite {2 4 5}Hbs0 to_Zpos_zeros ltBnn Z.mul_0_l /= Zmod_0_l. reflexivity.
    - apply negbT in Hbs0. rewrite -ltB0n -(ltB_zeros_l (size bs)) in Hbs0.
      rewrite Hbs0 Z.mul_1_l.
      rewrite -(Z.mod_add _ 1); last exact: pow2_nat2z_nonzero.
      rewrite Z.mul_1_l Z.add_comm Z.add_opp_r.
      rewrite Z.mod_small; first reflexivity. split.
      + apply Zle_minus_le_0, Z.lt_le_incl. exact: to_Zpos_bounded.
      + rewrite -{2}(Z.sub_0_r (2 ^ _)).
        apply Z.sub_le_lt_mono; first exact: Z.le_refl.
        rewrite to_Zpos_ltB_eqn to_Zpos_zeros in Hbs0.
        by apply /Z.ltb_spec0.
  Qed.

  Lemma high1_1_to_Zpos_negB bs :
    high 1 bs = [:: b1] -> to_Zpos (negB bs) = Z.abs (to_Z bs).
  Proof.
    move=> Hmsb. rewrite (high1_1_to_Z Hmsb).
    rewrite Z.abs_neq;
      last by rewrite Z.opp_nonpos_nonneg; apply Z.le_le_succ_r; exact: to_Zneg_ge0.
    rewrite Z.opp_involutive.
    move/Z.add_move_l: (to_Zpos_add_to_Zneg bs) => ->.
    rewrite -Z.add_1_r -Z.add_sub_swap Z.sub_simpl_r.
    rewrite to_Zpos_negB -(Z.mod_add _ 1); last exact: pow2_nat2z_nonzero.
    rewrite Z.mul_1_l Z.add_comm Z.add_opp_r. apply Z.mod_small.
    split.
    - apply Zle_minus_le_0, Z.lt_le_incl. exact: to_Zpos_bounded.
    - rewrite -{2}(Z.sub_0_r (2 ^ _)).
      apply Z.sub_le_lt_mono; first exact: Z.le_refl.
      exact: high1_1_to_Zpos_gt0.
  Qed.

  Lemma neq_zeros_to_Zpos_negB bs :
    ~~ (bs == zeros (size bs)) ->
    to_Zpos (negB bs) = (2 ^ Z.of_nat (size bs) - to_Zpos bs)%Z.
  Proof.
    move=> Hbs.
    rewrite to_Zpos_negB -(Z.mod_add _ 1); last exact: pow2_nat2z_nonzero.
    rewrite Z.mul_1_l Z.add_comm Z.add_opp_r Z.mod_small; first reflexivity.
    split.
    - apply Zle_minus_le_0, Z.lt_le_incl. exact: to_Zpos_bounded.
    - rewrite -{2}(Z.sub_0_r (2 ^ _)).
      apply Z.sub_le_lt_mono; first exact: Z.le_refl.
      apply neq_zeros_to_Z_gt0, to_Zpos_ltB in Hbs. by rewrite to_Zpos_zeros in Hbs.
  Qed.

  Lemma high1_0_to_Z_negB bs :
    high 1 bs = [:: b0] -> to_Z (negB bs) = (- to_Zpos bs)%Z.
  Proof.
    move: bs. apply: last_ind => [| bs b _] //=.
    rewrite high1_rcons. case => ?; subst. case Hbs: (bs == zeros (size bs)).
    - have Hzbs: (rcons bs b0 = zeros (size bs).+1).
      { rewrite -zeros_rcons. rewrite -(eqP Hbs). reflexivity. }
      rewrite Hzbs. rewrite (eqP (negB_zeros (size bs).+1)).
      rewrite to_Z_zeros to_Zpos_zeros. reflexivity.
    - have Hdnz: (~~ (dropmsb (rcons bs b0) == zeros (size (rcons bs b0) - 1))).
      { apply/negP => H. rewrite dropmsb_rcons in H. apply/negPf: Hbs.
        rewrite size_rcons in H. rewrite subn1 -pred_Sn in H. assumption. }
      rewrite to_Z_to_Zpos. rewrite -(msb_negB Hdnz). rewrite msb_rcons.
      rewrite Z.mul_1_l. rewrite size_negB size_rcons.
      have Hrcons: (~~ (rcons bs b0 == zeros (size (rcons bs b0)))).
      { apply/negP => H. move/negP: Hdnz; apply. rewrite (eqP H).
        rewrite size_rcons size_zeros. rewrite subn1 -pred_Sn.
        rewrite -zeros_rcons dropmsb_rcons eqxx. reflexivity. }
      rewrite (neq_zeros_to_Zpos_negB Hrcons). rewrite size_rcons.
      rewrite Z.add_simpl_l. reflexivity.
  Qed.

  Lemma msb0_to_Z_negB bs :
    msb bs = b0 -> to_Z (negB bs) = (- to_Zpos bs)%Z.
  Proof. move=> Hmsb. apply high1_0_to_Z_negB. by rewrite high1_msb Hmsb. Qed.

  Lemma to_Z_negB_from_Zpos1 n : 0 < n -> to_Z (negB (from_Zpos n 1)) = (- Z.one)%Z.
  Proof.
    have->: from_Zpos n 1 = from_nat n 1.
    { case: n => [| n] //=. by rewrite -zeros_from_Zpos from_natn0. }
    move=> Hn. rewrite (eqP (negB1_ones _)) (to_Z_ones Hn). reflexivity.
  Qed.

  Lemma to_Z_negB bs : negb (msb bs && (dropmsb bs == zeros (size bs - 1))) ->
                       to_Z (negB bs) = (- to_Z bs)%Z.
  Proof.
    case Hm : (msb bs).
    - rewrite andTb; symmetry; rewrite high1_1_to_Z; last rewrite high1_msb Hm//.
      move : (msb_negB H); rewrite Hm /= => Hnm; symmetry in Hnm.
      rewrite Z.opp_involutive high1_0_to_Z; last rewrite high1_msb Hnm//.
      rewrite /negB -to_Zpos_invB -addB1 to_Zpos_addB' size_invB; last rewrite size_from_nat//.
      rewrite -(from_Zpos_from_nat_1 (msb_1_size_gt0 Hm)) (to_Zpos_from_Zpos_1 (msb_1_size_gt0 Hm)).
      rewrite to_Zpos_invB_full -Z.add_1_r Z.add_sub_swap Z.add_opp_r Z.sub_add.
      rewrite Z.mod_small//; split;
        [apply Zle_minus_le_0, Z.lt_le_incl, to_Zpos_bounded
        |rewrite <-Z.lt_sub_pos; apply high1_1_to_Zpos_gt0; rewrite high1_msb Hm//].
    - rewrite (msb0_to_Z_negB Hm) => _. rewrite high1_0_to_Z; first reflexivity.
      rewrite high1_msb Hm. reflexivity.
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

  Lemma upper_bound : forall bs,
      ltB bs (joinmsb (zeros (sig_bits bs)) b1).
  Proof.
    rewrite /sig_bits . move => bs.
    move : (revK bs) => Hrev. rewrite -Hrev. set bsr := rev bs. rewrite revK size_rev.
    elim bsr => [|bsrhd bsrtl IH] .
    - by rewrite /ltB.
    - case Hbsrhd: bsrhd; rewrite rev_cons /=; move : IH.
      + rewrite 2!to_nat_ltB /= add0n 2!to_nat_joinmsb 2!to_nat_zeros 2!size_zeros to_nat_rcons 3!mul1n 2!addn0 size_rev -addnn ltn_add2r.
        move : (sig_bits_le (rev bsrtl)); rewrite/sig_bits revK size_rev.
        move => Hle.
        move: (leq_pexp2l (ltn0Sn 1) Hle). move => Hexp Hlt1.
        exact : (ltn_leq_trans Hlt1 Hexp).
      + rewrite 2!to_nat_ltB /= to_nat_rcons mul0n 2!to_nat_joinmsb 2!to_nat_zeros 2!size_zeros 3!addn0 2!mul1n subn1//.
  Qed.

  Lemma lower_bound : forall bs,
      0 < sig_bits bs -> leB ((joinmsb (zeros (sig_bits bs).-1) b1) ++ zeros (size bs - sig_bits bs)) bs.
  Proof.
    intros.
    rewrite to_Zpos_leB; last rewrite size_cat size_joinmsb !size_zeros addn1 (ltn_predK H) subnKC// (sig_bits_le bs)//.
    rewrite {4}(sig_bits_zero_cat bs) to_Zpos_cat to_Zpos_rcons !to_Zpos_zeros size_joinmsb Z.add_0_r Z.add_0_l Z.mul_1_l size_zeros.
    move : (sig_bits_le bs); rewrite -{1}(subnK H) addn1 subn1 => Haux.
    rewrite /low -{2}(ltn_predK H) (take_nth b1 Haux) -subn1 (get_sig_bit H) !to_Zpos_cat !to_Zpos_zeros !Z.mul_0_l to_Zpos_rcons Z.mul_1_l !Z.add_0_r size_takel;
      last rewrite subn1 (ltnW Haux)//.
    apply Zle_left_rev; rewrite Z.add_opp_r Z.add_simpl_r. apply to_Zpos_ge0.
  Qed.

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

  Lemma to_nat_sig_bits bs : to_nat (ucastB bs (sig_bits bs)) = to_nat bs.
  Proof.
    rewrite/ucastB.
    case Hsz: (sig_bits bs == size bs); try done.
    case Hsz1 : (sig_bits bs < size bs). by rewrite {3}(sig_bits_zero_cat bs) to_nat_cat to_nat_zeros mul0n addn0.
    by rewrite to_nat_zext.
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
    - case b => H .
      + apply : sig_bits_lsb1 .
      + rewrite head_rev in H .
          by rewrite -(sig_bits_cons1 _ ((IH) H)) ltn0Sn .
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
      + move=> Hszcons. rewrite sig_bits_rcons1 size_rev Hsz Hbs1tl0 add0n.
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
      move : Hgt02. case bs2; done.
      move : (Handb Handbb). rewrite size_splitlsb {4}Hbs1 {2}Hbs2 -Hh1 -Hh2/= addSn addnS subn2/=.
      rewrite -(ltn_add2r 1) subnK.
      by rewrite addn1 ltnS.
      rewrite Hbs1. move : (sig_bits_le (joinlsb (splitlsb bs1).1 (splitlsb bs1).2)). rewrite -Hh1.
      move => Hszj.
      exact : (ltn_trans Hgt01 Hszj).
  Qed.

  Lemma sig_bits_cons_b1 bs : sig_bits (b1 :: bs) = sig_bits bs + 1.
  Proof.
    case Hsg : (sig_bits bs).
    - rewrite -sig_bits_consb// Hsg//.
    - rewrite -sig_bits_cons1 Hsg// addn1//.
  Qed.

  Lemma andb_orb_all_b1b1 bs1 bs2: size bs1 = size bs2 ->
                                   andb_orb_all (true :: bs1) (rev (true :: bs2)).
  Proof.
    move => Hsz. rewrite /andb_orb_all revK/= !orbT//.
  Qed.

  Lemma andb_orb_all_zip_rcons11 bs : andb_orb_all_zip (rcons bs (b1, b1)).
  Proof.
    elim bs => [|bshd bstl IH]; first done.
    rewrite /=.
    case bshd => [ls1h ls2h]/=.
    case ls1h; case ls2h;
      [rewrite 2!orbT//|rewrite andbF orbF//|rewrite andbT orbF IH orTb//|rewrite andbF orbF IH//].
  Qed.

  Lemma andb_orb_all_rcons_b1b1 bs1 bs2 :
    size bs1  = size bs2 -> andb_orb_all (rev (b1 :: bs1)) (b1 :: bs2).
  Proof.
    intros. rewrite /andb_orb_all /extzip0. rewrite -rev_extzip_ss/=; last by rewrite H.
    rewrite rev_cons andb_orb_all_zip_rcons11//.
  Qed.

  Lemma andb_orb_all_true_ss' :
    forall bs1 bs2 ,
      size bs1 = size bs2 -> andb_orb_all bs1 bs2 -> (0 < sig_bits bs1) && (0 < sig_bits bs2).
  Proof.
    intros; apply/andP. move : H H0; exact : andb_orb_all_true_ss.
  Qed.

  Lemma andb_orb_all_false_sig_bits' :
    forall bs1 bs2, size bs1 = size bs2 ->
                    ~~ (andb_orb_all bs1 (rev bs2)) -> (sig_bits bs1 + sig_bits (rev bs2)) <= size bs1.
  Proof.
    apply : seq_ind2; first done.
    move => x y s t Hsz IH.
    case Hx : x; case Hy : y;
      try (rewrite (andb_orb_all_b1b1 Hsz)//); rewrite/andb_orb_all revK rev_cons/=; try (rewrite !sig_bits_cons_b1); try (rewrite !orbT andbF orbF || rewrite orbF andbT ||rewrite !orbF andbF orbF).
    - rewrite sig_bits_rcons0; rewrite /andb_orb_all revK in IH; move => Haoa; move : (IH Haoa) => Hsg.
      rewrite addnAC -(addn1 (size s)) leq_add2r//.
    - rewrite sig_bits_rcons1 negb_or; move/andP => [Haoa Hoa].
      rewrite /andb_orb_all revK in IH; move : (IH Haoa) => Hsg.
      rewrite addnS ltnS. rewrite /extzip0 (unzip1_extzip_ss b0 b0 Hsz) in Hoa.
      move/negbTE : Hoa => Hoa. move/eqP : (orb_all_false_zeros Hoa) => Hz.
      rewrite Hz zeros_cons sig_bits_zeros add0n Hsz size_rev size_zeros//.
    - move => Haoa; rewrite /andb_orb_all revK in IH; move : (IH Haoa) => Hsg.
      rewrite sig_bits_rcons0. move : Hsg; case Hsg: (sig_bits s).
      rewrite -sig_bits_consb // Hsg !add0n -(addn1 (size s)) -{2}(addn0 (sig_bits (rev t))).
      move => Hle. exact : (leq_add Hle (ltnW (ltnSn 0))).
      rewrite -sig_bits_cons1 Hsg //.
  Qed.

  Lemma andb_orb_all_false_sig_bits bs1 bs2 :
    size bs1 = size bs2 ->
    ~~ (andb_orb_all bs1 bs2) -> (sig_bits bs1 + sig_bits bs2) <= size bs1.
  Proof.
    rewrite -(revK bs2) {1}size_rev; exact : (andb_orb_all_false_sig_bits').
  Qed.

  Lemma andb_orb_all_false_sig_bits2 bs1 bs2 :
    size bs1 = size bs2 ->
    ~~ (andb_orb_all (splitlsb bs1).2 (splitlsb bs2).2) -> (sig_bits bs1 + sig_bits bs2) <= size bs1 + 1.
  Proof.
    intros.
    have Hszspl : size (splitlsb bs1).2 = size (splitlsb bs2).2 by rewrite !size_splitlsb H.
    move : (andb_orb_all_false_sig_bits Hszspl H0) => Hle.
    case Hszgt0 : (size bs1). generalize Hszgt0; rewrite H; move/size0nil => Hszgt02.
    rewrite (size0nil Hszgt0) Hszgt02//.
    have Hgt01 : 0 < size bs1 by rewrite Hszgt0. generalize Hgt01; rewrite H; move => Hgt02. rewrite size_splitlsb in Hle.
    rewrite -(joinlsb_splitlsb Hgt01) -(joinlsb_splitlsb Hgt02) /joinlsb -Hszgt0. generalize Hle.
    case Hsg1 : (sig_bits (splitlsb bs1).2); case Hsg2 : (sig_bits (splitlsb bs2).2).
    - rewrite -(sig_bits_consb (splitlsb bs1).1 Hsg1) -(sig_bits_consb (splitlsb bs2).1 Hsg2) Hsg1 Hsg2 !add0n//.
      (case (splitlsb bs1).1; case (splitlsb bs2).1); try (rewrite leq_add2r//|| rewrite addnC leq_add2r//|| done).
    - rewrite -(sig_bits_consb (splitlsb bs1).1 Hsg1).
      have Hsg02 : 0 < sig_bits (splitlsb bs2).2 by rewrite Hsg2.
      rewrite -(sig_bits_cons1 (splitlsb bs2).1 Hsg02) -Hsg2 Hsg1 !add0n -(addn1 ((sig_bits (splitlsb bs2).2))) addnA leq_add2r.
      rewrite -ltnS subn1 (ltn_predK Hgt01).
      case (splitlsb bs1).1; first rewrite addnC addn1//; rewrite add0n; apply ltnW.
    - rewrite -(sig_bits_consb (splitlsb bs2).1 Hsg2) Hsg2 add0n.
      have Hsg01 : 0 < sig_bits (splitlsb bs1).2 by rewrite Hsg1.
      rewrite  -(sig_bits_cons1 (splitlsb bs1).1 Hsg01) -Hsg1 addn0 -(addn1 (sig_bits (splitlsb bs1).2)) addnAC leq_add2r.
      rewrite -ltnS subn1 (ltn_predK Hgt01).
      case (splitlsb bs2).1; first rewrite addn1//; rewrite addn0; apply ltnW.
    - have Hsg01 : 0 < sig_bits (splitlsb bs1).2 by rewrite Hsg1.
      have Hsg02 : 0 < sig_bits (splitlsb bs2).2 by rewrite Hsg2.
      rewrite -(sig_bits_cons1 (splitlsb bs1).1 Hsg01) -(sig_bits_cons1 (splitlsb bs2).1 Hsg02) -Hsg1 -Hsg2 -ltnS.
      rewrite subn1 (ltn_predK Hgt01) addSn addnS addn1 ltnS//.
  Qed.

  Lemma sig_bits1_to_Zpos1 bs : sig_bits bs = 1 -> to_Zpos bs = 1%Z.
  Proof.
    intros.
    move : (upper_bound bs); rewrite H to_Zpos_ltB to_Zpos_rcons to_Zpos_zeros/=.
    have Hsz : 0 < sig_bits bs by rewrite H.
    move : (lower_bound Hsz); rewrite H to_Zpos_leB;
      last rewrite size_cat size_joinmsb !size_zeros/= subnKC // add0n (ltn_leq_trans Hsz (sig_bits_le bs))//.
    rewrite to_Zpos_cat to_Zpos_zeros Z.mul_0_l /=.
    move => Hgt1. rewrite Z.lt_le_pred. move/Zle_lt_or_eq => [Hlt|Heq]; by lia.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of multiplication
  ---------------------------------------------------------------------------*)

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

  Lemma one_to_nat n : if (n==0) then to_nat (from_nat n 1) = 0 else to_nat (from_nat n 1) = 1.
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
        rewrite /addB to_nat_adcB'.
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
    elim n. done. intros. rewrite/=. case a. rewrite H zext_nil addB0 unzip1_zip//.
      by rewrite H.
  Qed.

  Lemma mulB_nil_r n : mulB n [::] = zeros (size n).
  Proof.  rewrite/mulB full_mul_nil_r/low size_zeros subnn cats0 take_oversize; last by rewrite size_zeros. done. Qed.

  Lemma mulB0' : forall m n, mulB m (zeros n) = zeros (size m).
  Proof.
    intros. rewrite/mulB full_mulB0/low -zeros_cats take_cat size_zeros/=.
    case H : (size m < size m). rewrite (ltnn (size m)) in H. discriminate.
      by rewrite size_cat size_zeros subnDA subnn take0 sub0n !cats0.
  Qed.

  (* full_mul semantics *)

  Lemma to_nat_full_mul p1 p2 : to_nat (full_mul p1 p2) = to_nat (from_nat (size (full_mul p1 p2)) (to_nat p1 * to_nat p2)).
  Proof.
    move : p2. elim p1 => [|phd1 ptl1 IH] p2 /=; first by rewrite!from_natn0 size_zeros!add0n.
    move : (to_nat_bounded ptl1) => Hbd1; move : (to_nat_bounded p2) => Hbd2.
    move : (ltn_mul Hbd1 Hbd2); rewrite -expnD; move => Hbd. generalize Hbd.
    rewrite -(ltn_pmul2l (ltn0Sn 1)) -expnS mulnC in Hbd. move => Hbd'.
    case phd1.
    - rewrite/= to_nat_addB size_addB size_joinlsb to_nat_joinlsb (IH p2)
             size_full_mul size_zext to_nat_zext addn1
      -addSn addnC minnn addn0 !to_nat_from_nat -!muln2 muln_modl.
      rewrite addnS expnS.
      have-> :(2 * 2 ^ (size p2 + size ptl1) = (2 ^ (size ptl1 + size p2) * 2)) by rewrite mulnC addnC. rewrite div.modnDml.
      have->:(((1 + to_nat ptl1 * 2) * to_nat p2) = to_nat ptl1 * to_nat p2 * 2 + to_nat p2) by rewrite mulnDl mul1n; ring. done.
    - rewrite size_joinlsb to_nat_joinlsb (IH p2) size_full_mul addn0 add0n-!muln2!to_nat_from_nat_bounded; first ring; try exact. by rewrite addn1 mulnAC.
  Qed.

  Lemma to_nat_full_mul' bs1 bs2 :
    to_nat (full_mul bs1 bs2) = to_nat bs1 * to_nat bs2.
  Proof.
    rewrite to_nat_full_mul size_full_mul. apply to_nat_from_nat_bounded.
    rewrite expnD; apply ltn_mul; exact: to_nat_bounded.
  Qed.

  Lemma to_Zpos_full_mul bs1 bs2 :
    to_Zpos (full_mul bs1 bs2) = (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
    move: (to_nat_full_mul' bs1 bs2) => Hnat.
    apply (f_equal Z.of_nat) in Hnat. rewrite Nat2Z.inj_mul -!to_Zpos_nat in Hnat.
    exact: Hnat.
  Qed.

  (* mulB semantics *)

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

  Lemma to_Zpos_mulB' bs1 bs2 :
    to_Zpos (bs1 *# bs2) =
    ((to_Zpos bs1 * to_Zpos bs2) mod 2 ^ Z.of_nat (size bs1))%Z.
  Proof.
    rewrite /mulB -to_Zpos_mod_pow2 to_Zpos_full_mul. reflexivity.
  Qed.

  Lemma full_mul_mulB_zext bs1 bs2 :
    full_mul bs1 bs2 = zext (size bs2) bs1 *# zext (size bs1) bs2.
  Proof.
    move: (to_nat_mulB (zext (size bs2) bs1) (zext (size bs1) bs2))
          (to_nat_full_mul' bs1 bs2).
    rewrite size_zext 2!to_nat_zext to_nat_from_nat_bounded;
      last (rewrite expnD; apply ltn_mul; exact: to_nat_bounded).
    move=> <- /eqP H.
    rewrite to_nat_inj_ss in H; last by rewrite size_full_mul size_mulB size_zext.
    exact: (eqP H).
  Qed.

  Lemma mulB_shlB_assoc bs1 bs2 n :
    size bs1 = size bs2 -> (bs1 *# bs2) <<# n = bs1 *# (bs2 <<# n).
  Proof.
    move=> Hsz. apply to_Zpos_inj_ss; first by rewrite size_shlB !size_mulB.
    case/orP: (leq_gtn_total (size bs1) n) => Hn.
    - rewrite shlB_oversize; last by rewrite size_mulB.
      rewrite shlB_oversize; last by rewrite -Hsz.
      by rewrite mulB0' !to_Zpos_zeros.
    - rewrite to_Zpos_shlB 2!to_Zpos_mulB' to_Zpos_shlB size_mulB -Hsz.
      rewrite Z.mul_mod_idemp_r; last exact: pow2_nat2z_nonzero.
      rewrite Z.mul_mod_idemp_l; last exact: pow2_nat2z_nonzero.
      by rewrite Z.mul_assoc.
  Qed.

  Lemma mulB_shlB_swap bs1 bs2 n :
    size bs1 = size bs2 -> bs1 *# (bs2 <<# n) = (bs1 <<#n) *# bs2.
  Proof.
    move=> Hsz. rewrite -(mulB_shlB_assoc _ Hsz) (mulBC Hsz).
    rewrite mulB_shlB_assoc; last by symmetry.
    rewrite mulBC; last by rewrite size_shlB Hsz. reflexivity.
  Qed.

  (* The semantics of Umulo *)
  Lemma umulo_to_Zpos bs1 bs2 :
    size bs1 = size bs2 ->
    ~~ Umulo bs1 bs2 <-> (to_Zpos bs1 * to_Zpos bs2 < 2 ^ Z.of_nat (size bs1))%Z.
  Proof.
    rewrite /Umulo.
    case Haoa : (andb_orb_all (splitlsb bs1).2 (splitlsb bs2).2).
    - split; try done.
      rewrite orTb/=.  move : (andb_orb_all_sig_bits2 H Haoa) => Hszsg.
      move : (to_nat_sig_bits bs1); rewrite 2!to_nat_Zpos Z2Nat.inj_iff; try apply to_Zpos_ge0; move => Hz1.
      move : (to_nat_sig_bits bs2); rewrite 2!to_nat_Zpos Z2Nat.inj_iff; try apply to_Zpos_ge0; move => Hz2.
      move : (andb_orb_all_true Haoa) => [Hsg1 Hsg2].
      move : (ltn_leq_trans Hsg1 (sig_bits_le (splitlsb bs1).2));
      move : (ltn_leq_trans Hsg2 (sig_bits_le (splitlsb bs2).2)); rewrite 2!size_splitlsb 2!subn_gt0; move => Hsz2 Hsz1.
      move : (ltn_leq_trans Hsg1 (sig_bits_cons (splitlsb bs1).1 (splitlsb bs1).2));
      move : (ltn_leq_trans Hsg2 (sig_bits_cons (splitlsb bs2).1 (splitlsb bs2).2)).
      rewrite -2!/joinlsb !joinlsb_splitlsb; try (rewrite (ltnW Hsz2)//||rewrite (ltnW Hsz1)//).
      move => Hsg2gt0 Hsg1gt0 {Hsg1 Hsg2 Hsz1 Hsz2}.
      move : (lower_bound Hsg1gt0); move : (lower_bound Hsg2gt0).
      rewrite to_Zpos_leB;
        [rewrite to_Zpos_leB;
         [|rewrite size_cat size_joinmsb !size_zeros -subn1 (subnK Hsg1gt0) (subnKC (sig_bits_le bs1))//]
          |rewrite size_cat size_joinmsb !size_zeros -subn1 (subnK Hsg2gt0) (subnKC (sig_bits_le bs2))//].
      rewrite !to_Zpos_cat !to_Zpos_zeros !Z.mul_0_l !Z.add_0_r.
      rewrite 2!/joinmsb 2!to_Zpos_rcons 2!size_zeros 2!to_Zpos_zeros 2!Z.add_0_l 2!Z.mul_1_l.
      move => Hgt2 Hgt1.
      move : (Z.mul_le_mono_nonneg _ _ _ _ (Z.lt_le_incl _ _ (pow2_nat2z_gt0 (sig_bits bs1).-1)) Hgt1 (Z.lt_le_incl _ _ (pow2_nat2z_gt0 (sig_bits bs2).-1)) Hgt2).
      rewrite -Z.pow_add_r; try apply Nat2Z.is_nonneg.
      rewrite -Nat2Z.inj_add Nat.add_pred_l; last apply (nesym (lt_0_neq _ (ltP Hsg1gt0))).
      rewrite Nat.add_pred_r; last apply (nesym (lt_0_neq _ (ltP Hsg2gt0))).
      have -> : (sig_bits bs1 + sig_bits bs2)%coq_nat = (sig_bits bs1 + sig_bits bs2) by done. rewrite -subn2.
      move => Hmult.
      move/leP : Hszsg; rewrite Nat2Z.inj_le; move => Hszsg.
      move : (Zle_not_lt _ _ (Z.le_trans _ _ _ (Z.pow_le_mono_r _ _ _ (Z.lt_0_2) Hszsg) Hmult)). done.
    - split; rewrite orFb. move => Hmsbz.
      move/leP : (andb_orb_all_false_sig_bits2 H (negbT Haoa)) => Haoaf. rewrite ->Nat2Z.inj_le in Haoaf.
      move : (Z.pow_le_mono_r _ _ _ Z.lt_0_2 Haoaf) => Haoaf'.
      have Hszgt0 : 0 < size (zext 1 bs1 *# zext 1 bs2) by rewrite size_mulB size_zext addn1//.
      move : (upper_bound bs1); move : (upper_bound bs2).
      rewrite 2!to_Zpos_ltB /joinmsb !to_Zpos_rcons !to_Zpos_zeros !size_zeros 2!Z.mul_1_l 2!Z.add_0_l.
      move => Hbd2 Hbd1.
      move : (Z.mul_lt_mono_nonneg _ _ _ _ (@to_Zpos_ge0 bs1) Hbd1 (@to_Zpos_ge0 bs2) Hbd2).
      rewrite -(Z.pow_add_r _ _ _ (Nat2Z.is_nonneg _) (Nat2Z.is_nonneg _)) -Nat2Z.inj_add.
      have -> : (sig_bits bs1 + sig_bits bs2)%coq_nat = (sig_bits bs1 + sig_bits bs2) by done.
      move => Hmullt. move : (Z.lt_le_trans _ _ _ Hmullt Haoaf') => Hlt1.
      move : Hmsbz.
      rewrite ->(msb0_to_Zpos_bounded Hszgt0).
      rewrite size_mulB size_zext addnK to_Zpos_mulB' 2!to_Zpos_zext size_zext.
      rewrite Z.mod_small//; last (split; [apply Z.mul_nonneg_nonneg; try apply to_Zpos_ge0| done]).
    - have Hszzmul : 0 < size (zext 1 bs1 *# zext 1 bs2) by rewrite size_mulB size_zext addn1//.
      move => Hlt.
      rewrite (msb0_to_Zpos_bounded Hszzmul) size_mulB size_zext addnK to_Zpos_mulB' 2!to_Zpos_zext size_zext.
      have Hlt1: (2 ^ Z.of_nat (size bs1) < 2 ^ Z.of_nat (size bs1 + 1))%Z.
      {
        apply Z.pow_lt_mono_r; [done|apply Nat2Z.is_nonneg|rewrite -Nat2Z.inj_lt addn1; apply Nat.lt_succ_diag_r].
      }
      rewrite Z.mod_small//; last (split; [apply Z.mul_nonneg_nonneg; apply to_Zpos_ge0|exact : (Z.lt_trans _ _ _ Hlt Hlt1)]).
  Qed.

  (* Semantics of mulB without overflow *)
  Lemma to_Zpos_mulB bs1 bs2 :
    size bs1 = size bs2 -> ~~ Umulo bs1 bs2 ->
    to_Zpos (bs1 *# bs2)%bits = (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
    move: (to_Zpos_full_mul bs1 bs2) => H.
    apply (f_equal (fun z => Z.modulo z (2 ^ Z.of_nat (size bs1)))) in H. move: H.
    rewrite to_Zpos_mod_pow2 /mulB => -> Hsz Hov.
    rewrite Z.mod_small; first reflexivity. split.
    - apply Z.mul_nonneg_nonneg; exact: to_Zpos_ge0.
    - by apply umulo_to_Zpos.
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

  Lemma andB_cons b1 bs1 b2 bs2 :
    andB (b1 :: bs1) (b2 :: bs2) = (andb b1 b2) :: (andB bs1 bs2).
  Proof. by rewrite /andB /lift0 lift_cons. Qed.

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

  Lemma orB_copy_case : forall b bs,
      orB (copy (size bs) b) bs = if b then ones (size bs) else bs.
  Proof.
    move => [] bs.
    - by rewrite or1B.
    - by rewrite or0B.
  Qed.

  Lemma orB_cons b1 bs1 b2 bs2 :
    orB (b1 :: bs1) (b2 :: bs2) = (orb b1 b2) :: (orB bs1 bs2).
  Proof. by rewrite /orB /lift0 lift_cons. Qed.


  (*---------------------------------------------------------------------------
    Properties of bitwise xor
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

  Lemma xorB_cons b1 bs1 b2 bs2 :
    xorB (b1 :: bs1) (b2 :: bs2) = (xorb b1 b2) :: (xorB bs1 bs2).
  Proof. by rewrite /xorB /lift0 lift_cons. Qed.

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

  (*---------------------------------------------------------------------------
    Signed multiplication overflow detection
    ---------------------------------------------------------------------------*)

  Lemma signed_sig_bits_to_Z bs : msb bs -> (- 2 ^ Z.of_nat (size bs - 1) <= to_Z bs < 0)%Z.
  Proof.
    intros. rewrite -{2 3}(joinmsb_splitmsb (msb_1_size_gt0 H)) -/(msb bs) H to_Z_rcons.
    split.
    - rewrite -Z.opp_le_mono -to_Zpos_invB.
      move : (to_Zpos_bounded (~~# (splitmsb bs).1)); rewrite size_invB size_splitmsb; move/Zlt_le_succ => H0; done.
    - rewrite Z.opp_neg_pos; apply Z.add_nonneg_pos; [apply to_Zneg_ge0|done].
  Qed.

  Lemma mulB_same_sign_bits bs1 bs2 :
    size bs1 = size bs2 ->
    low (size bs1) (full_mul (joinmsb bs1 b1) (joinmsb bs2 b1))
    = low (size bs1) (full_mul (joinmsb bs1 b0) (joinmsb bs2 b0)).
  Proof.
    intros.
    apply to_Zpos_inj_ss; first rewrite !size_low//.
    rewrite -!to_Zpos_mod_pow2 2!to_Zpos_full_mul !to_Zpos_rcons !Z.mul_0_l !Z.add_0_r !Z.mul_1_l Zmult_mod -H.
    repeat (rewrite -Zplus_mod_idemp_r Z_mod_same_full Z.add_0_r).
    rewrite -Zmult_mod//.
  Qed.

  Lemma full_mul_sext1_zext1 bs1 bs2 :
    size bs1 = size bs2 ->
    low (size bs1) (full_mul (sext 1 bs1) (sext 1 bs2))
    = low (size bs1) (full_mul (zext 1 bs1) (zext 1 bs2)).
  Proof.
    intros.
    apply to_Zpos_inj_ss; first rewrite !size_low//.
    rewrite !sext_Sn !sext0 !zext_Sn !zext0 !cats1.
    case Hm1 : (msb bs1); case Hm2 : (msb bs2).
    - rewrite mulB_same_sign_bits//.
    - rewrite -!to_Zpos_mod_pow2 2!to_Zpos_full_mul !to_Zpos_rcons !Z.mul_0_l !Z.add_0_r !Z.mul_1_l.
      rewrite -Zmult_mod_idemp_l -Zplus_mod_idemp_r Z_mod_same_full Z.add_0_r.
      rewrite (Z.mod_small _ _ (conj (@to_Zpos_ge0 bs1) (to_Zpos_bounded bs1)))//.
    - rewrite -!to_Zpos_mod_pow2 2!to_Zpos_full_mul !to_Zpos_rcons !Z.mul_0_l !Z.add_0_r !Z.mul_1_l.
      rewrite -Zmult_mod_idemp_r -Zplus_mod_idemp_r H Z_mod_same_full Z.add_0_r.
      rewrite (Z.mod_small _ _ (conj (@to_Zpos_ge0 bs2) (to_Zpos_bounded bs2)))//.
    - rewrite //.
  Qed.

  Lemma msb_mulB_pos bs1 bs2 :
    0 < size bs1 ->
    size bs1 = size bs2 ->
    sig_bits bs1 + sig_bits bs2 <= size bs1 ->
    ~~ (msb bs1) -> ~~ (msb bs2) ->
    ~~ (msb (mulB (sext 1 bs1) (sext 1 bs2))).
  Proof.
    intros.
    rewrite !sext_Sn !cats1 !sext0.
    rewrite -/joinmsb (negbTE H2) (negbTE H3).
    move : (upper_bound bs1); move : (upper_bound bs2); rewrite 2!to_Zpos_ltB 2!to_Zpos_rcons 2!size_zeros 2!Z.mul_1_l 2!to_Zpos_zeros 2!Z.add_0_l => Hbd2 Hbd1.
    move : (Z.mul_lt_mono_nonneg _ _ _ _ (@to_Zpos_ge0 bs1) Hbd1 (@to_Zpos_ge0 bs2) Hbd2).
    rewrite -Z.pow_add_r; try apply Nat2Z.is_nonneg.
    rewrite -Nat2Z.inj_add. have -> : (sig_bits bs1 + sig_bits bs2)%coq_nat = (sig_bits bs1 + sig_bits bs2) by done.
    move => Hmulbd.
    move : H1 => Hsgbbd.
    move/leP : Hsgbbd => Hsgbbd; rewrite -> Nat2Z.inj_le in Hsgbbd.
    move : (Z.lt_le_trans _ _ _ Hmulbd (Z.pow_le_mono_r _ _ _ Z.lt_0_2 Hsgbbd)) => Hmulbd2.
    move : Z.lt_1_2; rewrite (Z.lt_mul_diag_r _ _ (pow2_nat2z_gt0 (size bs1))) => Haux.
    move : (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2)) (Z.lt_trans _ _ _ Hmulbd2 Haux)).
    move : (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2)) Hmulbd2) => Hmodsm1.
    have Haux2 : (2 ^ Z.of_nat (size bs1 + 1) = 2 ^ Z.of_nat (size bs1) *2)%Z.
    {
      rewrite Nat2Z.inj_add Z.pow_add_r; try apply Nat2Z.is_nonneg; rewrite Z.pow_1_r.
      reflexivity.
    }
    rewrite -Haux2 => Hmodsm.
    have Hmul: (joinmsb bs1 false *# joinmsb bs2 false) = (rcons (bs1 *# bs2) false).
    {
      apply to_Zpos_inj_ss; first rewrite !size_rcons !size_mulB !size_joinmsb addn1//.
      rewrite to_Zpos_rcons !to_Zpos_mulB' !to_Zpos_rcons !Z.mul_0_l !Z.add_0_r size_joinmsb.
      rewrite (Z.mod_small _ _ Hmodsm) (Z.mod_small _ _ Hmodsm1)//.
    }
    by rewrite Hmul msb_rcons //.
  Qed.

  Lemma to_Z_Zmul bs1 bs2:
    size bs1 = size bs2 ->
    msb bs1 -> msb bs2 ->
    (to_Z bs1 * to_Z bs2
     = (to_Zpos bs1 * to_Zpos bs2 + 2 ^ Z.of_nat (size bs1 + size bs1) -
                                        2 ^ Z.of_nat (size bs1) * (to_Zpos bs1 + to_Zpos bs2)))%Z.
  Proof.
    intros. rewrite !to_Z_to_Zpos H0 H1 !Z.mul_1_l.
    rewrite Z.mul_sub_distr_r. rewrite 2!Z.mul_sub_distr_l -H.
    rewrite -Z.pow_add_r; try apply Nat2Z.is_nonneg.
    rewrite -Nat2Z.inj_add. have->:(size bs1 + size bs1)%coq_nat= (size bs1 + size bs1) by done.
    rewrite -Z.sub_add_distr Z.add_assoc.
    rewrite (Z.mul_comm (to_Zpos bs1) (2 ^ Z.of_nat (size bs1))) -Z.mul_add_distr_l Z.sub_add_distr Z.sub_opp_r.
    by lia.
  Qed.

  Lemma splitmsb_mulB_sext1 bs1 bs2 :
    0 < size bs1 ->
    size bs1 = size bs2 ->
    bs1 *# bs2 = (splitmsb (sext 1 bs1 *# sext 1 bs2)).1.
  Proof.
    intros. apply to_Zpos_inj_ss; first rewrite size_splitmsb !size_mulB size_sext addnK//.
    rewrite to_Zpos_dropmsb size_mulB size_sext.
    have {1}-> : 1%Z = Z.of_nat 1 by done. rewrite -Nat2Z.inj_sub; last by (apply/leP; apply ltn_addr).
    have -> : (size bs1 + 1 - 1)%coq_nat = (size bs1 + 1 - 1) by done. rewrite addnK.
    rewrite !to_Zpos_mulB' !sext_Sn !sext0 !cats1 !to_Zpos_rcons size_rcons -addn1.
    rewrite -H0 Nat2Z.inj_add Z.pow_add_r; try apply Nat2Z.is_nonneg. symmetry.
    move : (conj (@to_Zpos_ge0 bs1) (to_Zpos_bounded bs1)) => Hbd1.
    move : (conj (@to_Zpos_ge0 bs2) (to_Zpos_bounded bs2)) => Hbd2.
    case Hm1 : (msb bs1); case Hm2 : (msb bs2).
    - rewrite !Z.mul_1_l (Zmod_Zmod_lt _ (pow2_nat2z_gt0 (size bs1)) Z.lt_0_2) Zmult_mod -Zplus_mod_idemp_r Z_mod_same_full Z.add_0_r.
      rewrite -Zplus_mod_idemp_r Z_mod_same_full Z.add_0_r {2}H0 (Z.mod_small _ _ Hbd1) (Z.mod_small _ _ Hbd2)//.
    - rewrite Z.mul_1_l Z.mul_0_l Z.add_0_r (Zmod_Zmod_lt _ (pow2_nat2z_gt0 (size bs1)) Z.lt_0_2) .
      rewrite -Zmult_mod_idemp_l -Zplus_mod_idemp_r Z_mod_same_full Z.add_0_r (Z.mod_small _ _ Hbd1)//.
    - rewrite Z.mul_0_l Z.mul_1_l Z.add_0_r (Zmod_Zmod_lt _ (pow2_nat2z_gt0 (size bs1)) Z.lt_0_2) -Zmult_mod_idemp_r -Zplus_mod_idemp_r.
      rewrite Z_mod_same_full Z.add_0_r {1}H0 (Z.mod_small _ _ Hbd2)//.
    - rewrite !Z.mul_0_l !Z.add_0_r (Zmod_Zmod_lt _ (pow2_nat2z_gt0 (size bs1)) Z.lt_0_2)//.
  Qed.


  Lemma msb_msb_mulB_pos' bs1 bs2 :
    0 < size bs1 ->
    size bs1 = size bs2 ->
    sig_bits bs1 + sig_bits bs2 <= size bs1 ->
    ~~ (msb bs1) -> ~~ (msb bs2) ->
    (msb (mulB (sext 1 bs1) (sext 1 bs2))) = msb (splitmsb (mulB (sext 1 bs1) (sext 1 bs2))).1 ->
    (to_Z (bs1) * to_Z (bs2) < 2 ^ (Z.of_nat (size bs1) - 1))%Z.
  Proof.
    intros.
    have Hsz : 0 < size (sext 1 bs1 *# sext 1 bs2) by rewrite size_mulB size_sext addn1//.
    move : (negbTE (msb_mulB_pos H H0 H1 H2 H3)) => Hmsb.
    rewrite (negbTE (msb_mulB_pos H H0 H1 H2 H3)) in H4.
    move : (to_Zpos_bounded (splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).1).
    rewrite !size_splitmsb size_mulB size_sext addnK.
    have Hsz2 : 0 < size (splitmsb (sext 1 bs1 *# sext 1 bs2)).1 by rewrite size_splitmsb size_mulB size_sext addnK.
    have -> : to_Zpos (splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).1 = to_Zpos (sext 1 bs1 *# sext 1 bs2).
    {
      symmetry. rewrite -{1}(joinmsb_splitmsb Hsz) -/(msb (sext 1 bs1 *# sext 1 bs2)) Hmsb.
      rewrite -{1}(joinmsb_splitmsb Hsz2) -/(msb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1) -H4 !to_Zpos_rcons !Z.mul_0_l !Z.add_0_r//.
    }
    generalize H; rewrite H0 => Hgt02.
    rewrite !sext_Sn !cats1 !sext0 (negbTE H2) (negbTE H3).
    rewrite to_Zpos_mulB' !to_Zpos_rcons !Z.mul_0_l !Z.add_0_r size_rcons -addn1.
    move : (upper_bound bs1); move : (upper_bound bs2); rewrite 2!to_Zpos_ltB 2!to_Zpos_rcons 2!size_zeros 2!Z.mul_1_l 2!to_Zpos_zeros 2!Z.add_0_l => Hbd2 Hbd1.
    move : (Z.mul_lt_mono_nonneg _ _ _ _ (@to_Zpos_ge0 bs1) Hbd1 (@to_Zpos_ge0 bs2) Hbd2).
    rewrite -Z.pow_add_r; try apply Nat2Z.is_nonneg.
    rewrite -Nat2Z.inj_add. have -> : (sig_bits bs1 + sig_bits bs2)%coq_nat = (sig_bits bs1 + sig_bits bs2) by done.
    move => Hmulbd.
    have Hszeq : size (splitmsb bs1).1 = size (splitmsb bs2).1 by rewrite !size_splitmsb H0.
    move : H1 => Hsgbbd.
    move/leP : Hsgbbd => Hsgbbd; rewrite -> Nat2Z.inj_le in Hsgbbd.
    move : (Z.lt_le_trans _ _ _ Hmulbd (Z.pow_le_mono_r _ _ _ Z.lt_0_2 Hsgbbd)) => Hmulbd2.
    move : Z.lt_1_2; rewrite (Z.lt_mul_diag_r _ _ (pow2_nat2z_gt0 (size bs1))) => Haux.
    move : (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2)) (Z.lt_trans _ _ _ Hmulbd2 Haux)).
    have Haux2 : (2 ^ Z.of_nat (size bs1 + 1) = 2 ^ Z.of_nat (size bs1) *2)%Z.
    {
      rewrite Nat2Z.inj_add Z.pow_add_r; try apply Nat2Z.is_nonneg; rewrite Z.pow_1_r.
      reflexivity.
    }
    rewrite -Haux2 => Hmodsm.
    rewrite (Z.mod_small _ _ Hmodsm) Nat2Z.inj_sub//; last by apply/leP.
    rewrite high1_0_to_Z; last rewrite high1_msb (negbTE H2)//.
    rewrite high1_0_to_Z; last rewrite high1_msb (negbTE H3)//.
    done.
  Qed.

  Lemma mulB_negB_negmax bs :
    0 < size bs ->
    msb (mulB bs (rcons (zeros (size bs - 1)) true)) = lsb bs.
  Proof.
    intros.
    move : (to_nat_mulB bs (rcons (zeros (size bs - 1)) true)); rewrite to_nat_rcons size_zeros to_nat_zeros mul1n add0n.
    have Hszsub1 : (size bs - 1 < size bs) by rewrite -{2}(subn0 (size bs)); apply ltn_sub2l.
    generalize Hszsub1; rewrite -(ltn_exp2l _ _ (ltnSn 1)) => Hszsub1'.
    rewrite -{1}(to_nat_from_nat_bounded Hszsub1') -to_nat_mulB -shlB_mul2exp -/(shlB (size bs - 1) bs).
    move/eqP => Haux; rewrite to_nat_inj_ss in Haux; last rewrite size_mulB size_shlB//.
    rewrite (eqP Haux) shlB_cat; last rewrite (ltnW Hszsub1)//.
    rewrite subKn//.
    move : (high1_msb (zeros (size bs - 1) ++ low 1 bs)). rewrite high_size_cat; last rewrite size_low//.
    rewrite low1_lsb => /eqP Haux2.
    rewrite eqseq_cons in Haux2. move/andP : Haux2 => [Haux2 _].
    rewrite {2}(eqP Haux2)//.
  Qed.

  Lemma mulB_negB_negmax' bs :
    0 < size bs ->
    (mulB bs (rcons (zeros (size bs - 1)) true)) = rcons (zeros (size bs -1 )) (lsb bs).
  Proof.
    intros.
    apply/eqP; rewrite -to_nat_inj_ss; last rewrite size_mulB size_rcons size_zeros subn1 (ltn_predK H)//.
    rewrite to_nat_mulB to_nat_rcons size_zeros to_nat_zeros mul1n add0n.
    have Hszsub1 : (size bs - 1 < size bs) by rewrite -{2}(subn0 (size bs)); apply ltn_sub2l.
    generalize Hszsub1; rewrite -(ltn_exp2l _ _ (ltnSn 1)) => Hszsub1'.
    rewrite -{1}(to_nat_from_nat_bounded Hszsub1') -to_nat_mulB -shlB_mul2exp -/(shlB (size bs - 1) bs).
    rewrite shlB_cat; last rewrite (ltnW Hszsub1)//.
    rewrite subKn// -cats1 low1_lsb//.
  Qed.

  Lemma mulB_neg_msb11 bs :
    1 < size bs ->
    msb (mulB (sext 1 bs) (rcons (rcons (zeros (size bs - 1)) true) true)) = xorb (lsb bs) (lsb (high (size bs - 1) bs)).
  Proof.
    intros.
    move : (to_nat_mulB (sext 1 bs) (rcons (rcons (zeros (size bs - 1)) true) true)).
    rewrite -cats1 to_nat_cat to_nat_rcons to_nat_zeros size_rcons size_zeros !mul1n add0n {3}subn1 (ltn_predK H).
    move : (ltnW H) => Hsz.
    have Haux : (2 ^ (size bs - 1) + 2 ^ size bs) < 2 ^ (size (sext 1 bs)).
    {
      rewrite size_sext expnD expn1 muln2 -addnn ltn_add2r ltn_exp2l// -{2}(subn0 (size bs)).
      by apply ltn_sub2l .
    }
    rewrite -(to_nat_from_nat_bounded Haux) -to_nat_mulB mulB_addn.
    have -> : (size (sext 1 bs)) -bits of (2 ^ size bs) = rcons (zeros (size bs)) true.
    {
      apply/eqP; rewrite -to_nat_inj_ss; last rewrite size_from_nat size_rcons size_zeros size_sext addn1//.
      rewrite to_nat_from_nat size_sext to_nat_rcons to_nat_zeros mul1n add0n size_zeros modn_small// ltn_exp2l// addn1//.
    }
    rewrite -{3}(addnK 1 (size bs)) -(size_sext 1 bs) mulB_negB_negmax'; last rewrite size_sext addn1//.
    rewrite -shlB_mul2exp -/(shlB (size bs - 1) (sext 1 bs)).
    move/eqP => {Haux}Haux. rewrite to_nat_inj_ss in Haux; last rewrite size_addB !size_mulB size_shlB size_rcons size_zeros size_sext addnK addn1 minnn//.
    rewrite shlB_cat in Haux; last rewrite size_sext leq_subLR addnC !addn1 -addn2 leq_addr//.
    rewrite size_sext addnK subnBA // !addn1 -addn2 -addnBAC// subnn add0n in Haux.
    rewrite sext_Sn sext0 cats1 in Haux.
    have Haux2 : (low 1 (rcons bs (msb bs)) = low 1 bs) by rewrite low_rcons//.
    move/eqP : Haux2. rewrite 2!low1_lsb eqseq_cons => /andP [Haux2 _].
    rewrite !(eqP Haux2) in Haux.
    have Haux3 : low 2 (rcons bs (msb bs)) = [::lsb (rcons bs (msb bs))] ++ [::lsb (high (size bs - 1) bs)].
    {
      have Hsz' : 0 < size (rcons bs (msb bs)) by rewrite size_rcons//.
      rewrite -{1}(joinlsb_splitlsb Hsz') low_cons low1_lsb cat1s.
      apply/eqP; rewrite eqseq_cons -/(lsb (rcons bs (msb bs))) eq_refl andTb.
      rewrite -droplsb_high subn1 (ltn_predK H) high_size// -/(droplsb (rcons bs (msb bs))) droplsb_joinmsb// /joinmsb -2!low1_lsb low_rcons// size_droplsb subn_gt0//.
    }
    rewrite Haux3 in Haux.
    move => {Haux3}.
    have Haux3 : rcons (zeros (size bs)) (lsb bs) = zeros (size bs - 1) ++ [::b0] ++ [::(lsb bs)].
    {
      apply to_Zpos_inj_ss; first rewrite !size_cat size_rcons !size_zeros/= addn1 addn2 subn1 (ltn_predK Hsz)//.
      rewrite to_Zpos_rcons 2!to_Zpos_cat !to_Zpos_zeros !size_zeros !Z.add_0_l -Z.mul_assoc -Z.pow_add_r; try apply Nat2Z.is_nonneg.
      rewrite (lock Z.of_nat) /= Z.add_0_r -lock Nat2Z.inj_sub//; last by apply/leP. rewrite Zplus_minus//.
    }
    rewrite Haux3 addB_zeros_cats in Haux; last rewrite !size_cat//.
    rewrite sext_Sn cats1 sext0 (eqP Haux) .
    apply/eqP. rewrite -(andbT (msb
    (zeros (size bs - 1) ++
     ([:: lsb (rcons bs (msb bs))] ++ [:: lsb (high (size bs - 1) bs)]) +# ([:: b0] ++ [:: lsb bs])) ==
                                xorb (lsb bs) (lsb (high (size bs - 1) bs)))).
    have Ht : true = (@nil bits == [::]) by rewrite eq_refl//. rewrite Ht.
    rewrite -(eqseq_cons (msb (zeros (size bs - 1) ++ ([:: lsb (rcons bs (msb bs))] ++ [:: lsb (high (size bs - 1) bs)]) +# ([:: b0] ++ [:: lsb bs]))) (xorb (lsb bs) (lsb (high (size bs - 1) bs))) nil nil).
    rewrite -high1_msb -droplsb_high (eqP Haux2) high_size_cat; last rewrite size_addB size_cat//.
    case H1 : (lsb bs); case H2 : (lsb (high (size bs - 1) bs)); rewrite /addB/=droplsb_joinlsb//.
  Qed.

  Lemma mulB_negB_msbmsb11 bs :
    0 < size bs ->
    msb (splitmsb (mulB (sext 1 bs) (rcons (rcons (zeros (size bs - 1)) true) true))).1 = lsb bs.
  Proof.
    intros.
    have -> : rcons (rcons (zeros (size bs - 1)) true) true = sext 1 (rcons (zeros (size bs - 1)) true).
    {
      rewrite sext_Sn sext0 cats1 msb_rcons//.
    }
    rewrite -splitmsb_mulB_sext1//; last rewrite size_rcons size_zeros subn1 (ltn_predK H)//.
    rewrite (mulB_negB_negmax H)//.
  Qed.

  Lemma mulB_negB_negB bs1 bs2 :
    size bs1 = size bs2 ->
    (negB bs1) *# (negB bs2) = bs1 *# bs2.
  Proof.
    move => H.
    move : (to_Zpos_bounded bs1); move : (to_Zpos_bounded bs2); rewrite -Z.lt_sub_0; move/Z.lt_le_incl => Hbd2.
    rewrite /msb -Z.lt_sub_0; move/Z.lt_le_incl => Hbd1.
    case Hz1 : (bs1 == zeros (size bs1)); last case Hz2 : (bs2 == zeros (size bs2)).
    - rewrite (eqP Hz1) (eqP (negB_zeros _)) !mul0B//.
    - rewrite (eqP Hz2) (eqP (negB_zeros _)) mulBC; last rewrite size_negB size_zeros//.
      rewrite !mul0B mulBC; last rewrite size_zeros//. rewrite mul0B//.
    - apply to_Zpos_inj_ss; first rewrite !size_mulB size_negB//.
      rewrite 2!to_Zpos_mulB' size_negB.
      rewrite (neq_zeros_to_Zpos_negB (negbT Hz1)) (neq_zeros_to_Zpos_negB (negbT Hz2)).
      symmetry. rewrite -(Z.opp_involutive (to_Zpos bs1 * to_Zpos bs2)) -Z.mul_opp_l -Z.mul_opp_r Zmult_mod.
      move : (pow2_nat2z_gt0 (size bs1)) => /Z.lt_gt Hgt.
      move : (neq_zeros_to_Zpos_neq0 (negbT Hz1)) => Hneq0z1.
      move : (neq_zeros_to_Zpos_neq0 (negbT Hz2)) => Hneq0z2.
      move : (to_Zpos_mod_pow2 bs1 (size bs1)); rewrite low_size => Hmod1.
      move : (to_Zpos_mod_pow2 bs2 (size bs2)); rewrite low_size => Hmod2.
      rewrite -Hmod1 in Hneq0z1; rewrite -Hmod2 in Hneq0z2.
      rewrite {1}(Z_mod_nz_opp_full _ _ Hneq0z1) {3}H {1}(Z_mod_nz_opp_full _ _ Hneq0z2).
      rewrite (Z.mod_small _ _ (conj (@to_Zpos_ge0 bs1) (to_Zpos_bounded bs1))).
      rewrite (Z.mod_small _ _ (conj (@to_Zpos_ge0 bs2) (to_Zpos_bounded bs2)))//.
  Qed.

  Lemma Smulo_negB_dropmsb_zeors_r bs :
    1 < size bs ->
    msb bs ->
    Smulo bs (joinmsb (zeros (size bs - 1)) true).
  Proof.
    intros.
    rewrite /Smulo splitmsb_joinmsb (lock splitmsb) (lock splitlsb)/= -!lock.
    rewrite -splitmsb_mulB_sext1; [|rewrite (ltnW H)//|rewrite size_joinmsb size_zeros (subnK (ltnW H))//].
    rewrite -/(msb bs) H0.
    rewrite (xorBC (zeros (size bs - 1)) (copy (size (zeros (size bs - 1))) true)) xorB_copy_case invB_zeros.
    rewrite (xorBC (splitmsb bs).1 (copy (size (splitmsb bs).1) true)) xorB_copy_case.
    generalize H; rewrite -subn_gt0 => Hones.
    rewrite -{1}(ltn_predK Hones) -ones_cons splitlsb_joinlsb (lock splitlsb) (lock splitmsb)/=.
    case Hsz : ((size bs - 1).-1) => [ | ns].
    - move/eqP : Hsz; rewrite subn1 -subn2 subn_eq0 leq_eqVlt => /orP [Hsz | Hsz]. apply/orP; right.
      rewrite -lock -/(msb (sext 1 bs *# sext 1 (joinmsb (zeros (size bs).-1) true))) (sext_Sn 0 (joinmsb (zeros (size bs).-1) true)) msb_joinmsb cats1 sext0 /joinmsb.
      rewrite -subn1 mulB_neg_msb11//.
      rewrite mulB_negB_negmax'; last rewrite (ltnW H)//. rewrite splitmsb_rcons (eqP Hsz) subn1 high1_msb H0 /(lsb [::true])/=.
      rewrite Bool.xorb_true_r; by case (lsb bs).
      rewrite ltnNge -ltnS  Hsz // in H.
    - rewrite mulB_negB_negmax'; last rewrite (ltnW H)//.
      rewrite -!lock -/(msb (sext 1 bs *# sext 1 (joinmsb (zeros (size bs -1)) true))) (sext_Sn 0 (joinmsb (zeros (size bs - 1)) true)) msb_joinmsb cats1 sext0.
      rewrite mulB_neg_msb11// splitmsb_rcons.
      case Hn2 : (lsb (high (size bs - 1) bs)). rewrite Bool.xorb_true_r/=. apply/orP; right; by case (lsb bs).
      apply/orP; left.
      have -> : (~~# (splitmsb bs).1) = (splitmsb (~~# bs)).1.
      {
        rewrite -{2}(joinmsb_splitmsb (ltnW H)) invB_rcons splitmsb_joinmsb//.
      }
      rewrite -/(dropmsb (~~# bs)) -/(droplsb (splitmsb (~~# bs)).1) droplsb_dropmsb.
      rewrite -(joinlsb_splitlsb (ltnW H)) invB_cons droplsb_joinlsb -/(droplsb bs).
      have -> : bs = high (size bs - 1).+1 bs.
      {
        rewrite subn1 (ltn_predK (ltnW H)) high_size//.
      }
      rewrite droplsb_high.
      have Hsz' : 0 < size (high (size bs - 1) bs) by rewrite size_high//.
      rewrite -(joinlsb_splitlsb Hsz') -/(lsb (high (size bs - 1) bs)) Hn2 invB_cons. move => {Hsz'}.
      have Hsz' :  size (~~# (splitlsb (high (size bs - 1) bs)).2) = ns.+1.
      {
        rewrite size_invB size_splitlsb size_high (subn1 (size bs - 1)) Hsz//.
      }
      rewrite (eqP (dropmsb_cons true Hsz')) -ones_rcons /ones -rev_copy -rev_cons.
      have Hsz'' : size (dropmsb (~~# (splitlsb (high (size bs - 1) bs)).2)) = size (copy ns b1).
      {
        rewrite size_dropmsb Hsz' size_copy subn1//.
      }
      rewrite (andb_orb_all_b1b1 Hsz'')//.
  Qed.

  Lemma Smulo_negB_dropmsb_zeors_l bs :
    1 < size bs ->
    msb bs ->
    Smulo (joinmsb (zeros (size bs - 1)) true) bs.
  Proof.
    intros.
    rewrite /Smulo splitmsb_joinmsb (lock splitmsb) (lock splitlsb)/= -!lock.
    rewrite -splitmsb_mulB_sext1;
      [|rewrite size_joinmsb size_zeros (subnK (ltnW H)) (ltnW H)//
       |rewrite size_joinmsb size_zeros (subnK (ltnW H))//].
    rewrite -/(msb bs) H0.
    rewrite (xorBC (zeros (size bs - 1)) (copy (size (zeros (size bs - 1))) true)) xorB_copy_case invB_zeros.
    rewrite (xorBC (splitmsb bs).1 (copy (size (splitmsb bs).1) true)) xorB_copy_case.
    generalize H; rewrite -subn_gt0 => Hones.
    rewrite -{1}(ltn_predK Hones) -ones_cons splitlsb_joinlsb (lock splitlsb) (lock splitmsb)/=.
    rewrite mulBC; last rewrite !size_sext size_joinmsb size_zeros !addn1 subn1 (ltn_predK (ltnW H))//.
    have Hsz : size (joinmsb (zeros (size bs - 1)) true)  = size bs by rewrite size_joinmsb size_zeros (subnK (ltnW H)).
    rewrite (mulBC Hsz) => {Hsz}.
    case Hsz : ((size bs - 1).-1) => [ | ns].
    - move/eqP : Hsz; rewrite subn1 -subn2 subn_eq0 leq_eqVlt => /orP [Hsz | Hsz]. apply/orP; right.
      rewrite -lock -/(msb (sext 1 bs *# sext 1 (joinmsb (zeros (size bs).-1) true))) (sext_Sn 0 (joinmsb (zeros (size bs).-1) true)) msb_joinmsb cats1 sext0 /joinmsb.
      rewrite -subn1 mulB_neg_msb11//.
      rewrite mulB_negB_negmax'; last rewrite (ltnW H)//.
      rewrite splitmsb_rcons (eqP Hsz) subn1 high1_msb H0 /(lsb [::true])/=.
      rewrite Bool.xorb_true_r; by case (lsb bs).
      rewrite ltnNge -ltnS  Hsz // in H.
    - rewrite mulB_negB_negmax'; last rewrite (ltnW H)//.
      rewrite -!lock -/(msb _) (sext_Sn 0 (joinmsb (zeros (size bs - 1)) true)) msb_joinmsb cats1 sext0.
      rewrite mulB_neg_msb11// splitmsb_rcons.
      case Hn2 : (lsb (high (size bs - 1) bs));
        first (rewrite Bool.xorb_true_r/=; apply/orP; right; by case (lsb bs)).
      apply/orP; left.
      have -> : (~~# (splitmsb bs).1) = (splitmsb (~~# bs)).1.
      {
        rewrite -{2}(joinmsb_splitmsb (ltnW H)) invB_rcons splitmsb_joinmsb//.
      }
      rewrite -/(dropmsb (~~# bs)) -/(droplsb (splitmsb (~~# bs)).1) droplsb_dropmsb.
      rewrite -(joinlsb_splitlsb (ltnW H)) invB_cons droplsb_joinlsb -/(droplsb bs).
      have -> : bs = high (size bs - 1).+1 bs.
      {
        rewrite subn1 (ltn_predK (ltnW H)) high_size//.
      }
      rewrite droplsb_high.
      have Hsz' : 0 < size (high (size bs - 1) bs) by rewrite size_high//.
      rewrite -(joinlsb_splitlsb Hsz') -/(lsb (high (size bs - 1) bs)) Hn2 invB_cons => {Hsz'}.
      have Hsz' :  size (~~# (splitlsb (high (size bs - 1) bs)).2) = ns.+1.
      {
        rewrite size_invB size_splitlsb size_high (subn1 (size bs - 1)) Hsz//.
      }
      rewrite (eqP (dropmsb_cons true Hsz')) /ones -rev_copy -/(ones _) -ones_cons andb_orb_all_rcons_b1b1//.
      rewrite size_ones size_dropmsb size_invB size_splitlsb size_high (subn1 (size bs - 1)) Hsz -addn1 addnK//.
  Qed.

  Lemma mulB_negB bs1 bs2 : size bs1 = size bs2 -> mulB (negB bs1) bs2 = negB (mulB bs1 bs2).
  Proof.
    move => Hsz.
    apply to_Zpos_inj_ss; first rewrite size_mulB !size_negB size_mulB//.
    rewrite to_Zpos_mulB' size_negB.
    case H10 : (bs1 == zeros (size bs1)).
    - rewrite (eqP H10) (eqP (negB_zeros _)) to_Zpos_zeros Z.mul_0_l size_zeros (Z.mod_0_l _ (Z.neq_sym _ _ (Z.lt_neq _ _ (pow2_nat2z_gt0 _))))//.
      rewrite mul0B (eqP (negB_zeros _ )) to_Zpos_zeros//.
    -
      case H20 : (bs2 == (zeros (size bs2))).
      + rewrite (eqP H20) mulBC; last by rewrite size_zeros//.
        rewrite mul0B (eqP (negB_zeros _)) to_Zpos_zeros !Z.mul_0_r (Z.mod_0_l _ (Z.neq_sym _ _ (Z.lt_neq _ _ (pow2_nat2z_gt0 _))))//.
      + move : (conj (neq_zeros_to_Zpos_neq0 (negbT H10)) (neq_zeros_to_Zpos_neq0 (negbT H20))).
        rewrite ->Z.neq_mul_0 => Hmulneq0.
        rewrite (neq_zeros_to_Zpos_negB (negbT H10)) Z.mul_sub_distr_r Zminus_mod {1}Z.mul_comm Z_mod_mult Z.sub_0_l.
        rewrite to_Zpos_negB to_Zpos_mulB' size_mulB//.
  Qed.

  Lemma to_Z_smulo bs1 bs2 :
    size bs1 = size bs2 ->
    0 < size bs1 ->
    ~~ Smulo bs1 bs2 ->
    (- 2 ^ (Z.of_nat (size bs1) - 1)
     <= to_Z bs1 * to_Z bs2 < 2 ^ (Z.of_nat (size bs1) - 1))%Z.
  Proof.
    intros.
    case Hszgt1 : (1 == size bs1).
    rewrite eq_sym in Hszgt1. generalize Hszgt1; rewrite {1}H; move => Hszgt12. move : H1.
    rewrite (eqP Hszgt1) (size1_msb (eqP (Hszgt1))) (size1_msb (eqP Hszgt12)).
    case Hm1 : (msb bs1) ; case Hm2: (msb bs2); try done.
    have Hsz : 1 < size bs1.
    {
      rewrite ltn_neqAle Hszgt1 H0//.
    }
    move => {H0 Hszgt1}. generalize Hsz; rewrite {1}H => Hsz2.
    move : H1.
    case Hm1 : (splitmsb bs1).2; case Hm2 : (splitmsb bs2).2.
    -
      case Hd1 : (dropmsb bs1 == zeros (size bs1 - 1)); last case Hd2 : (dropmsb bs2 == zeros (size bs2 - 1)).
      move : (Smulo_negB_dropmsb_zeors_l Hsz2 Hm2).
      rewrite -{1}H -(eqP Hd1) -Hm1 (joinmsb_splitmsb (ltnW Hsz)) => Ht. rewrite Ht//.
      move : (Smulo_negB_dropmsb_zeors_r Hsz Hm1).
      rewrite {1}H -(eqP Hd2) -Hm2 (joinmsb_splitmsb (ltnW Hsz2)) => Ht. rewrite Ht//.
      rewrite /Smulo.
      case Haoa : (andb_orb_all (splitlsb ((splitmsb bs1).1 ^# copy (size (splitmsb bs1).1) (splitmsb bs1).2)).2
                                (splitlsb ((splitmsb bs2).1 ^# copy (size (splitmsb bs2).1) (splitmsb bs2).2)).2).
      split; try done. move => H1.
      rewrite negb_or in H1; move/andP : H1 => [_ Hxorb].
      move : (Bool.xorb_eq _ _ (negbTE Hxorb)) => Heqmsb12.
      rewrite Hm1 Hm2 xorBC xorB_copy_case xorBC  xorB_copy_case in Haoa.
      have Hszgt0 : 0 < size ((sext 1 bs1 *# sext 1 bs2)) by rewrite size_mulB size_sext addn1.
      have Hszgt0' : 0 < size ((splitmsb (sext 1 bs1 *# sext 1 bs2)).1).
      {
        rewrite size_splitmsb size_mulB size_sext addnK (ltnW Hsz)//.
      }
      have Hszeq : size (sext 1 bs1) = size (sext 1 bs2) by rewrite !size_sext H.
      have Hszeq': size (~~# (splitmsb bs1).1) = size (~~# (splitmsb bs2).1) by rewrite  !size_invB !size_splitmsb H.
      split.
      + rewrite high1_1_to_Z; last rewrite high1_msb /msb Hm1//.
        rewrite high1_1_to_Z; last rewrite high1_msb /msb Hm2//.
        rewrite Z.mul_opp_opp.
        move : (Z.mul_pos_pos _ _ (Zle_lt_succ _ _ (@to_Zneg_ge0 bs1)) (Zle_lt_succ _ _ (@to_Zneg_ge0 bs2))) => Haux.
        move : (pow2_nat2z_gt0 (size bs1 - 1)); rewrite <-Z.opp_neg_pos => Haux2.
        move : (Z.lt_le_incl _ _ (Z.lt_trans _ _ _ Haux2 Haux)).
        rewrite Nat2Z.inj_sub//; apply/leP; rewrite (ltnW Hsz)//.
      + move : (andb_orb_all_false_sig_bits2 Hszeq' (negbT Haoa)); rewrite size_invB size_splitmsb (subnK (ltnW Hsz)) => Haoa'.
        generalize Haoa'; rewrite -sig_bits_rcons0 -(sig_bits_rcons0 (~~# (splitmsb bs2).1)).
        have {1}-> : b0 = ~~ (splitmsb bs1).2 by rewrite Hm1.
        have {1}-> : b0 = ~~ (splitmsb bs2).2 by rewrite Hm2.
        rewrite -2!invB_rcons -/joinmsb !joinmsb_splitmsb//; [|rewrite -H (ltnW Hsz)//|rewrite (ltnW Hsz)//].
        move => /leP; rewrite Nat2Z.inj_le => Hmulinv.
        move : (Z.pow_le_mono_r _ _ _ Z.lt_0_2 Hmulinv) => Hmulinv'{Hmulinv}.
        move : (upper_bound (~~# bs1)); move : (upper_bound (~~# bs2));
          rewrite !to_Zpos_ltB !to_Zpos_rcons !to_Zpos_zeros !size_zeros !Z.mul_1_l !Z.add_0_l => Hubinv2 Hubinv1.
        move : (Zlt_le_succ _ _ Hubinv1) => {Hubinv1}Hubinv1; move : (Zlt_le_succ _ _ Hubinv2) => {Hubinv2}Hubinv2.
        move : (Z.mul_le_mono_nonneg _ _ _ _ (Z.le_le_succ_r _ _ (@to_Zpos_ge0 (~~# bs1))) Hubinv1 (Z.le_le_succ_r _ _ (@to_Zpos_ge0 (~~# bs2))) Hubinv2).
        have Hh1 : high 1 bs1 = [:: b1] by rewrite high1_msb /msb Hm1.
        have Hh2 : high 1 bs2 = [:: b1] by rewrite high1_msb /msb Hm2.
        rewrite 2!to_Zpos_invB -(Z.opp_involutive ((Z.succ (to_Zneg bs1) * Z.succ (to_Zneg bs2)))) -Z.mul_opp_l -Z.mul_opp_r.
        rewrite -(high1_1_to_Z Hh1) -(high1_1_to_Z Hh2) => {Hh1 Hh2}.
        rewrite -Z.pow_add_r; try by apply Nat2Z.is_nonneg. rewrite -Nat2Z.inj_add.
        have -> : (sig_bits (~~# bs1) + sig_bits (~~# bs2))%coq_nat = (sig_bits (~~# bs1) + sig_bits (~~# bs2)) by done.
        generalize Hm1; rewrite -/(msb bs1); rewrite-> (msb1_to_Z_lt0 bs1).
        generalize Hm2; rewrite -/(msb bs2); rewrite-> (msb1_to_Z_lt0 bs2).
        rewrite -(to_Z_sext bs1 1) -(to_Z_sext bs2 1) => Hneg2 Hneg1.
        rewrite -{1 2}(Z.abs_eq _  (Z.lt_le_incl _ _ (Z.mul_neg_neg _ _ Hneg1 Hneg2))) Z.abs_mul.
        move : (Z.lt_neq _ _ Hneg2); move : (Z.lt_neq _ _ Hneg1); rewrite <- 2!Z.abs_pos.
        rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext /msb Hm1//.
        rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext /msb Hm2//.
        move => Hpos1 Hpos2 Hle' {Hneg1 Hneg2}.
        have H2lt : (2 ^ Z.of_nat (size bs1) < 2 ^ Z.of_nat (size (-# sext 1 bs1)))%Z.
        {
          apply (Z.pow_lt_mono_r); [lia | lia |].
          by apply Nat2Z.inj_lt; rewrite size_negB size_sext addn1 //.
        }
        move : (Z.le_trans _ _ _ Hle' Hmulinv') => /Zle_lt_or_eq [Hlt|Heq].
        move : (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (-# sext 1 bs1)) (@to_Zpos_ge0 (-# sext 1 bs2))) => Hge0.
        move : (Zmod_small _ _ (conj Hge0 (Z.lt_trans _ _ _ Hlt H2lt))) => Hmod {H2lt}.
        rewrite -to_Zpos_mulB' (mulB_negB_negB Hszeq)// in Hmod. move : Hlt; rewrite -Hmod.
        rewrite -(joinmsb_splitmsb Hszgt0) to_Zpos_rcons size_splitmsb size_mulB size_sext.
        move : Heqmsb12. case Hmmsb : ((splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).2); move => Hmsb.
        rewrite Hmsb Z.mul_1_l addnK Z.lt_add_lt_sub_r Z.sub_diag => /Zlt_not_le Hf.
        move : (@to_Zpos_ge0 (splitmsb (sext 1 bs1 *# sext 1 bs2)).1) => Ht. by apply Hf in Ht.
        move => _; rewrite Hmsb Z.mul_0_l Z.add_0_r.
        rewrite -(joinmsb_splitmsb Hszgt0') Hmmsb to_Zpos_rcons Z.mul_0_l Z.add_0_r.
        move : (to_Zpos_bounded (splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).1).
        rewrite !size_splitmsb size_mulB size_sext addnK Nat2Z.inj_sub//; apply/leP; rewrite (ltnW Hsz)//.
        move : (Z.mod_small _ _ (conj (Z.lt_le_incl _ _ (Z.mul_pos_pos _ _ Hpos1 Hpos2)) (Z.le_lt_trans _ _ _ (Z.eq_le_incl _ _ Heq) H2lt))).
        rewrite -{1}(to_Zpos_mulB') {1}Heq (mulB_negB_negB Hszeq).
        have -> : (2 ^ Z.of_nat (size bs1) = to_Zpos (rcons (zeros (size bs1)) b1))%Z.
        {
          rewrite to_Zpos_rcons to_Zpos_zeros Z.mul_1_l Z.add_0_l size_zeros//.
        }
        move => Htozpos.
        have Haux : size (sext 1 bs1 *# sext 1 bs2) = size (rcons (zeros (size bs1)) b1).
        {
          rewrite size_mulB size_sext size_rcons size_zeros addn1//.
        }
        move : (to_Zpos_inj_ss Haux Htozpos) => {Htozpos}Htozpos.
        rewrite Htozpos -{2}(ltn_predK (ltnW Hsz)) -zeros_rcons !splitmsb_rcons // in Heqmsb12.
    - rewrite /Smulo.
      case Haoa : (andb_orb_all (splitlsb ((splitmsb bs1).1 ^# copy (size (splitmsb bs1).1) (splitmsb bs1).2)).2
                                (splitlsb ((splitmsb bs2).1 ^# copy (size (splitmsb bs2).1) (splitmsb bs2).2)).2).
      split; try done. move => H1.
      rewrite negb_or in H1; move/andP : H1 => [_ Hxorb].
      move : (Bool.xorb_eq _ _ (negbTE Hxorb)) => Heqmsb12.
      rewrite Hm1 Hm2 xorBC xorB_copy_case xorBC  xorB_copy_case in Haoa.
      have Hszeq : size (sext 1 bs1) = size (sext 1 bs2) by rewrite !size_sext H.
      have Hszeq' : size (~~#(splitmsb bs1).1) = size ((splitmsb bs2).1) by rewrite size_invB !size_splitmsb H.
      move : (andb_orb_all_false_sig_bits2 Hszeq' (negbT Haoa)).
      rewrite size_invB size_splitmsb (subnK (ltnW Hsz)) => Haoa'.
      generalize Haoa'. rewrite -sig_bits_rcons0 -(sig_bits_rcons0 ((splitmsb bs2).1)).
      have {1}-> : b0 = ~~(splitmsb bs1).2 by rewrite Hm1.
      have {1}-> : b0 = (splitmsb bs2).2 by rewrite Hm2.
      rewrite -invB_rcons -/joinmsb !joinmsb_splitmsb//; [|rewrite -H (ltnW Hsz)//|rewrite (ltnW Hsz)//].
      move => /leP; rewrite Nat2Z.inj_le => Hmulinv.
      move : (Z.pow_le_mono_r _ _ _ Z.lt_0_2 Hmulinv) => Hmulinv'.
      move : (upper_bound (~~# bs1)); move : (upper_bound (sext 1 bs2));
        rewrite !to_Zpos_ltB !to_Zpos_rcons !to_Zpos_zeros !size_zeros !Z.mul_1_l !Z.add_0_l {2}sext_Sn sext0 cats1 /msb Hm2 sig_bits_rcons0.
      move => Hubinv2 Hubinv1.
      move : (Zlt_le_succ _ _ Hubinv1) => {Hubinv1} /Z.opp_le_mono Hubinv1.
      rewrite to_Zpos_invB -high1_1_to_Z in Hubinv1; last rewrite high1_msb /msb Hm1//.
      case Hsg2 : (sig_bits bs2 == 0) .
      + move/eqP : Hsg2 => Hsg2; rewrite -> sig_bits_is0 in Hsg2.
        rewrite Hsg2 to_Z_zeros Z.mul_0_r.
        move : (pow2_nat2z_gt0 (size bs1 -1 )); rewrite Nat2Z.inj_sub//; last (apply/ltP; rewrite (ltnW Hsz)//).
        move => Hp2.
        split; [rewrite Z.opp_nonpos_nonneg; exact : (Z.lt_le_incl _ _ Hp2) | done].
      + move/negbT : Hsg2; rewrite -lt0n => Hsg2.
        have Hsg2' : 0 < sig_bits (sext 1 bs2) by rewrite sext_Sn sext0 cats1 /msb Hm2 sig_bits_rcons0//.
        move : (lower_bound Hsg2'); rewrite to_Zpos_leB;
          last (rewrite size_cat size_joinmsb !size_zeros addn1 (ltn_predK Hsg2') addnBA;
                [rewrite -addnBAC// subnn//|apply sig_bits_le]).
        rewrite to_Zpos_cat to_Zpos_zeros to_Zpos_rcons to_Zpos_zeros size_zeros Z.mul_1_l Z.mul_0_l Z.add_0_l Z.add_0_r => Hlb2.
        generalize Hm1; rewrite -/(msb bs1); rewrite ->(msb1_to_Z_lt0 bs1). move : Hubinv1.
        rewrite -(to_Z_sext bs1 1) -(to_Z_sext bs2 1) => Hubinv1 Hneg1.
        rewrite Z.mul_comm high1_0_to_Z; last rewrite high1_msb msb_sext /msb Hm2//.
        move : (Z.lt_le_trans _ _ _ (pow2_nat2z_gt0 (sig_bits (sext 1 bs2)).-1) Hlb2) => Hpos2; rewrite Z.mul_comm.
        move : (Z.lt_trans _ _ _ (Z.mul_neg_pos _ _ Hneg1 Hpos2) (pow2_nat2z_gt0 (size bs1 - 1))) => Hmulp.
        split; [|move : Hmulp; rewrite Nat2Z.inj_sub//; apply/leP; rewrite (ltnW Hsz)//].
        rewrite Z.opp_le_mono Z.opp_involutive.
        rewrite ->Z.opp_le_mono in Hubinv1; rewrite Z.opp_involutive in Hubinv1.
        rewrite <-Z.opp_pos_neg in Hneg1.
        move : (Z.mul_le_mono_nonneg _ _ _ _ (Z.lt_le_incl _ _ Hneg1) Hubinv1 (Z.lt_le_incl _ _ Hpos2) (Z.lt_le_incl _ _ Hubinv2)).
        rewrite -Z.pow_add_r; try by apply Nat2Z.is_nonneg. rewrite -Nat2Z.inj_add.
        have -> : (sig_bits (~~# bs1) + sig_bits (bs2))%coq_nat = (sig_bits (~~# bs1) + sig_bits (bs2)) by done.
        move => Hle. move : (Z.le_trans _ _ _ Hle Hmulinv') .
        move => {Hle Hlb2}.
        rewrite -Z.mul_opp_l -(Z.abs_eq _ (Z.lt_le_incl _ _ (Z.mul_pos_pos _ _ Hneg1 Hpos2))) Z.abs_mul.
        rewrite Z.abs_opp -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext /msb Hm1//.
        rewrite Z.abs_eq; last exact : (Z.lt_le_incl _ _ Hpos2).
        have Hszgt0 : 0 < size ((sext 1 bs1 *# sext 1 bs2)) by rewrite size_mulB size_sext addn1.
        have Hszgt0' : 0 < size ((splitmsb (sext 1 bs1 *# sext 1 bs2)).1).
        {
          rewrite size_splitmsb size_mulB size_sext addnK (ltnW Hsz)//.
        }
        move => /Zle_lt_or_eq [Hlt|Heq].
        * have Haux2 : (2 ^ Z.of_nat (size bs1) < 2 ^ Z.of_nat (size (-# sext 1 bs1)))%Z.
          {
            rewrite size_negB size_sext; apply Z.pow_lt_mono_r; [lia|apply Nat2Z.is_nonneg|].
            by rewrite -Nat2Z.inj_lt addn1 //.
          }
          move : (Z.lt_trans _ _ _ Hlt Haux2) => {Hmulp Haux2}Hmulp.
          move : (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (-# sext 1 bs1)) (@to_Zpos_ge0 (sext 1 bs2))) Hmulp) => Hmodsm.
          move : (Z.mod_small _ _ Hmodsm); rewrite -to_Zpos_mulB' => Hmulmod.
          move : Hlt; rewrite -Hmulmod (mulB_negB Hszeq).
          move : Heqmsb12; case Hmmsb : (splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).2; move => Hmsb.
          { move => Hub. rewrite high1_1_to_Zpos_negB; last rewrite high1_msb /msb Hmsb//.
            rewrite Z.abs_neq; last (apply Z.lt_le_incl; rewrite -msb1_to_Z_lt0 /msb Hmsb//).
            rewrite to_Z_to_Zpos /msb Hmsb Z.mul_1_l size_mulB size_sext.
            rewrite -(joinmsb_splitmsb Hszgt0) Hmsb to_Zpos_rcons Z.mul_1_l size_splitmsb size_mulB size_sext addnK.
            rewrite -(joinmsb_splitmsb Hszgt0') Hmmsb to_Zpos_rcons Z.mul_1_l !size_splitmsb size_mulB size_sext addnK.
            rewrite Z.opp_le_mono Z.opp_involutive -Z.le_0_sub Z.sub_opp_r -Z.add_opp_r.
            rewrite -Z.add_assoc Z.add_shuffle2.
            rewrite -(Z.add_assoc (to_Zpos (splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).1) (2 ^ Z.of_nat (size bs1 - 1)) (2 ^ (Z.of_nat (size bs1) - 1))).
            have {1}->: 1%Z = (Z.of_nat 1) by done.
            rewrite -Nat2Z.inj_sub; last (apply/leP; rewrite (ltnW Hsz)//).
            have ->: (size bs1 - 1)%coq_nat = (size bs1 - 1) by done.
            rewrite Zred_factor1 -{2}(Z.pow_1_r 2) -Z.pow_add_r; [|apply Nat2Z.is_nonneg|lia].
            rewrite Z.add_shuffle1 Z.add_shuffle2. have {1}->: 1%Z = (Z.of_nat 1) by done.
            rewrite -Nat2Z.inj_add. have -> :(size bs1 - 1 + 1)%coq_nat = (size bs1 - 1 + 1) by done.
            rewrite (subnK (ltnW Hsz)) Zred_factor1 -{3}(Z.pow_1_r 2) -Z.pow_add_r; [|apply Nat2Z.is_nonneg|lia].
            have {1}->: 1%Z = (Z.of_nat 1) by done. rewrite -Nat2Z.inj_add.
            have -> :(size bs1 + 1)%coq_nat = (size bs1 + 1) by done.
            rewrite -Z.add_assoc Z.add_opp_diag_l Z.add_0_r. apply to_Zpos_ge0.
          }
          {
            move : (Z.mul_pos_pos _ _ Hneg1 Hpos2).
            rewrite -(Z.abs_eq _ (Z.lt_le_incl _ _ Hneg1)) Z.abs_opp -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext /msb Hm1//.
            move/Z.lt_neq/Z.neq_sym => Hneq0; rewrite -Hmulmod in Hneq0.
            case Hmul0 : ((sext 1 bs1 *# sext 1 bs2) == zeros (size bs1 + 1));
              first rewrite (mulB_negB Hszeq) (eqP Hmul0) (eqP (negB_zeros _)) to_Zpos_zeros // in Hneq0.
            rewrite (neq_zeros_to_Zpos_negB) size_mulB size_sext; last rewrite Hmul0//.
            rewrite Z.lt_sub_lt_add_r -Z.lt_sub_lt_add_l {1}Nat2Z.inj_add {1}Z.pow_add_r; try apply Nat2Z.is_nonneg.
            rewrite -Zred_factor1 Z.add_simpl_l.
            rewrite -(joinmsb_splitmsb Hszgt0) Hmsb to_Zpos_rcons Z.mul_0_l Z.add_0_r.
            move : (to_Zpos_bounded (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).
            rewrite size_splitmsb size_mulB size_sext addnK => Ht /Z.lt_asymm Hf//.
          }
        * move : Heq.
          move => Hmodeq.
          have Hmodsm : ((to_Zpos (-# sext 1 bs1) * to_Zpos (sext 1 bs2)) < (2 ^ Z.of_nat (size (-# sext 1 bs1))))%Z.
          {
            rewrite Hmodeq size_negB size_sext.
            apply Z.pow_lt_mono_r;
              [rewrite //| apply Nat2Z.is_nonneg |apply Nat2Z.inj_lt; apply/ltP; rewrite addn1//].
          }
          move : (Z.mod_small _ _ (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (-# sext 1 bs1)) (@to_Zpos_ge0 (sext 1 bs2))) Hmodsm)).
          rewrite -to_Zpos_mulB' => {Hszeq}. rewrite Hmodeq.
          have Hszeq : size (sext 1 bs1) = size (sext 1 bs2) by rewrite !size_sext H.
          rewrite (mulB_negB Hszeq).
          have -> : (2 ^ Z.of_nat (size bs1) = to_Zpos (joinmsb (zeros (size (-# (sext 1 bs1 *# sext 1 bs2)) - 1)) b1))%Z.
          {
            rewrite to_Zpos_rcons size_negB size_mulB size_sext size_zeros addnK to_Zpos_zeros Z.mul_1_l Z.add_0_l//.
          }
          have Haux : size (-# (sext 1 bs1 *# sext 1 bs2)) = size (joinmsb (zeros (size (-# (sext 1 bs1 *# sext 1 bs2)) - 1)) b1).
          {
            rewrite size_negB size_joinmsb size_zeros size_mulB size_sext addnK//.
          }
          move => /(to_Zpos_inj_ss Haux) {Haux} Heq0.
          have Hdmul : dropmsb (-# (sext 1 bs1 *# sext 1 bs2)) == zeros (size (-# (sext 1 bs1 *# sext 1 bs2)) - 1).
          {
            rewrite Heq0 dropmsb_joinmsb size_joinmsb size_zeros addnK//.
          }
          move : (dropmsb_0_negB_id Hdmul); rewrite negB_involutive => Hneg {Hszeq}.
          move : Heqmsb12; rewrite Hneg Heq0 splitmsb_joinmsb size_negB size_mulB size_sext addnK -(ltn_predK (ltnW Hsz)).
          rewrite -zeros_rcons splitmsb_joinmsb//.
    - rewrite /Smulo.
      case Haoa : (andb_orb_all (splitlsb ((splitmsb bs1).1 ^# copy (size (splitmsb bs1).1) (splitmsb bs1).2)).2
                                (splitlsb ((splitmsb bs2).1 ^# copy (size (splitmsb bs2).1) (splitmsb bs2).2)).2).
      split; try done. move => H1.
      rewrite negb_or in H1; move/andP : H1 => [_ Hxorb].
      move : (Bool.xorb_eq _ _ (negbTE Hxorb)) => Heqmsb12.
      rewrite Hm1 Hm2 xorBC xorB_copy_case xorBC  xorB_copy_case in Haoa.
      have Hszeq : size (sext 1 bs1) = size (-# sext 1 bs2) by rewrite size_negB !size_sext H.
      have Hszeq' : size ((splitmsb bs1).1) = size (~~#(splitmsb bs2).1) by rewrite size_invB !size_splitmsb H.
      move : (andb_orb_all_false_sig_bits2 Hszeq' (negbT Haoa)).
      rewrite size_splitmsb (subnK (ltnW Hsz)) => Haoa'.
      generalize Haoa'. rewrite -sig_bits_rcons0 -(sig_bits_rcons0 (~~#(splitmsb bs2).1)).
      have {1}-> : b0 = (splitmsb bs1).2 by rewrite Hm1.
      have {1}-> : b0 = ~~(splitmsb bs2).2 by rewrite Hm2.
      rewrite -invB_rcons -/joinmsb !joinmsb_splitmsb//; [|rewrite -H (ltnW Hsz)//|rewrite (ltnW Hsz)//].
      move => /leP; rewrite Nat2Z.inj_le => Hmulinv.
      move : (Z.pow_le_mono_r _ _ _ Z.lt_0_2 Hmulinv) => Hmulinv'.
      move : (upper_bound (~~# bs2)); move : (upper_bound (sext 1 bs1));
        rewrite !to_Zpos_ltB !to_Zpos_rcons !to_Zpos_zeros !size_zeros !Z.mul_1_l !Z.add_0_l {2}sext_Sn sext0 cats1 /msb Hm1 sig_bits_rcons0.
      move => Hubinv1 Hubinv2.
      move : (Zlt_le_succ _ _ Hubinv2) => {Hubinv2} /Z.opp_le_mono Hubinv2.
      rewrite to_Zpos_invB -high1_1_to_Z in Hubinv2; last rewrite high1_msb /msb Hm2//.
      case Hsg1 : (sig_bits bs1 == 0) .
      + move/eqP : Hsg1 => Hsg1; rewrite -> sig_bits_is0 in Hsg1.
        rewrite Hsg1 to_Z_zeros Z.mul_0_l size_zeros.
        move : (pow2_nat2z_gt0 (size bs1 -1 )); rewrite Nat2Z.inj_sub//; last (apply/ltP; rewrite (ltnW Hsz)//).
        move => Hp2.
        split; [rewrite Z.opp_nonpos_nonneg; exact : (Z.lt_le_incl _ _ Hp2) | done].
      + move/negbT : Hsg1; rewrite -lt0n => Hsg1.
        have Hsg1' : 0 < sig_bits (sext 1 bs1) by rewrite sext_Sn sext0 cats1 /msb Hm1 sig_bits_rcons0//.
        move : (lower_bound Hsg1'); rewrite to_Zpos_leB;
          last (rewrite size_cat size_joinmsb !size_zeros addn1 (ltn_predK Hsg1') addnBA;
                [rewrite -addnBAC// subnn//|apply sig_bits_le]).
        rewrite to_Zpos_cat to_Zpos_rcons !to_Zpos_zeros size_zeros Z.mul_1_l Z.mul_0_l Z.add_0_l Z.add_0_r => Hlb1.
        generalize Hm2; rewrite -/(msb bs2); rewrite ->(msb1_to_Z_lt0 bs2). move : Hubinv2.
        rewrite -(to_Z_sext bs1 1) -(to_Z_sext bs2 1) => Hubinv2 Hneg2.
        rewrite high1_0_to_Z; last rewrite high1_msb msb_sext /msb Hm1//.
        move : (Z.lt_le_trans _ _ _ (pow2_nat2z_gt0 (sig_bits (sext 1 bs1)).-1) Hlb1) => Hpos1.
        move : (Z.lt_trans _ _ _ (Z.mul_pos_neg _ _ Hpos1 Hneg2) (pow2_nat2z_gt0 (size bs1 - 1))) => Hmulp.
        split; [|move : Hmulp; rewrite Nat2Z.inj_sub//; apply/leP; rewrite (ltnW Hsz)//].
        rewrite Z.opp_le_mono Z.opp_involutive.
        rewrite ->Z.opp_le_mono in Hubinv2; rewrite Z.opp_involutive in Hubinv2.
        rewrite <-Z.opp_pos_neg in Hneg2.
        move : (Z.mul_le_mono_nonneg _ _ _ _ (Z.lt_le_incl _ _ Hpos1) (Z.lt_le_incl _ _ Hubinv1) (Z.lt_le_incl _ _ Hneg2) Hubinv2).
        rewrite -Z.pow_add_r; try by apply Nat2Z.is_nonneg. rewrite -Nat2Z.inj_add.
        have -> : (sig_bits (bs1) + sig_bits (~~#bs2))%coq_nat = (sig_bits (bs1) + sig_bits (~~#bs2)) by done.
        move => Hle. move : (Z.le_trans _ _ _ Hle Hmulinv') .
        move => {Hle Hlb1}.
        rewrite -Z.mul_opp_r -(Z.abs_eq _ (Z.lt_le_incl _ _ (Z.mul_pos_pos _ _ Hpos1 Hneg2))) Z.abs_mul.
        rewrite Z.abs_opp -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext /msb Hm2//.
        rewrite Z.abs_eq; last exact : (Z.lt_le_incl _ _ Hpos1).
        have Hszgt0 : 0 < size ((sext 1 bs1 *# sext 1 bs2)) by rewrite size_mulB size_sext addn1.
        have Hszgt0' : 0 < size ((splitmsb (sext 1 bs1 *# sext 1 bs2)).1).
        {
          rewrite size_splitmsb size_mulB size_sext addnK (ltnW Hsz)//.
        }
        move => /Zle_lt_or_eq [Hlt|Heq].
        * have Haux2 : (2 ^ Z.of_nat (size bs1) < 2 ^ Z.of_nat (size (sext 1 bs1)))%Z.
          {
            rewrite size_sext; apply Z.pow_lt_mono_r; [lia|apply Nat2Z.is_nonneg|].
            rewrite -Nat2Z.inj_lt addn1//.
          }
          move : (Z.lt_trans _ _ _ Hlt Haux2) => {Hmulp Haux2}Hmulp.
          move : (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (sext 1 bs1)) (@to_Zpos_ge0 (-# sext 1 bs2))) Hmulp) => Hmodsm.
          move : (Z.mod_small _ _ Hmodsm); rewrite -to_Zpos_mulB' => Hmulmod.
          move : Hlt; rewrite -Hmulmod (mulBC Hszeq) mulB_negB; last rewrite !size_sext H//.
          rewrite mulBC; last rewrite !size_sext H//.
          move : Heqmsb12; case Hmmsb : (splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).2; move => Hmsb.
          {
            move => Hub. rewrite high1_1_to_Zpos_negB; last rewrite high1_msb /msb Hmsb//.
            rewrite Z.abs_neq; last (apply Z.lt_le_incl; rewrite -msb1_to_Z_lt0 /msb Hmsb//).
            rewrite to_Z_to_Zpos /msb Hmsb Z.mul_1_l size_mulB size_sext.
            rewrite -(joinmsb_splitmsb Hszgt0) Hmsb to_Zpos_rcons Z.mul_1_l size_splitmsb size_mulB size_sext addnK.
            rewrite -(joinmsb_splitmsb Hszgt0') Hmmsb to_Zpos_rcons Z.mul_1_l !size_splitmsb size_mulB size_sext addnK.
            rewrite Z.opp_le_mono Z.opp_involutive -Z.le_0_sub Z.sub_opp_r -Z.add_opp_r.
            rewrite -Z.add_assoc Z.add_shuffle2.
            rewrite -(Z.add_assoc (to_Zpos (splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).1) (2 ^ Z.of_nat (size bs1 - 1)) (2 ^ (Z.of_nat (size bs1) - 1))).
            have {1}->: 1%Z = (Z.of_nat 1) by done.
            rewrite -Nat2Z.inj_sub; last (apply/leP; rewrite (ltnW Hsz)//).
            have ->: (size bs1 - 1)%coq_nat = (size bs1 - 1) by done.
            rewrite Zred_factor1 -{2}(Z.pow_1_r 2) -Z.pow_add_r; [|apply Nat2Z.is_nonneg|lia].
            rewrite Z.add_shuffle1 Z.add_shuffle2. have {1}->: 1%Z = (Z.of_nat 1) by done.
            rewrite -Nat2Z.inj_add. have -> :(size bs1 - 1 + 1)%coq_nat = (size bs1 - 1 + 1) by done.
            rewrite (subnK (ltnW Hsz)) Zred_factor1 -{3}(Z.pow_1_r 2) -Z.pow_add_r; [|apply Nat2Z.is_nonneg|lia].
            have {1}->: 1%Z = (Z.of_nat 1) by done. rewrite -Nat2Z.inj_add.
            have -> :(size bs1 + 1)%coq_nat = (size bs1 + 1) by done.
            rewrite -Z.add_assoc Z.add_opp_diag_l Z.add_0_r. apply to_Zpos_ge0.
          }
          {
            move : (Z.mul_pos_pos _ _ Hpos1 Hneg2).
            rewrite -(Z.abs_eq _ (Z.lt_le_incl _ _ Hneg2)) Z.abs_opp -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext /msb Hm2//.
            move/Z.lt_neq/Z.neq_sym => Hneq0; rewrite -Hmulmod in Hneq0.
            case Hmul0 : ((sext 1 bs1 *# sext 1 bs2) == zeros (size bs1 + 1)).
            rewrite (mulBC Hszeq) mulB_negB in Hneq0; last rewrite !size_sext H//.
            rewrite mulBC in Hneq0 ; last rewrite !size_sext H//.
            rewrite (eqP Hmul0) (eqP (negB_zeros _)) to_Zpos_zeros // in Hneq0.
            rewrite (neq_zeros_to_Zpos_negB) size_mulB size_sext; last rewrite Hmul0//.
            rewrite Z.lt_sub_lt_add_r -Z.lt_sub_lt_add_l {1}Nat2Z.inj_add {1}Z.pow_add_r; try apply Nat2Z.is_nonneg.
            rewrite -Zred_factor1 Z.add_simpl_l.
            rewrite -(joinmsb_splitmsb Hszgt0) Hmsb to_Zpos_rcons Z.mul_0_l Z.add_0_r.
            move : (to_Zpos_bounded (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).
            rewrite size_splitmsb size_mulB size_sext addnK => Ht /Z.lt_asymm Hf//.
          }
        * move : Heq => Hmodeq.
          have Hmodsm : ((to_Zpos (sext 1 bs1) * to_Zpos (-# sext 1 bs2)) < (2 ^ Z.of_nat (size (sext 1 bs1))))%Z.
          {
            rewrite Hmodeq size_sext.
            apply Z.pow_lt_mono_r;
              [rewrite //| apply Nat2Z.is_nonneg |apply Nat2Z.inj_lt; apply/ltP; rewrite addn1//].
          }
          move : (Z.mod_small _ _ (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (sext 1 bs1)) (@to_Zpos_ge0 (-# sext 1 bs2))) Hmodsm)).
          rewrite -to_Zpos_mulB' => {Hszeq}. rewrite Hmodeq.
          have Hszeq : size (sext 1 bs1) = size (-#sext 1 bs2) by rewrite size_negB !size_sext H.
          rewrite (mulBC Hszeq) (mulB_negB); last rewrite !size_sext H//.
          rewrite mulBC; last rewrite !size_sext H//.
          have -> : (2 ^ Z.of_nat (size bs1) = to_Zpos (joinmsb (zeros (size (-# (sext 1 bs1 *# sext 1 bs2)) - 1)) b1))%Z.
          {
            rewrite to_Zpos_rcons size_negB size_mulB size_sext size_zeros addnK to_Zpos_zeros Z.mul_1_l Z.add_0_l//.
          }
          have Haux : size (-# (sext 1 bs1 *# sext 1 bs2)) = size (joinmsb (zeros (size (-# (sext 1 bs1 *# sext 1 bs2)) - 1)) b1).
          {
            rewrite size_negB size_joinmsb size_zeros size_mulB size_sext addnK//.
          }
          move => /(to_Zpos_inj_ss Haux) {Haux} Heq0.
          have Hdmul : dropmsb (-# (sext 1 bs1 *# sext 1 bs2)) == zeros (size (-# (sext 1 bs1 *# sext 1 bs2)) - 1).
          {
            rewrite Heq0 dropmsb_joinmsb size_joinmsb size_zeros addnK//.
          }
          move : (dropmsb_0_negB_id Hdmul); rewrite negB_involutive => Hneg {Hszeq}.
          move : Heqmsb12; rewrite Hneg Heq0 splitmsb_joinmsb size_negB size_mulB size_sext addnK -(ltn_predK (ltnW Hsz)).
          rewrite -zeros_rcons splitmsb_joinmsb//.
      + rewrite /Smulo.
        case Haoa : (andb_orb_all (splitlsb ((splitmsb bs1).1 ^# copy (size (splitmsb bs1).1) (splitmsb bs1).2)).2
                                (splitlsb ((splitmsb bs2).1 ^# copy (size (splitmsb bs2).1) (splitmsb bs2).2)).2).
        split; try done. move => H1.
        rewrite negb_or in H1; move/andP : H1 => [_ Hxorb].
        move : (Bool.xorb_eq _ _ (negbTE Hxorb)) => Heqmsb12.
        rewrite Hm1 Hm2 xorBC xorB_copy_case xorBC  xorB_copy_case in Haoa.
        have Hszeq: size ((splitmsb bs1).1) = size ((splitmsb bs2).1) by rewrite !size_splitmsb H.
        move : (andb_orb_all_false_sig_bits2 Hszeq (negbT Haoa)).
        rewrite size_splitmsb (subnK (ltnW Hsz)) => Haoa'.
        generalize Haoa'. rewrite -sig_bits_rcons0 -(sig_bits_rcons0 ((splitmsb bs2).1)).
        have {1}-> : b0 = (splitmsb bs1).2 by rewrite Hm1.
        have {1}-> : b0 = (splitmsb bs2).2 by rewrite Hm2.
        rewrite -/joinmsb !joinmsb_splitmsb//; [|rewrite -H (ltnW Hsz)//|rewrite (ltnW Hsz)//] => Hsgadd.
        move : (msb_msb_mulB_pos' (ltnW Hsz) H Hsgadd (negbT Hm1) (negbT Hm2) Heqmsb12) => Hlt.
        split; last done. rewrite high1_0_to_Z; last rewrite high1_msb /msb Hm1//.
        rewrite high1_0_to_Z; last rewrite high1_msb /msb Hm2//.
        move : (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2)) => Hge0.
        move : (pow2_nat2z_gt0 (size bs1 - 1)); rewrite -Z.opp_neg_pos => Hlt0.
        move : (Z.lt_le_incl _ _ (Z.lt_le_trans _ _ _ Hlt0 Hge0)); rewrite Nat2Z.inj_sub; last (apply/ltP; rewrite (ltnW Hsz)//).
        done.
  Qed.

  Lemma sext_neq_zeros bs :
   (sext 1 bs == zeros (size bs + 1)) <-> bs == zeros (size bs).
  Proof.
    split.
    rewrite addn1 -zeros_rcons sext_Sn sext0 cats1.
      by rewrite eqseq_rcons => /andP [H H'].
    move/eqP => ->. rewrite sext_Sn sext0 cats1 msb_zeros zeros_rcons size_zeros addn1//.
  Qed.

  Lemma neq_copy_rev_neq_copy m: ~~(m == zeros (size m)) -> ~~(rev m == zeros (size (rev m))).
  Proof.
    move => Hmn0.
    have Hfeq : (rev m == (rev (zeros (size m))) -> m == zeros (size m)).
    by move/eqP => Hrm; move : (f_equal rev Hrm) => Hm; rewrite 2!revK in Hm; apply/eqP.
    rewrite /zeros -(rev_copy) -/(zeros (size (rev m))) size_rev. exact : (contra Hfeq Hmn0).
  Qed.

  Lemma msb_mulB_signed bs1 bs2 :
    size bs1 = size bs2 ->
    ~~ Smulo bs1 bs2 ->
    ~~ (bs1 == zeros (size bs1)) -> ~~ (bs2 == zeros (size bs2)) ->
    msb (bs1 *# bs2) = ~~ (msb bs1 == msb bs2).
  Proof.
    intros .
    case Hszgt0 : (0 < size bs1);
      last (move/negbT: Hszgt0; rewrite -eqn0Ngt => /eqP /size0nil; move => Hn; rewrite Hn //in H1).
    move : (to_Z_smulo H Hszgt0 H0).
    have -> : 1%Z = Z.of_nat 1 by done. rewrite -Nat2Z.inj_sub; last by apply/leP.
    have -> : (size bs1 - 1)%coq_nat = (size bs1 - 1) by done.
    have Hszgt0' : 0 < size ((sext 1 bs1 *# sext 1 bs2)) by rewrite size_mulB size_sext addn1.
    have Haux : (2 ^ Z.of_nat (size bs1 - 1) < 2 ^ Z.of_nat (size bs1 + 1))%Z.
    {
      apply Z.pow_lt_mono_r;
        [rewrite//|apply Nat2Z.is_nonneg|rewrite -Nat2Z.inj_lt//; apply/ltP; rewrite -(ltn_add2r 1) (subnK Hszgt0) addn1 leq_addr//].
    }
    case Hs1 : (sext 1 bs1 == zeros (size bs1 + 1)). rewrite ->(sext_neq_zeros bs1) in Hs1; rewrite Hs1 // in H1.
    case Hs2 : (sext 1 bs2 == zeros (size bs2 + 1)). rewrite ->(sext_neq_zeros bs2) in Hs2; rewrite Hs2 // in H2.
    case Hns1 : (-# sext 1 bs1 == zeros (size (-#sext 1 bs1))).
    rewrite ->(negB_zeros' (-# sext 1 bs1)) in Hns1; rewrite negB_involutive size_sext in Hns1; rewrite Hns1 // in Hs1.
    case Hns2 : (-# sext 1 bs2 == zeros (size (-#sext 1 bs2))).
    rewrite ->(negB_zeros' (-# sext 1 bs2)) in Hns2; rewrite negB_involutive size_sext in Hns2; rewrite Hns2 // in Hs2.
    move : H0; rewrite /Smulo.
    case Haoa : (andb_orb_all (splitlsb ((splitmsb bs1).1 ^# copy (size (splitmsb bs1).1) (splitmsb bs1).2)).2
                              (splitlsb ((splitmsb bs2).1 ^# copy (size (splitmsb bs2).1) (splitmsb bs2).2)).2); first done.
    move => Hor; rewrite negb_or in Hor; move/andP : Hor => [_ Hxorb].
    move : (Bool.xorb_eq _ _ (negbTE Hxorb)) => Heqmsb12.
    rewrite splitmsb_mulB_sext1//.
    rewrite xorBC xorB_copy_case xorBC  xorB_copy_case -/(msb bs1) -/(msb bs2) in Haoa.
    move : Haoa.
    case Hm1 : (msb bs1); case Hm2 : (msb bs2);
      move => Haoa; move : Heqmsb12; rewrite /msb;
                case Hmmsb : ((splitmsb (splitmsb (sext 1 bs1 *# sext 1 bs2)).1).2); move => Hmsb; try done.
    - rewrite -(to_Z_sext bs1 1) -(Z.abs_sgn (to_Z (sext 1 bs1))) Z.sgn_neg; last rewrite to_Z_sext -msb1_to_Z_lt0//.
      rewrite -(to_Z_sext bs2 1) -(Z.abs_sgn (to_Z (sext 1 bs2))) Z.sgn_neg; last rewrite to_Z_sext -msb1_to_Z_lt0//.
      rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext Hm1//.
      rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext Hm2//.
      rewrite -!Z.opp_eq_mul_m1 Z.mul_opp_opp; move => [Hge Hlt].
      move : (Z.mod_small _ _ (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (-# sext 1 bs1)) (@to_Zpos_ge0 (-# sext 1 bs2))) (Z.lt_trans _ _ _ Hlt Haux))).
      rewrite -(size_sext) -(size_negB) -to_Zpos_mulB' mulB_negB_negB; last rewrite !size_sext H//.
      move => Hmulmod ; move : Hlt.
      rewrite -Hmulmod -(joinmsb_splitmsb Hszgt0') Hmsb to_Zpos_rcons Z.mul_1_l size_splitmsb size_mulB size_sext addnK Z.lt_add_lt_sub_r => Hlt.
      have Haux' : (2 ^ Z.of_nat (size bs1 - 1) < 2 ^ Z.of_nat (size bs1))%Z.
      {
        apply Z.pow_lt_mono_r;
          [rewrite//|apply Nat2Z.is_nonneg|rewrite -Nat2Z.inj_lt//; apply/ltP; rewrite -(ltn_add2r 1) (subnK Hszgt0) addn1//].
      }
      rewrite <-Z.lt_sub_0 in Haux'. move : (Z.lt_trans _ _ _ Hlt Haux') => /Zlt_not_le Hlt'.
        by move : (@to_Zpos_ge0 (splitmsb (sext 1 bs1 *# sext 1 bs2)).1) => /Hlt' .
    - rewrite -(to_Z_sext bs1 1) -(Z.abs_sgn (to_Z (sext 1 bs1))) Z.sgn_neg; last rewrite to_Z_sext -msb1_to_Z_lt0//.
      rewrite -(to_Z_sext bs2 1).
      rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext Hm1//.
      rewrite high1_0_to_Z; last rewrite high1_msb msb_sext Hm2//.
      rewrite -!Z.opp_eq_mul_m1 Z.mul_opp_l; move => [Hge Hlt].
      rewrite <-Z.opp_le_mono in Hge.
      rewrite -size_sext in Hs1; rewrite -size_sext in Hs2.
      move : (Z.mul_pos_pos _ _ (neq_zeros_to_Zpos_gt0 (negbT Hns1)) (neq_zeros_to_Zpos_gt0 (negbT Hs2))) => Hgt0.
      move : (Z.mod_small _ _ (conj (Z.lt_le_incl _ _ Hgt0) (Z.le_lt_trans _ _ _ Hge Haux))).
      rewrite -(size_sext) -(size_negB) -to_Zpos_mulB' mulB_negB; last rewrite !size_sext H//; move => Hmulmod.
      move : Hgt0 Hge; rewrite -Hmulmod => Hgt0.
      case Hmul : (((sext 1 bs1 *# sext 1 bs2)) == zeros (size ((sext 1 bs1 *# sext 1 bs2)))).
      rewrite (eqP Hmul) (eqP (negB_zeros _)) to_Zpos_zeros // in Hgt0.
      rewrite (neq_zeros_to_Zpos_negB (negbT Hmul)) size_mulB size_sext -(joinmsb_splitmsb Hszgt0') Hmsb /joinmsb to_Zpos_rcons.
      rewrite Z.mul_0_l Z.add_0_r.
      move : (to_Zpos_bounded (splitmsb (sext 1 bs1 *# sext 1 bs2)).1); rewrite size_splitmsb size_mulB size_sext addnK => Hs1bd.
      rewrite ->Z.le_sub_le_add_r; rewrite <-Z.le_sub_le_add_l => Hf.
      move : (Z.le_lt_trans _ _ _ Hf Hs1bd).
      rewrite Z.lt_sub_lt_add_l Nat2Z.inj_add Z.pow_add_r; [| lia | lia].
      rewrite -Zred_factor1 -Z.add_lt_mono_r.
      rewrite <-Z.pow_lt_mono_r_iff; [| lia | lia]. rewrite -Nat2Z.inj_lt => /ltP Hf'.
      by rewrite -subn_gt0 -subnDA addnC subnDA subnn // in Hf'.
    - rewrite -(to_Z_sext bs2 1) -(Z.abs_sgn (to_Z (sext 1 bs2))) Z.sgn_neg; last rewrite to_Z_sext -msb1_to_Z_lt0//.
      rewrite -(to_Z_sext bs1 1).
      rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb msb_sext Hm2//.
      rewrite high1_0_to_Z; last rewrite high1_msb msb_sext Hm1//.
      rewrite -!Z.opp_eq_mul_m1 Z.mul_opp_r; move => [Hge Hlt].
      rewrite <-Z.opp_le_mono in Hge.
      rewrite -size_sext in Hs1; rewrite -size_sext in Hs2.
      move : (Z.mul_pos_pos _ _ (neq_zeros_to_Zpos_gt0 (negbT Hs1)) (neq_zeros_to_Zpos_gt0 (negbT Hns2))) => Hgt0.
      move : (Z.mod_small _ _ (conj (Z.lt_le_incl _ _ Hgt0) (Z.le_lt_trans _ _ _ Hge Haux))).
      rewrite -(size_sext) -to_Zpos_mulB' mulBC; last rewrite size_negB !size_sext H//; move => Hmulmod.
      rewrite mulB_negB in Hmulmod; last rewrite !size_sext H//.
      rewrite mulBC in Hmulmod; last rewrite ! size_sext H//.
      move : Hgt0 Hge; rewrite -Hmulmod => Hgt0.
      case Hmul : (((sext 1 bs1 *# sext 1 bs2)) == zeros (size ((sext 1 bs1 *# sext 1 bs2)))).
      rewrite (eqP Hmul) (eqP (negB_zeros _)) to_Zpos_zeros // in Hgt0.
      rewrite (neq_zeros_to_Zpos_negB (negbT Hmul)) size_mulB size_sext -(joinmsb_splitmsb Hszgt0') Hmsb /joinmsb to_Zpos_rcons.
      rewrite Z.mul_0_l Z.add_0_r.
      move : (to_Zpos_bounded (splitmsb (sext 1 bs1 *# sext 1 bs2)).1); rewrite size_splitmsb size_mulB size_sext addnK => Hs1bd.
      rewrite ->Z.le_sub_le_add_r; rewrite <-Z.le_sub_le_add_l => Hf.
      move : (Z.le_lt_trans _ _ _ Hf Hs1bd).
      rewrite Z.lt_sub_lt_add_l Nat2Z.inj_add Z.pow_add_r; [| lia | lia].
      rewrite -Zred_factor1 -Z.add_lt_mono_r.
      rewrite <-Z.pow_lt_mono_r_iff; [| lia | lia]. rewrite -Nat2Z.inj_lt => /ltP Hf'.
      by rewrite -subn_gt0 -subnDA addnC subnDA subnn // in Hf'.
    - rewrite -(to_Z_sext bs1 1) -(to_Z_sext bs2 1).
      rewrite high1_0_to_Z; last rewrite high1_msb msb_sext Hm1//.
      rewrite high1_0_to_Z; last rewrite high1_msb msb_sext Hm2//.
      move => [Hge Hlt].
      move : (Z.mod_small _ _ (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (sext 1 bs1)) (@to_Zpos_ge0 (sext 1 bs2))) (Z.lt_trans _ _ _ Hlt Haux))).
      rewrite -(size_sext) -to_Zpos_mulB' => Hmulmod ; move : Hlt.
      rewrite -Hmulmod -(joinmsb_splitmsb Hszgt0') Hmsb to_Zpos_rcons Z.mul_1_l size_splitmsb size_mulB size_sext addnK Z.lt_add_lt_sub_r => Hlt.
      have Haux' : (2 ^ Z.of_nat (size bs1 - 1) < 2 ^ Z.of_nat (size bs1))%Z.
      {
        apply Z.pow_lt_mono_r;
          [rewrite//|apply Nat2Z.is_nonneg|rewrite -Nat2Z.inj_lt//; apply/ltP; rewrite -(ltn_add2r 1) (subnK Hszgt0) addn1//].
      }
      rewrite <-Z.lt_sub_0 in Haux'. move : (Z.lt_trans _ _ _ Hlt Haux') => /Zlt_not_le Hlt'.
        by move : (@to_Zpos_ge0 (splitmsb (sext 1 bs1 *# sext 1 bs2)).1) => /Hlt' .
  Qed.

  Lemma andb_orb_all_cat_zeros : forall bs1 bs2,
    ~~ (andb_orb_all (bs1 ++ zeros (size bs2)) (bs2 ++ zeros (size bs1))).
  Proof.
    elim => [|bs1hd bs1tl IH]; elim => [|bs2hd bs2tl IHm]; first done.
    - rewrite cat0s cats0 andb_orb_all_0l//.
    - rewrite cats0 cat0s andb_orb_all_0r//.
    - rewrite /andb_orb_all rev_cat (eqP (rev_zeros _)) -(zeros_cons (size bs1tl)) 2!cat_cons.
      rewrite /extzip0 extzip_zip_ss; last rewrite /= !size_cat /= !size_zeros size_rev !addnS//.
      rewrite zip_cons andb_orb_all_zipb0 -(eqP (rev_zeros (size bs1tl))) -rev_cat -(extzip_zip_ss b0 b0);
        last rewrite size_rev !size_cat !size_zeros addnC//.
      rewrite -/extzip0 -/(andb_orb_all _ _ ) IH//.
  Qed.

  Lemma succB_rcons bs:
    ~~ (dropmsb bs == ones (size bs -1)) ->
    1 < size bs ->
    succB (sext 1 bs) = sext 1 (succB bs).
  Proof.
    intros.
    rewrite !sext_Sn !sext0 !cats1 (msb_succB_dropmsb_not1s H).
    apply to_Zpos_inj_ss; first rewrite size_succB !size_rcons size_succB//.
    rewrite -!addB1 !to_Zpos_rcons size_rcons size_addB size_from_nat minnn -!from_Zpos_from_nat_1//; try by apply ltnW.
    have Hsz : size (rcons bs (msb bs)) = size (from_Zpos (size bs).+1 1) by rewrite size_rcons size_from_Zpos.
    move : (to_Zpos_addB Hsz). rewrite size_rcons (carry_addB_eq_msbs Hsz) !msb_rcons.
    have Haux : from_Zpos (size bs).+1 1 = b1:: (zeros (size bs)).
    {
      apply/eqP; rewrite -to_nat_inj_ss; last rewrite size_from_Zpos /= size_zeros//.
      rewrite from_Zpos_from_nat_1// to_nat_from_nat to_nat_cons to_nat_zeros -muln2 mul0n addn0 modn_small// -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1))//.
    }
    rewrite Haux -{2 4 6}(ltn_predK H0) -zeros_rcons -rcons_cons !msb_rcons andbT !andbF !orbF.
    have -> : (rcons bs (msb bs) +# (b1 :: zeros (size bs))) = succB (rcons bs (msb bs)).
    {
      rewrite -Haux from_Zpos_from_nat_1// -(size_rcons bs (msb bs)) -addB1//.
    }
    have Haux2 : (dropmsb (rcons bs (msb bs)) == ones (size (rcons bs (msb bs)) - 1)) = false.
    {
      rewrite dropmsb_joinmsb -{1}(joinmsb_splitmsb (ltnW H0)) size_rcons -(ltn_predK (ltnW H0)) -ones_rcons eqseq_rcons -/(dropmsb _) -subn1 (negbTE H) andFb//.
    }
    rewrite (msb_succB_dropmsb_not1s (negbT Haux2)) msb_rcons andbN Z.mul_0_l Z.add_0_r => -> {Hsz Haux Haux2} .
    have Hsz : size bs = size (from_Zpos (size bs) 1) by rewrite size_from_Zpos.
    move : (to_Zpos_addB Hsz). rewrite carry_addB_eq_msbs; last rewrite size_from_Zpos//.
    rewrite from_Zpos_from_nat_1; try by apply ltnW. rewrite addB1 (msb_succB_dropmsb_not1s H).
    have Haux : from_nat (size bs) 1 = b1 :: (zeros (size bs -1)).
    {
      apply/eqP; rewrite -to_nat_inj_ss; last rewrite size_from_nat /=size_zeros subn1 (ltn_predK H0)//.
      rewrite to_nat_from_nat to_nat_cons to_nat_zeros -muln2 mul0n addn0 modn_small// -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1))(ltnW H0)//.
    }
    generalize H0; rewrite -subn_gt0 => Hgt.
    rewrite Haux -{1 2 3}(ltn_predK Hgt) -zeros_rcons -rcons_cons msb_rcons !andbF !andbT andFb !orbF andbN Z.mul_0_l Z.add_0_r => ->.
    rewrite to_Zpos_rcons Z.add_shuffle0 Z.add_cancel_r/= !to_Zpos_zeros !Z.mul_0_l//.
  Qed.

  Lemma sig_bits_cats_zeros :
    forall n bs,
    sig_bits (bs ++ zeros n) = sig_bits bs.
  Proof.
    elim => [|ns IH] bs; first by rewrite cats0.
    rewrite -zeros_rcons -rcons_cat sig_bits_rcons0 IH//.
  Qed.

  Lemma smulo_sext bs1 bs2 :
    ~~ Smulo (sext (size bs2) bs1) (sext (size bs1) bs2).
  Proof.
    rewrite /Smulo.
    rewrite -!/(msb _) !msb_sext !size_splitmsb !size_sext.
    case Hsz1 : (size bs1) => [|ns1]; case Hsz2 : (size bs2) => [|ns2].
    - rewrite (size0nil Hsz1) (size0nil Hsz2) //.
    - rewrite (size0nil Hsz1) !sext_nil !sext_Sn !sext0 !cats1 -!zeros_rcons splitmsb_rcons zeros_rcons msb_zeros.
      rewrite add0n addn0 subn1 !zeros_rcons mul0B msb_zeros Bool.xorb_false_l.
      have ->: [::] = zeros 0 by done.  have {1}-> : ns2 = size (zeros ns2) by rewrite size_zeros.
      rewrite -zeros_rcons splitmsb_rcons !msb_zeros orbF -/(zeros ns2) xor0B.
      move : Hsz2; case ns2.
      + move/splitmsb_size1 => ->.
        have ->: [::] = zeros (size (copy 0 (msb bs2))) by rewrite size_copy.
        rewrite xor0B /splitlsb//.
      + move => ns21 Hsz2. rewrite -zeros_cons splitlsb_joinlsb andb_orb_all_0l//.
    - rewrite (size0nil Hsz2) !sext_nil !sext_Sn !sext0 !cats1 -!zeros_rcons splitmsb_rcons zeros_rcons msb_zeros.
      rewrite add0n addn0 subn1 !zeros_rcons mulBC; last rewrite size_rcons size_zeros Hsz1//.
      rewrite mul0B msb_zeros Bool.xorb_false_l.
      have ->: [::] = zeros 0 by done.  have {2}-> : ns1 = size (zeros ns1) by rewrite size_zeros.
      rewrite -zeros_rcons splitmsb_rcons !msb_zeros orbF -/(zeros ns1) xorBC xor0B.
      move : Hsz1; case ns1.
      + move/splitmsb_size1 => ->.
        have ->: [::] = zeros (size (copy 0 (msb bs1))) by rewrite size_copy.
        rewrite xorBC xor0B /splitlsb//.
      + move => ns11 Hsz1. rewrite -zeros_cons splitlsb_joinlsb andb_orb_all_0r//.
    - rewrite 2!subn1 {1}sext_Sn {1}(sext_Sn ns1 bs2) !cats1 !splitmsb_rcons.
      rewrite xorBC.
      have ->: (ns1.+1 + ns2.+1).-1 = size (sext ns2 bs1) by rewrite addnS/= size_sext -Hsz1.
      have ->: (ns2.+1 + ns1.+1).-1 = size (sext ns1 bs2) by rewrite addnS/= size_sext -Hsz2.
      rewrite xorB_copy_case xorBC xorB_copy_case {1 2}/sext.
      have Hsz1' : 0 < size bs1 by rewrite Hsz1.
      have Hsz2' : 0 < size bs2 by rewrite Hsz2.
      case Hm1 : (msb bs1); case Hm2 : (msb bs2).
      +
        have Haoa: (~~(andb_orb_all (splitlsb (~~# (bs1 ++ copy ns2 true))).2 (splitlsb (~~# sext ns1 bs2)).2)).
        {
          rewrite -/(ones ns2) {1}/sext Hm2 -/(ones ns1) !invB_cat !invB_ones -!/(droplsb _) !droplsb_cat;
            try (rewrite size_invB Hsz1//||rewrite size_invB Hsz2//).
          have {1}->: ns2 = (size (droplsb (~~#bs2))) by rewrite size_droplsb size_invB subn1 Hsz2.
          have {1}->: ns1 = (size (droplsb (~~#bs1))) by rewrite size_droplsb size_invB subn1 Hsz1.
          rewrite (negbTE (andb_orb_all_cat_zeros _ _ ))//.
        }
        rewrite (negbTE Haoa) orFb.
        have Hszeq : size (sext 1 (sext ns2.+1 bs1)) = size (sext 1 (sext ns1.+1 bs2)).
        {
          rewrite !size_sext -Hsz2 -Hsz1 (addnC (size bs1) (size bs2))//.
        }
        rewrite -(mulB_negB_negB Hszeq).
        move : (signed_sig_bits_to_Z Hm1) => [Hltl1 _].
        move : (signed_sig_bits_to_Z Hm2) => [Hltl2 _].
        generalize Hm1; rewrite -> (msb1_to_Z_lt0 bs1); generalize Hm2; rewrite -> (msb1_to_Z_lt0 bs2) => Hlt02' Hlt01'.
        move : (Z.mul_le_mono_nonpos _ _ _ _ (Z.lt_le_incl _ _ Hlt01') Hltl1 (Z.lt_le_incl _ _ Hlt02') Hltl2).
        rewrite Z.mul_opp_l Z.mul_opp_r Z.opp_involutive -Z.pow_add_r; [| lia | lia].
        rewrite -Nat2Z.inj_add.
        have -> : (size bs1 - 1 + (size bs2 - 1))%coq_nat = (size bs1 - 1 + (size bs2 - 1)) by done.
        move => Hmulbd.
        have Haux : (2 ^ Z.of_nat (size bs1 - 1 + (size bs2 - 1)) < 2 ^ Z.of_nat (size (-#(sext 1 (sext ns2.+1 bs1)))))%Z.
        {
          apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith | ].
          rewrite -Nat2Z.inj_lt. apply/ltP.
          rewrite size_negB !size_sext !subn1 Hsz1 Hsz2/= addn1 addnS addSn -addn2.
          apply ltn_addr. done.
        }
        move : (Z.mod_small _ _ (conj (Z.lt_le_incl _ _ (Z.mul_neg_neg _ _ Hlt01' Hlt02')) (Z.le_lt_trans _ _ _ Hmulbd Haux))).
        have Hsxt1 : to_Z (sext 1 (sext ns2.+1 bs1)) = to_Z bs1 by rewrite !to_Z_sext.
        have Hsxt2 : to_Z (sext 1 (sext ns1.+1 bs2)) = to_Z bs2 by rewrite !to_Z_sext.
        rewrite -Hsxt2 -Hsxt1.
        rewrite -{1}(Z.opp_involutive (to_Z (sext 1 (sext ns2.+1 bs1)) * to_Z (sext 1 (sext ns1.+1 bs2)))).
        have Hh1 : msb (sext ns2.+1 bs1) = b1 by rewrite msb_sext Hm1//.
        have Hh2 : msb (sext ns1.+1 bs2) = b1 by rewrite msb_sext Hm2//.
        generalize Hh1; rewrite -(msb_sext 1); rewrite ->(msb1_to_Z_lt0 (sext 1 (sext ns2.+1 bs1))).
        generalize Hh2; rewrite -(msb_sext 1); rewrite ->(msb1_to_Z_lt0 (sext 1 (sext ns1.+1 bs2))) => Hlt02 Hlt01.
        rewrite -Z.mul_opp_l -Z.mul_opp_r -(Z.abs_neq _ (Z.lt_le_incl _ _ Hlt01)).
        rewrite -(Z.abs_neq _ (Z.lt_le_incl _ _ Hlt02)).
        rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb !msb_sext Hm1//.
        rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb !msb_sext Hm2//.
        rewrite -to_Zpos_mulB' !to_Z_sext.
        have Hszgt : 0 < size (-# sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2)).
        {
          rewrite size_mulB size_negB !size_sext addn1//.
        }
        have Hszgt' : 0 < size (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).1.
        {
          rewrite size_splitmsb size_mulB size_negB !size_sext addnK addnS//.
        }
        rewrite -{1}(joinmsb_splitmsb Hszgt) -{1}(joinmsb_splitmsb Hszgt') 2!to_Zpos_rcons.
        rewrite !size_splitmsb size_joinmsb !size_splitmsb !size_mulB !size_negB !size_sext addnK addnS subn1 /msb.
        move => Heq; move : Hmulbd; rewrite -Heq.
        case Hmsb : (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).2;
          case Hmmsb : (splitmsb (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).1).2; try done;
            rewrite Z.mul_1_l Z.mul_0_l Z.add_0_r;
            rewrite Hsz2 !subn1 Z.le_add_le_sub_r => Hmulbd {Haux}.
        have Haux : (2 ^ Z.of_nat ((size bs1).-1 + ns2.+1.-1) < 2 ^ Z.of_nat ((size bs1 + ns2).+1.-1 + 1))%Z.
        {
          apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
          rewrite -Nat2Z.inj_lt Hsz1/= addSn. apply/ltP.
          by apply ltn_addr.
        }
        rewrite <-Z.lt_sub_0 in Haux.
        move : (Z.le_lt_trans _ _ _ Hmulbd Haux) => /Zlt_not_le Hf.
        by move : (@to_Zpos_ge0 (splitmsb (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).1).1) => Ht.
        have Haux : (2 ^ Z.of_nat ((size bs1).-1 + ns2.+1.-1) < 2 ^ Z.of_nat ((size bs1 + ns2).+1.-1))%Z.
        {
          apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
          rewrite -Nat2Z.inj_lt Hsz1/= addSn. by apply/ltP.
        }
        rewrite <-Z.lt_sub_0 in Haux.
        move : (Z.le_lt_trans _ _ _ Hmulbd Haux) => /Zlt_not_le Hf.
        by move : (@to_Zpos_ge0 (splitmsb (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).1).1) => Ht.
      +
        have Haoa: (~~(andb_orb_all (splitlsb (~~# (bs1 ++ copy ns2 true))).2 (splitlsb (sext ns1 bs2)).2)).
        {
          rewrite -/(ones ns2) {1}/sext Hm2 -/(ones ns1) !invB_cat !invB_ones -!/(droplsb _) !droplsb_cat;
          try (rewrite Hsz2//||rewrite size_invB Hsz1//).
          have {1}->: ns2 = (size (droplsb (bs2))) by rewrite size_droplsb subn1 Hsz2.
          have {1}->: ns1 = (size (droplsb (~~#bs1))) by rewrite size_droplsb size_invB subn1 Hsz1.
          rewrite (negbTE (andb_orb_all_cat_zeros _ _ ))//.
        }
        rewrite (negbTE Haoa) orFb.
        have Hszeq : size (sext 1 (sext ns2.+1 bs1)) = size (sext 1 (sext ns1.+1 bs2)).
        {
          rewrite !size_sext -Hsz2 -Hsz1 (addnC (size bs1) (size bs2))//.
        }
        rewrite -(mulB_negB_negB Hszeq) mulBC; last rewrite !size_negB//.
        rewrite mulB_negB; last rewrite size_negB//.
        rewrite mulBC; last rewrite size_negB//.
        move : (signed_sig_bits_to_Z Hm1) => [Hltl1 Hltr1].
        move : (conj Hltl1 (Z.lt_le_incl _ _ (Z.lt_trans _ _ _ Hltr1 (pow2_nat2z_gt0 (size bs1 - 1))))).
        rewrite <-Z.abs_le => Habs1.
        have Hzzpos2 : to_Z bs2 = to_Zpos bs2
          by rewrite high1_0_to_Z//; last rewrite high1_msb Hm2//.
        move : (@to_Zpos_ge0 bs2); rewrite -Hzzpos2 => Hge02'.
        generalize Hm1; rewrite -> (msb1_to_Z_lt0 bs1) => Hlt01'.
        generalize Hlt01'; rewrite -Z.opp_pos_neg => Hgt01'.
        move : (Z.mul_nonneg_nonneg _ _ (Z.lt_le_incl _ _ Hgt01') Hge02').
        move : (to_Zpos_bounded bs2); rewrite - Hzzpos2.
        rewrite -(Z.abs_neq _ (Z.lt_le_incl _ _ Hlt01')) -(Z.abs_eq _ Hge02') => Habs2.
        move : (Z.mul_le_mono_nonneg _ _ _ _ (Z.abs_nonneg _) Habs1 (Z.abs_nonneg _) (Z.lt_le_incl _ _ Habs2)).
        rewrite -Z.pow_add_r; [| by auto with zarith | by auto with zarith]. rewrite -Nat2Z.inj_add.
        have -> : (size bs1 - 1 + size bs2)%coq_nat = (size bs1 - 1 + size bs2) by done.
        move => /Zle_lt_or_eq [Hmulle1|Hmulle2] Hmulge.
        have Haux : (2 ^ Z.of_nat (size bs1 - 1 + size bs2) < 2 ^ Z.of_nat (size (-#(sext 1 (sext ns2.+1 bs1)))))%Z.
        {
          apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
          rewrite -Nat2Z.inj_lt. apply/ltP.
          rewrite size_negB !size_sext !subn1 Hsz1 Hsz2/= addSn addn1//.
        }
        move : (Z.mod_small _ _ (conj Hmulge (Z.lt_trans _ _ _ Hmulle1 Haux))) => {Haux}.
        have Hsxt1 : to_Z (sext 1 (sext ns2.+1 bs1)) = to_Z bs1 by rewrite !to_Z_sext.
        have Hsxt2 : to_Z (sext 1 (sext ns1.+1 bs2)) = to_Z bs2 by rewrite !to_Z_sext.
        rewrite -{1}Hsxt2 -{1}Hsxt1 -high1_1_to_Zpos_negB; last rewrite high1_msb !msb_sext Hm1//.
        rewrite high1_0_to_Z; last rewrite high1_msb !msb_sext Hm2//.
        rewrite Z.abs_eq; last apply to_Zpos_ge0.
        rewrite -to_Zpos_mulB' => Heq. generalize Hmulle1; rewrite -Heq.
        have Hsz : (0 < size (-# sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).
        {
          rewrite size_mulB size_negB !size_sext addn1//.
        }
        have Hsz' : (0 < size (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).1).
        {
          rewrite size_splitmsb size_mulB size_negB !size_sext addn1 subn1/= addnS//.
        }
        case Hd0 : (dropmsb (-# sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2)) == zeros (size (-# sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2)) - 1)).
        * rewrite -msb_negB_dropmsb_0// -/(dropmsb _) dropmsb_negB (eqP Hd0) (eqP (negB_zeros _)) msb_zeros.
          rewrite Bool.xorb_false_r.
          rewrite -{1}(joinmsb_splitmsb Hsz) /msb.
          case Hmsb : (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).2; try done.
          rewrite to_Zpos_rcons Z.mul_1_l size_splitmsb size_mulB size_negB !size_sext addnK Z.lt_add_lt_sub_r => Hf.
          have Haux : (2 ^ Z.of_nat (size bs1 - 1 + size bs2) < 2 ^ Z.of_nat (size bs1 + ns2.+1))%Z.
          {
            apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
            rewrite -Nat2Z.inj_lt. apply/ltP. by rewrite Hsz1 Hsz2 subn1//.
          }
          rewrite <-Z.lt_sub_0 in Haux.
          move : (Z.lt_trans _ _ _ Hf Haux) => {Hf}/Zlt_not_le Hf.
            by move : (@to_Zpos_ge0 (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).1).
        * rewrite -(msb_negB (negbT Hd0)) -{1}(joinmsb_splitmsb Hsz) -{1}(joinmsb_splitmsb Hsz')/msb.
          case Hmsb : (splitmsb (-# sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).2;
            case Hmmsb : (splitmsb (splitmsb (-#(-# sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2)))).1).2;
            try done.
          rewrite !to_Zpos_rcons Z.mul_1_l !size_joinmsb !size_splitmsb size_mulB size_negB !size_sext !addnK.
          rewrite -Hsz2 Z.lt_add_lt_sub_r => Hmulbd.
          have Haux : (2 ^ Z.of_nat (size bs1 - 1 + size bs2) < 2 ^ Z.of_nat (size bs1 + size bs2 - 1 + 1))%Z.
          {
            apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
            rewrite -Nat2Z.inj_lt Hsz1 addSn !subn1/= addn1. apply/ltP.
            by apply ltnSn.
          }
          rewrite <-Z.lt_sub_0 in Haux.
          move : (Z.lt_trans _ _ _ Hmulbd Haux) => /Zlt_not_le.
          case Hmmsb': (splitmsb (splitmsb (-# sext 1 (sext (size bs2) bs1) *# sext 1 (sext ns1.+1 bs2))).1).2.
          rewrite Z.mul_1_l.
          move => Hf.
            by move : (Z.add_nonneg_nonneg _ _ (@to_Zpos_ge0 (splitmsb
                                                                (splitmsb (-# sext 1 (sext (size bs2) bs1) *# sext 1 (sext ns1.+1 bs2))).1).1)  (Z.lt_le_incl _ _ (pow2_nat2z_gt0 (size bs1 + size bs2 - 1)))).
            rewrite Z.mul_0_l Z.add_0_r.
            move => Hf.
              by move : (@to_Zpos_ge0 ((splitmsb (splitmsb (-# sext 1 (sext (size bs2) bs1) *# sext 1 (sext ns1.+1 bs2))).1).1)).
        * rewrite to_Zpos_rcons Z.mul_0_l Z.add_0_r.
          move : Hmmsb Hmsb Hd0.
          rewrite -mulB_negB; [rewrite negB_involutive|rewrite size_negB !size_sext -Hsz1 -Hsz2; ring].
          move => Hmmsb.
          rewrite to_Zpos_rcons mulB_negB; [|rewrite !size_sext -Hsz1 -Hsz2; ring].
          rewrite -!/(dropmsb _) -!/(msb _) => Hmsb Hd0.
          move : (dropmsb_negB_nonzeros (negbT Hd0)).
          rewrite negB_involutive size_negB => Hd0'.
          rewrite dropmsb_negB -msb_negB;
            [|move : (zeros_msb_dropmsb (dropmsb (sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2)))); rewrite size_dropmsb (negbTE Hd0') /msb Hmmsb andTb => Haux; rewrite -Haux//].
          rewrite /msb /dropmsb Hmmsb Z.mul_1_l.
          rewrite size_splitmsb size_negB size_splitmsb size_mulB !size_sext addnK Hsz1 !subn1 addSn.
          rewrite Z.lt_add_lt_sub_r (lock splitmsb)/=-Hsz2 Z.sub_diag -lock.
          by move : (@to_Zpos_ge0 (splitmsb (-# (splitmsb (sext 1 (sext (size bs2) bs1) *# sext 1 (sext ns1.+1 bs2))).1)).1) => /Zle_not_lt.
        * move : Hmulle2.
          rewrite -(to_Z_sext bs1 (size bs2))  -(to_Z_sext bs2 (size bs1)).
          rewrite -(to_Z_sext (sext (size bs2) bs1) 1) -(to_Z_sext (sext (size bs1) bs2) 1).
          rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb !msb_sext Hm1//.
          rewrite Z.abs_eq; last rewrite !to_Z_sext//.
          rewrite high1_0_to_Z; last rewrite high1_msb !msb_sext Hm2//.
          have Haux : (2 ^ Z.of_nat (size bs1 - 1 + size bs2) < 2 ^ Z.of_nat (size (-# sext 1 (sext (size bs2) bs1))))%Z.
          {
            apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
            rewrite -Nat2Z.inj_lt. apply/ltP. rewrite size_negB !size_sext Hsz1 subn1/= addSn.
            by rewrite addn1 ltnW //.
          }
          move => Hmulbd. rewrite -Hmulbd in Haux.
          move : (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (-# sext 1 (sext (size bs2) bs1))) (@to_Zpos_ge0 (sext 1 (sext (size bs1) bs2)))) Haux) => Hsm.
          move : (Z.mod_small _ _ Hsm). rewrite -to_Zpos_mulB' Hmulbd => Hmul{Haux}.
          have Haux : (-# sext 1 (sext (size bs2) bs1) *# sext 1 (sext (size bs1) bs2)) =
                      rcons (rcons (zeros (size bs1 -1 + size bs2)) b1) b0.
          {
            apply to_Zpos_inj_ss; first rewrite size_mulB size_negB !size_sext !size_rcons size_zeros addn1 subn1 Hsz1 Hsz2//.
            rewrite !to_Zpos_rcons Z.mul_0_l Z.mul_1_l Z.add_0_r to_Zpos_zeros Z.add_0_l size_zeros//.
          }
          rewrite -Hsz1 -Hsz2 Haux -msb_negB;
            [|rewrite dropmsb_joinmsb !size_rcons size_zeros !subn1 -zeros_rcons eqseq_rcons andbF//].
          rewrite msb_rcons -/(dropmsb _) dropmsb_negB dropmsb_joinmsb -msb_negB_dropmsb_0;
            [rewrite msb_rcons//|rewrite dropmsb_joinmsb size_rcons size_zeros !subn1//].
      + have Haoa: (~~(andb_orb_all (splitlsb ((bs1 ++ copy ns2 false))).2 (splitlsb (~~#sext ns1 bs2)).2)).
        {
          rewrite -/(zeros ns2) {1}/sext Hm2 -/(ones ns1) !invB_cat !invB_ones -!/(droplsb _) !droplsb_cat;
          try (rewrite size_invB Hsz2//||rewrite Hsz1//).
          have {1}->: ns2 = (size (droplsb (~~#bs2))) by rewrite size_droplsb size_invB subn1 Hsz2.
          have {1}->: ns1 = (size (droplsb (bs1))) by rewrite size_droplsb subn1 Hsz1.
          rewrite (negbTE (andb_orb_all_cat_zeros _ _ ))//.
        }
        rewrite (negbTE Haoa) orFb.
        have Hszeq : size (sext 1 (sext ns2.+1 bs1)) = size (sext 1 (sext ns1.+1 bs2)).
        {
          rewrite !size_sext -Hsz2 -Hsz1 (addnC (size bs1) (size bs2))//.
        }
        rewrite -(mulB_negB_negB Hszeq).
        rewrite mulB_negB; last rewrite size_negB//.
        move : (signed_sig_bits_to_Z Hm2) => [Hltl1 Hltr1].
        move : (conj Hltl1 (Z.lt_le_incl _ _ (Z.lt_trans _ _ _ Hltr1 (pow2_nat2z_gt0 (size bs2 - 1))))).
        rewrite <-Z.abs_le => Habs2.
        have Hzzpos1 : to_Z bs1 = to_Zpos bs1
          by rewrite high1_0_to_Z//; last rewrite high1_msb Hm1//.
        move : (@to_Zpos_ge0 bs1); rewrite -Hzzpos1 => Hge01'.
        generalize Hm2; rewrite -> (msb1_to_Z_lt0 bs2) => Hlt02'.
        generalize Hlt02'; rewrite -Z.opp_pos_neg => Hgt02'.
        move : (Z.mul_nonneg_nonneg _ _ Hge01' (Z.lt_le_incl _ _ Hgt02') ).
        move : (to_Zpos_bounded bs1); rewrite - Hzzpos1.
        rewrite -(Z.abs_neq _ (Z.lt_le_incl _ _ Hlt02')) -(Z.abs_eq _ Hge01') => Habs1.
        move : (Z.mul_le_mono_nonneg _ _ _ _ (Z.abs_nonneg _) (Z.lt_le_incl _ _ Habs1) (Z.abs_nonneg _) Habs2).
        rewrite -Z.pow_add_r; [| by auto with zarith | by auto with zarith]. rewrite -Nat2Z.inj_add.
        have -> : (size bs1 + (size bs2 - 1))%coq_nat = (size bs1 + (size bs2 - 1)) by done.
        move => /Zle_lt_or_eq [Hmulle1|Hmulle2] Hmulge.
        have Haux : (2 ^ Z.of_nat (size bs1 + (size bs2 - 1)) < 2 ^ Z.of_nat (size ((sext 1 (sext ns2.+1 bs1)))))%Z.
        {
          apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
          rewrite -Nat2Z.inj_lt. apply/ltP.
          by rewrite !size_sext !subn1 Hsz1 Hsz2/= addSn addn1 addnS//.
        }
        move : (Z.mod_small _ _ (conj Hmulge (Z.lt_trans _ _ _ Hmulle1 Haux))) => {Haux}.
        have Hsxt1 : to_Z (sext 1 (sext ns2.+1 bs1)) = to_Z bs1 by rewrite !to_Z_sext.
        have Hsxt2 : to_Z (sext 1 (sext ns1.+1 bs2)) = to_Z bs2 by rewrite !to_Z_sext.
        rewrite -{1}Hsxt2 -{1}Hsxt1 Z.abs_eq; last rewrite !to_Z_sext//.
        rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb !msb_sext Hm2//.
        rewrite high1_0_to_Z; last rewrite high1_msb !msb_sext Hm1//.
        rewrite -to_Zpos_mulB' => Heq. generalize Hmulle1; rewrite -Heq.
        have Hsz : (0 < size (sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).
        {
          rewrite size_mulB !size_sext addn1//.
        }
        have Hsz' : (0 < size (splitmsb (sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).1).
        {
          rewrite size_splitmsb size_mulB !size_sext addn1 subn1/= addnS//.
        }
        case Hd0 : (dropmsb (sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2)) == zeros (size (sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2)) - 1)).
        * rewrite -msb_negB_dropmsb_0// -/(dropmsb _) dropmsb_negB (eqP Hd0) (eqP (negB_zeros _)) msb_zeros.
          rewrite Bool.xorb_false_r.
          rewrite -{1}(joinmsb_splitmsb Hsz) /msb.
          case Hmsb : (splitmsb (sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).2; try done.
          rewrite to_Zpos_rcons Z.mul_1_l size_splitmsb size_mulB !size_sext addnK Z.lt_add_lt_sub_r => Hf.
          have Haux : (2 ^ Z.of_nat (size bs1 + (size bs2 - 1)) < 2 ^ Z.of_nat (size bs1 + ns2.+1))%Z.
          {
            apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
            rewrite -Nat2Z.inj_lt. apply/ltP. by rewrite Hsz1 Hsz2 subn1/= addnS//.
          }
          rewrite <-Z.lt_sub_0 in Haux.
          move : (Z.lt_trans _ _ _ Hf Haux) => {Hf}/Zlt_not_le Hf.
            by move : (@to_Zpos_ge0 (splitmsb (sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2))).1).
        * rewrite -(msb_negB (negbT Hd0)) -{1}(joinmsb_splitmsb Hsz) -{1}(joinmsb_splitmsb Hsz')/msb.
          case Hmsb : (splitmsb ( sext 1 (sext ns2.+1 bs1) *# -#sext 1 (sext ns1.+1 bs2))).2;
            case Hmmsb : (splitmsb (splitmsb (-#(sext 1 (sext ns2.+1 bs1) *# -# sext 1 (sext ns1.+1 bs2)))).1).2;
            try done.
          rewrite !to_Zpos_rcons Z.mul_1_l !size_joinmsb !size_splitmsb size_mulB !size_sext !addnK.
          rewrite -Hsz2 Z.lt_add_lt_sub_r => Hmulbd.
          have Haux : (2 ^ Z.of_nat (size bs1 + (size bs2 - 1)) < 2 ^ Z.of_nat (size bs1 + size bs2 - 1 + 1))%Z.
          {
            apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
            rewrite -Nat2Z.inj_lt Hsz1 Hsz2 !subn1 addn1 addnS. apply/ltP.
            by apply ltnSn.
          }
          rewrite <-Z.lt_sub_0 in Haux.
          move : (Z.lt_trans _ _ _ Hmulbd Haux) => /Zlt_not_le.
          case Hmmsb': (splitmsb (splitmsb (sext 1 (sext (size bs2) bs1) *# -# sext 1 (sext ns1.+1 bs2))).1).2.
          rewrite Z.mul_1_l.
          move => Hf.
            by move : (Z.add_nonneg_nonneg _ _ (@to_Zpos_ge0 (splitmsb
                                                                (splitmsb (sext 1 (sext (size bs2) bs1) *# -# sext 1 (sext ns1.+1 bs2))).1).1)  (Z.lt_le_incl _ _ (pow2_nat2z_gt0 (size bs1 + size bs2 - 1)))).
            rewrite Z.mul_0_l Z.add_0_r.
            move => Hf.
              by move : (@to_Zpos_ge0 ((splitmsb (splitmsb (sext 1 (sext (size bs2) bs1) *# -#sext 1 (sext ns1.+1 bs2))).1).1)).
        * rewrite to_Zpos_rcons Z.mul_0_l Z.add_0_r.
          move : Hmmsb Hmsb Hd0.
          rewrite -mulB_negB; [|rewrite size_negB !size_sext -Hsz1 -Hsz2; ring].
          rewrite (mulB_negB_negB Hszeq).
          move => Hmmsb.
          rewrite to_Zpos_rcons mulBC; last rewrite size_negB //.
          rewrite mulB_negB; [rewrite mulBC//|rewrite !size_sext -Hsz1 -Hsz2; ring].
          rewrite -!/(dropmsb _) -!/(msb _) => Hmsb Hd0.
          move : (dropmsb_negB_nonzeros (negbT Hd0)).
          rewrite negB_involutive size_negB => Hd0'.
          rewrite dropmsb_negB -msb_negB;
            [|move : (zeros_msb_dropmsb (dropmsb (sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2)))); rewrite size_dropmsb (negbTE Hd0') /msb Hmmsb andTb => Haux; rewrite -Haux//].
          rewrite /msb /dropmsb Hmmsb Z.mul_1_l.
          rewrite size_splitmsb size_negB size_splitmsb size_mulB !size_sext addnK Hsz1 Hsz2 !subn1 addnS.
          rewrite Z.lt_add_lt_sub_r (lock splitmsb) (lock Z.of_nat)/=-Hsz2 Z.sub_diag -lock.
          by move : (@to_Zpos_ge0 (splitmsb (-# (splitmsb (sext 1 (sext (size bs2) bs1) *# sext 1 (sext ns1.+1 bs2))).1)).1) => /Zle_not_lt.
        * move : Hmulle2.
          rewrite -(to_Z_sext bs1 (size bs2))  -(to_Z_sext bs2 (size bs1)).
          rewrite -(to_Z_sext (sext (size bs2) bs1) 1) -(to_Z_sext (sext (size bs1) bs2) 1).
          rewrite Z.abs_eq; last rewrite !to_Z_sext//.
          rewrite high1_0_to_Z; last rewrite high1_msb !msb_sext Hm1//.
          rewrite -high1_1_to_Zpos_negB; last rewrite high1_msb !msb_sext Hm2//.
          have Haux : (2 ^ Z.of_nat (size bs1 + (size bs2 - 1)) < 2 ^ Z.of_nat (size (sext 1 (sext (size bs2) bs1))))%Z.
          {
            apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
            rewrite -Nat2Z.inj_lt. apply/ltP.
            by rewrite !size_sext Hsz1 Hsz2 subn1 addn1 addnS ltnW//.
          }
          move => Hmulbd. rewrite -Hmulbd in Haux.
          move : (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 (sext 1 (sext (size bs2) bs1))) (@to_Zpos_ge0 (-#sext 1 (sext (size bs1) bs2)))) Haux) => Hsm.
          move : (Z.mod_small _ _ Hsm). rewrite -to_Zpos_mulB' Hmulbd => Hmul{Haux}.
          have Haux : (sext 1 (sext (size bs2) bs1) *# -#sext 1 (sext (size bs1) bs2)) =
                      rcons (rcons (zeros (size bs1 + (size bs2 - 1))) b1) b0.
          {
            apply to_Zpos_inj_ss; first rewrite size_mulB !size_sext !size_rcons size_zeros addn1 subn1 Hsz1 Hsz2 -3!addnS//.
            rewrite !to_Zpos_rcons Z.mul_0_l Z.mul_1_l Z.add_0_r to_Zpos_zeros Z.add_0_l size_zeros//.
          }
          rewrite -Hsz1 -Hsz2 Haux -msb_negB;
            [|rewrite dropmsb_joinmsb !size_rcons size_zeros !subn1 -zeros_rcons eqseq_rcons andbF//].
          rewrite msb_rcons -/(dropmsb _) dropmsb_negB dropmsb_joinmsb -msb_negB_dropmsb_0;
            [rewrite msb_rcons//|rewrite dropmsb_joinmsb size_rcons size_zeros !subn1//].
      + have Haoa: (~~(andb_orb_all (splitlsb ((bs1 ++ copy ns2 false))).2 (splitlsb (sext ns1 bs2)).2)).
        {
          rewrite -/(zeros ns2) {1}/sext Hm2 -!/(droplsb _) !droplsb_cat;
            try (rewrite Hsz1//||rewrite Hsz2//).
          have {1}->: ns2 = (size (droplsb bs2)) by rewrite size_droplsb subn1 Hsz2.
          have {1}->: ns1 = (size (droplsb bs1)) by rewrite size_droplsb subn1 Hsz1.
          rewrite (negbTE (andb_orb_all_cat_zeros _ _ ))//.
        }
        rewrite (negbTE Haoa) orFb.
        have Hszeq : size (sext 1 (sext ns2.+1 bs1)) = size (sext 1 (sext ns1.+1 bs2)).
        {
          rewrite !size_sext -Hsz2 -Hsz1 (addnC (size bs1) (size bs2))//.
        }
        have Hzzpos1 : to_Z bs1 = to_Zpos bs1
          by rewrite high1_0_to_Z//; last rewrite high1_msb Hm1//.
        have Hzzpos2 : to_Z bs2 = to_Zpos bs2
          by rewrite high1_0_to_Z//; last rewrite high1_msb Hm2//.
        move : (@to_Zpos_bounded bs2); move : (@to_Zpos_bounded bs1) => Hlt01 Hlt02.
        move : (Z.mul_lt_mono_nonneg _ _ _ _ (@to_Zpos_ge0 bs1) (Hlt01) (@to_Zpos_ge0 bs2) (Hlt02)).
        rewrite -Z.pow_add_r; [| by auto with zarith | by auto with zarith ].
        rewrite -Nat2Z.inj_add.
        have -> : (size bs1 + (size bs2))%coq_nat = (size bs1 + (size bs2)) by done.
        move => Hmulbd.
        have Haux : (2 ^ Z.of_nat (size bs1 + (size bs2)) < 2 ^ Z.of_nat (size ((sext 1 (sext ns2.+1 bs1)))))%Z.
        {
          apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
          rewrite -Nat2Z.inj_lt. apply/ltP.
          by rewrite !size_sext -Hsz2 addn1//.
        }
        move : (Z.mod_small _ _ (conj (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2)) (Z.lt_trans _ _ _ Hmulbd Haux))).
        have Hsxt1 : to_Z (sext 1 (sext ns2.+1 bs1)) = to_Z bs1 by rewrite !to_Z_sext.
        have Hsxt2 : to_Z (sext 1 (sext ns1.+1 bs2)) = to_Z bs2 by rewrite !to_Z_sext.
        rewrite -Hzzpos2 -Hzzpos1 -{1}Hsxt2 -{1}Hsxt1.
        rewrite high1_0_to_Z; last rewrite high1_msb !msb_sext Hm1//.
        rewrite high1_0_to_Z; last rewrite high1_msb !msb_sext Hm2//.
        rewrite -to_Zpos_mulB'.
        have Hszgt : 0 < size (sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2)).
        {
          rewrite size_mulB !size_sext addn1//.
        }
        have Hszgt' : 0 < size (splitmsb (sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).1.
        {
          rewrite size_splitmsb size_mulB !size_sext addnK addnS//.
        }
        rewrite -{1}(joinmsb_splitmsb Hszgt) -{1}(joinmsb_splitmsb Hszgt') 2!to_Zpos_rcons.
        rewrite !size_splitmsb size_joinmsb !size_splitmsb !size_mulB !size_sext addnK addnS subn1 /msb.
        rewrite Hzzpos1 Hzzpos2 => Heq; move : Hmulbd; rewrite -Heq.
        case Hmsb : (splitmsb (sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).2;
          case Hmmsb : (splitmsb (splitmsb (sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).1).2; try done;
            rewrite Z.mul_1_l Z.mul_0_l Z.add_0_r -Hsz1 -Hsz2 Z.lt_add_lt_sub_r => Hmulbd {Haux}.
        have Haux : (2 ^ Z.of_nat (size bs1 + size bs2) = 2 ^ Z.of_nat ((size bs1 + ns2).+1.-1 + 1))%Z.
        {
          rewrite Hsz1 Hsz2 addn1 addnS//.
        }
        rewrite Haux Z.sub_diag in Hmulbd. move/Zlt_not_le : Hmulbd.
          by move : (@to_Zpos_ge0 (splitmsb (splitmsb (sext 1 (sext (size bs2) bs1) *# sext 1 (sext (size bs1) bs2))).1).1) => Ht.
          have Haux1 : (to_Zpos bs1 < 2 ^ Z.of_nat (size bs1 - 1))%Z.
          {
            rewrite -{1}(joinmsb_splitmsb Hsz1') -/(msb _ ) Hm1 to_Zpos_rcons Z.mul_0_l Z.add_0_r.
            move : (to_Zpos_bounded (splitmsb bs1).1). rewrite size_splitmsb//.
          }
          have Haux2 : (to_Zpos bs2 < 2 ^ Z.of_nat (size bs2 - 1))%Z.
          {
            rewrite -{1}(joinmsb_splitmsb Hsz2') -/(msb _ ) Hm2 to_Zpos_rcons Z.mul_0_l Z.add_0_r.
            move : (to_Zpos_bounded (splitmsb bs2).1). rewrite size_splitmsb//.
          }
          move : (Z.mul_lt_mono_nonneg _ _ _ _ (@to_Zpos_ge0 bs1) Haux1 (@to_Zpos_ge0 bs2) Haux2).
          rewrite -Z.pow_add_r; [| by auto with zarith | by auto with zarith ].
          rewrite -Nat2Z.inj_add.
          have -> : (size bs1 - 1 + (size bs2 - 1))%coq_nat = (size bs1 -1 + (size bs2 -1)) by done.
          rewrite -Heq Hmsb Hmmsb Z.mul_0_l Z.add_0_r Z.mul_1_l.
          have Haux : (2 ^ Z.of_nat (size bs1 - 1 + (size bs2 - 1))< 2 ^ Z.of_nat (size bs1 + ns2).+1.-1 )%Z.
          {
            rewrite Hsz1 Hsz2 !subn1 . apply Z.pow_lt_mono_r; [ by auto with zarith | by auto with zarith |].
            rewrite -Nat2Z.inj_lt. apply/ltP. by rewrite addSn //.
          }
          rewrite <-Z.lt_sub_0 in Haux.
          rewrite Z.lt_add_lt_sub_r => Hmulb.
          move : (Z.lt_trans _ _ _ Hmulb Haux) => /Zlt_not_le.
          move : (@to_Zpos_ge0 (splitmsb (splitmsb (sext 1 (sext ns2.+1 bs1) *# sext 1 (sext ns1.+1 bs2))).1).1). done.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of unsigned division
    ---------------------------------------------------------------------------*)

  (* Definition of unsigned division *)

  Fixpoint udivB_rec (n m : bits) (q r : bits): bits * bits :=
    match n with
    | [::] => (q, r)
    | nhd :: ntl => let di := dropmsb (joinlsb nhd r) in
                    let bi := leB m di in
                    let ri := if bi then subB di m else di in
                    let qi := dropmsb (joinlsb bi q) in
                    udivB_rec ntl m qi ri
    end.

  Definition udivB (n' m : bits) : bits * bits :=
    let n := rev n' in
    if ((from_Zpos (size n) (to_Zpos m)) == zeros (size n)) then (ones (size n), n')
    else udivB_rec n (from_Zpos (size n) (to_Zpos m)) (zeros (size n)) (zeros (size n)).

  Definition udivB' (n m : bits) : bits := (udivB n m).1.

  (* size *)

  Lemma size_udivB_rec (m n q r : bits) : size (udivB_rec m n q r).1 = size q.
  Proof.
    move : n q r. elim m => [|mhd mtl IH] n q r; first done.
    rewrite /=.
    case H : (n <=# dropmsb (joinlsb mhd r));
      rewrite (IH n _ _ ) size_dropmsb size_joinlsb addnK//.
  Qed.

  Lemma size_udivB m n : size (udivB m n).1 = size m.
  Proof.
    rewrite/udivB. intros.
    case Hm0: (from_Zpos (size (rev m)) (to_Zpos n) == zeros (size (rev m)));
                first by rewrite size_rev size_ones.
    by rewrite size_rev size_udivB_rec size_zeros.
  Qed.

  Lemma udivB0 : forall n m, (udivB m (zeros n)) = (ones (size m), m).
  Proof.
    intros; rewrite/udivB.  rewrite to_Zpos_zeros zeros_from_Zpos size_rev eq_refl//.
  Qed.

  Lemma udivB_rec0 : forall n (m : bits) q ,
      ~~(m==zeros(size m)) -> udivB_rec (zeros n.+1) m q (zeros (size m))= (shlB n.+1 q, (zeros (size m))).
  Proof.
    intros. rewrite /=.
    have H0 : (m <=# dropmsb (joinlsb b0 (zeros (size m))) = false).
    {
      rewrite /leB /joinlsb zeros_cons -zeros_rcons -/joinmsb dropmsb_joinmsb (negbTE H) ltB_zeros_r ltBn0//.
    }
    rewrite H0 {2}/joinlsb zeros_cons -zeros_rcons -/joinmsb dropmsb_joinmsb.
    move : q. elim n; first done.
    rewrite /= H0 => n0 IH q. rewrite {3}/joinlsb zeros_cons -zeros_rcons -/joinmsb dropmsb_joinmsb.
    rewrite (IH (dropmsb (joinlsb false q))) -shlB1_shlB//.
  Qed.

  Lemma udiv0B : forall n (m: bits),
      n = size m ->
      ~~(m==zeros(size m)) ->
      udivB (zeros n) m = (zeros n, zeros n).
  Proof.
    move => n m Hsz Hneq0m. rewrite/udivB size_rev size_zeros Hsz from_Zpos_to_Zpos (negbTE Hneq0m) rev_copy -/(zeros _).
    move : (neq_zero_size_gt0 Hneq0m) => Hgt0.
    rewrite -{1}(ltn_predK Hgt0) udivB_rec0// (ltn_predK Hgt0) shlB_zeros//.
  Qed.

  Lemma udivB1_rec : forall m n q,
      ~~(m == zeros (size m)) -> 0 < n -> size m <= n -> n = size q ->
      udivB_rec m (b1 :: zeros (n).-1) q (zeros n) = ((high (size m) (rev m)) ++ (low (size q - size m) q),  (shlB (size m) (zeros n))).
  Proof.
    elim => [|mhd mtl IH] n q Hn0 Hgt0n Hsznm Hsznq. rewrite subn0 low_size/= high0 cat0s//.
    move : (neq_zero_size_gt0 Hn0) => Hgt0.
    generalize Hgt0n; rewrite -(size_zeros n) => Hgt0nz.
    rewrite /=.
    case Hmtl : (mtl == (zeros (size mtl))).
    - move : Hn0; rewrite /= eqseq_cons Hmtl andbT.
      case Hmhd: mhd; rewrite // => _.
      rewrite size_zeros (dropmsb_joinlsb true Hgt0nz) {2}/joinlsb dropmsb_zeros /leB eq_refl orTb subB_same/= zeros_cons size_zeros (ltn_predK Hgt0n) subnS.
      case Hszmtl : (size mtl) => /=.
      + rewrite (size0nil Hszmtl)/= subn0 /rev/= cat1s shlB1_zeros dropmsb_joinlsb; last rewrite -Hsznq //.
        rewrite -low_dropmsb; last rewrite -Hsznq -ltnS (ltn_predK Hgt0n)//.
        rewrite -subn1 -size_dropmsb low_size//.
      + rewrite (eqP Hmtl) Hszmtl.
        have {1}-> : (zeros n = zeros (size (b1 :: zeros n.-1))) by rewrite /= size_zeros zeros_cons (ltn_predK Hgt0n).
        rewrite udivB_rec0// -Hszmtl -addn1 -{2}(size_zeros (size mtl)) -(size_joinlsb true (zeros (size mtl))).
        rewrite -(size_rev (joinlsb true (zeros (size mtl)))) /joinlsb high_size shlB_zeros !shlB1_zeros/= size_zeros zeros_cons (ltn_predK Hgt0n).
        generalize Hsznm; rewrite /= -subn_gt0 => Hsznm'.
        rewrite rev_cons cat_rcons (eqP (rev_zeros _)) -/joinlsb -low_joinlsb -low_dropmsb;
          last rewrite size_joinlsb -Hsznq (ltn_predK Hsznm') addn1 ltnS leq_subr//.
        rewrite -Hsznq (ltn_predK Hsznm') Hsznq.
        have {2}-> : (size q = size (dropmsb (joinlsb true q))) by rewrite size_dropmsb size_joinlsb addnK.
        rewrite shlB_cat// size_dropmsb size_joinlsb addnK -Hsznq (ltnW Hsznm)//.
    - rewrite size_zeros. case Hmhd : mhd; rewrite /=.
      + generalize Hgt0n; rewrite -{1}(size_zeros n) => H'.
        rewrite (dropmsb_joinlsb true H') dropmsb_zeros /leB eq_refl orTb subB_same size_joinlsb size_zeros addn1 (ltn_predK Hgt0n).
        have Hszaux : (n = size (dropmsb (joinlsb true q))) by rewrite size_dropmsb size_joinlsb addnK//.
        rewrite (IH n (dropmsb (joinlsb true q)) (negbT Hmtl) Hgt0n (ltnW Hsznm) Hszaux) rev_cons high_rcons cat_rcons -Hszaux.
        generalize Hsznm; rewrite /= -subn_gt0 => Hsznm'.
        rewrite subnS -/joinlsb -low_joinlsb -Hsznq (ltn_predK Hsznm') shlB_zeros shlB1_zeros low_dropmsb// size_joinlsb -Hsznq addn1 ltnS leq_subr//.
      + rewrite (dropmsb_joinlsb false Hgt0nz) dropmsb_zeros /leB eqseq_cons/= ltB_cons_ss// andbF orFb ltBnn /joinlsb zeros_cons (ltn_predK Hgt0n).
        rewrite shlB_zeros shlB1_zeros.
        have Hszaux : (n = size (dropmsb (joinlsb false q))) by rewrite size_dropmsb size_joinlsb addnK//.
        rewrite (IH n (dropmsb (false :: q)) (negbT Hmtl) Hgt0n (ltnW Hsznm) Hszaux) rev_cons high_rcons cat_rcons -Hszaux.
        generalize Hsznm; rewrite /= -subn_gt0 => Hsznm'.
        rewrite subnS -/joinlsb -low_joinlsb -Hsznq (ltn_predK Hsznm') shlB_zeros low_dropmsb// size_joinlsb -Hsznq addn1 ltnS leq_subr//.
  Qed.

  Lemma udivB1: forall m, ~~(m==zeros(size m)) -> udivB m (from_Zpos (size m) 1) = (m, zeros (size m)).
  Proof.
    move => m Hm.
    move : (neq_zero_size_gt0 Hm) => Hsz.
    rewrite /udivB size_rev (to_Zpos_from_Zpos_1 Hsz).
    have -> : from_Zpos (size m) 1 = cons b1 (zeros (size m - 1)).
    {
      apply to_Zpos_inj_ss; first rewrite size_from_Zpos/= size_zeros subn1 (ltn_predK Hsz)//.
      rewrite to_Zpos_from_Zpos_1// to_Zpos_joinlsb to_Zpos_zeros Z.add_0_l//.
    }
    rewrite -{2}(ltn_predK Hsz) -subn1 -zeros_cons eqseq_cons andFb subn1.
    move : Hsz; rewrite -(size_rev m) => Hsz.
    move : (neq_copy_rev_neq_copy Hm) => Hrm.
    have Hszq : (size (rev m) = size (zeros (size (rev m)))) by rewrite size_zeros.
    rewrite (udivB1_rec Hrm Hsz (leqnn (size (rev m))) Hszq) revK size_rev high_size size_zeros subnn low0 cats0 shlB_zeros//.
  Qed.

  Lemma ltB_dropmsb_joinlsb_ltB :
    forall m n b, size m = size n -> ltB m n ->
                  ltB (dropmsb (joinlsb b m) -# n) (n ++ [::(borrow_subB (dropmsb (joinlsb b m)) n)] ).
  Proof.
    intros.
    move : H0.
    rewrite !to_Zpos_ltB. move => H0.
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
      have Haux : (Z.odd (2 ^ Z.of_nat (size m)) = false)%Z by lia.
      move : (Zmod_odd' (to_Zpos m * 2 + true) (@pow2_nat2z_nonzero (size m)) Haux).
      by rewrite Z.odd_add Z.odd_mul/= andbF /= Heq Z.odd_mul/=andbF.
    - rewrite Z.add_0_r (Z.mul_comm 2 (to_Zpos n)).
      move : (Z.mul_nonneg_nonneg _ _ (@to_Zpos_ge0 m) (Z.le_0_2)) => Haux.
      move : (Z.pow_pos_nonneg _ _ (Z.lt_0_2) (Nat2Z.is_nonneg (size m))) => Haux2.
      move : (Z.mod_le _ _ Haux Haux2) => {Haux}{Haux2}Hmodle.
      move : (Zmult_lt_compat_r _ _ _ Z.lt_0_2 H0) => Hlt.
      exact : (Z.le_lt_trans _ _ _ Hmodle Hlt).
  Qed.

  Lemma uremB_rec_ltB :
    forall m d q r , size m <= size d -> size r = size d ->size q = size d ->
                       ~~(d == zeros (size d)) ->
                       ltB r d ->
                       (udivB_rec m d q r).2 <# d.
  Proof.
    elim => [|mhd mtl IH] d q r Hszdm Hszdr Hszdq Hdnot0 Hltrd; first done.
    move : (neq_zeros_to_nat_gt0 Hdnot0).
    move : (neq_zero_size_gt0 Hdnot0) => Hszd0.
    rewrite -{1}(to_nat_zeros (size d)) -to_nat_ltB. move => Hdgt0.
    case Hcond : (d <=# (dropmsb (joinlsb mhd r))).
    - rewrite /= Hcond /=.
      have Hszdr' : size (dropmsb (joinlsb mhd r) -# d) = size d by rewrite size_subB size_dropmsb size_joinlsb Hszdr addnK minnn.
      have Hszdq' : size (dropmsb (joinlsb true q)) = size d by rewrite size_dropmsb size_joinlsb Hszdq addnK.
      have Hszdr'' : size d = size (dropmsb (joinlsb mhd r)) by rewrite size_dropmsb size_joinlsb Hszdr addnK.
      move : (ltB_dropmsb_joinlsb_ltB mhd Hszdr Hltrd).
      rewrite -ltB_equiv_borrow_subB//. symmetry in Hszdr''; rewrite (ltBNle Hszdr'') Hcond/=.
      rewrite to_Zpos_ltB to_Zpos_cat/= Z.add_0_r -to_Zpos_ltB => Hltsub.
      exact: (IH d (dropmsb (joinlsb true q)) (dropmsb (joinlsb mhd r) -# d) (ltnW Hszdm) Hszdr' Hszdq' Hdnot0 Hltsub).
    - rewrite /= Hcond /=.
      have Hszdr' : size (dropmsb (joinlsb mhd r)) = size d by rewrite size_dropmsb size_joinlsb Hszdr addnK.
      generalize Hcond. rewrite leBNlt// => /negbFE Hcondlt.
      have Hszdq' : size (dropmsb (joinlsb false q)) = size d by rewrite size_dropmsb size_joinlsb Hszdq addnK.
      have Hszdr'' : size (dropmsb (joinlsb mhd r)) = size d by rewrite size_dropmsb size_joinlsb addnK Hszdr.
      exact: (IH d (dropmsb (joinlsb false q)) (dropmsb (joinlsb mhd r)) (ltnW Hszdm) Hszdr' Hszdq' Hdnot0 Hcondlt).
  Qed.

  Lemma udivB_rec_cat :
    forall m n d q r , size m <= size d -> size r = size d ->size q = size d ->
                    ~~(d == zeros (size d)) ->
                    ltB r d ->
                    (udivB_rec (m ++ n) d q r) =
                    (udivB_rec n d (udivB_rec m d q r).1 (udivB_rec m d q r).2).
  Proof.
    elim => [|mhd mtl IHm] n d q r Hszdm Hszdr Hszdq Hdnot0 Hltrd; first done.
    - move : (neq_zeros_to_Zpos_gt0 Hdnot0) => Hgt0z.
      move : (neq_zero_size_gt0 Hdnot0) => Hszd0. rewrite/=.
      case Hcondn : (d <=# dropmsb (joinlsb mhd r)).
      + have Hszdr' : size (dropmsb (joinlsb mhd r) -# d) = size d by rewrite size_subB size_dropmsb size_joinlsb Hszdr addnK minnn.
        have Hszdq' : size (dropmsb (joinlsb true q)) = size d by rewrite size_dropmsb size_joinlsb Hszdq addnK.
        have Hszdr'' : size (dropmsb (joinlsb mhd r)) = size d by rewrite size_dropmsb size_joinlsb addnK Hszdr.
        move : (ltB_dropmsb_joinlsb_ltB mhd Hszdr Hltrd) => Hdjsub.
        rewrite -(ltB_equiv_borrow_subB Hszdr'') (ltBNle Hszdr'') Hcondn in Hdjsub.
        move : Hdjsub. have -> : [:: false] = zeros 1 by done.
        rewrite to_Zpos_ltB to_Zpos_cat to_Zpos_zeros Z.mul_0_l Z.add_0_r -to_Zpos_ltB.
        move => Hdjsub.
        exact : (IHm n d (dropmsb (joinlsb true q)) (dropmsb (joinlsb mhd r) -# d) (ltnW Hszdm) Hszdr' Hszdq' Hdnot0 Hdjsub).
      + have Hszdr' : size d = size (dropmsb (joinlsb mhd r)) by rewrite size_dropmsb size_joinlsb Hszdr addnK.
        have Hszdr'' : size (dropmsb (joinlsb mhd r)) = size d by rewrite size_dropmsb size_joinlsb Hszdr addnK.
        have Hszdq' : size (dropmsb (joinlsb false q)) = size d by rewrite size_dropmsb size_joinlsb Hszdq addnK.
        rewrite (leBNlt Hszdr') in Hcondn. move/negbFE : Hcondn => Hcondn.
        exact : (IHm n d (dropmsb (joinlsb false q)) (dropmsb (joinlsb mhd r)) (ltnW Hszdm) Hszdr'' Hszdq' Hdnot0 Hcondn).
  Qed.

  Lemma udivB_rec_cat_exists :
    forall x m n , size m <= size n ->
                   x <= size m ->
                   ~~(n == zeros (size n)) ->
                   udivB_rec m n (zeros (size n)) (zeros (size n)) = udivB_rec (high (size m - x) m) n (udivB_rec (low x m) n (zeros (size n)) (zeros (size n))).1  (udivB_rec (low x m) n (zeros (size n)) (zeros (size n))).2.
  Proof.
    intros.
    move : (neq_zeros_to_nat_gt0 H1).
    move : (neq_zero_size_gt0 H1) => Hszn0.
    rewrite -{1}(to_nat_zeros (size n)) -to_nat_ltB.  move => Hngt0.
    have {1}->: m = low x m ++ high (size m - x) m
      by rewrite cat_low_high; [done | rewrite (subnKC H0)].
    rewrite udivB_rec_cat; try (done|| by rewrite size_zeros).
    by rewrite size_low (leq_trans H0 H).
  Qed.

  Lemma to_Zpos_cat_Zdiv :
    forall m n d, to_Zpos d <> 0%Z ->
                  (to_Zpos (m ++ n) / (to_Zpos d)
                   = (Zmod (to_Zpos m) (to_Zpos d) + (to_Zpos n) * 2 ^ Z.of_nat (size m)) / (to_Zpos d) + (to_Zpos m)/ (to_Zpos d))%Z.
  Proof.
    intros.
    rewrite to_Zpos_cat (Z.mod_eq _ _ H). symmetry.
    rewrite -Z.add_opp_r.
    rewrite (Z.add_comm (to_Zpos m) (-(to_Zpos d * (to_Zpos m / to_Zpos d)))).
    rewrite -Z.mul_opp_r.
    rewrite (Z.mul_comm (to_Zpos d) (- (to_Zpos m / to_Zpos d))).
    rewrite -Z.add_assoc (Z.div_add_l _ _ _ H) Z.add_shuffle0 Z.add_opp_diag_l.
      by rewrite Z.add_0_l.
  Qed.

  Lemma to_Zpos_cat_Zmod :
    forall m n d, to_Zpos d <> 0%Z ->
                  (to_Zpos (m ++ n) mod (to_Zpos d))%Z
                   = (((to_Zpos m) mod (to_Zpos d) + (to_Zpos n) *  2 ^ Z.of_nat (size m)) mod (to_Zpos d))%Z.
  Proof.
    intros.
    by rewrite to_Zpos_cat Zplus_mod_idemp_l.
  Qed.

  Lemma foo_aux bs n :
    lsb bs = b0 ->
    to_Zpos ((bs +# from_nat (size bs) 1) <<# n) =
    (to_Zpos (bs <<# n) + to_Zpos (from_nat (size bs) 1 <<# n))%Z.
  Proof.
    case/orP: (leq_gtn_total (size bs) n) => Hsz Hlsb.
    - rewrite shlB_oversize; last by rewrite size_addB size_from_nat minnn.
      rewrite (shlB_oversize Hsz) shlB_oversize; last by rewrite size_from_nat.
      rewrite !to_Zpos_zeros; reflexivity.
    - rewrite 3!to_Zpos_shlB size_addB size_from_nat minnn.
      rewrite (@to_Zpos_low_high _ (size bs - n) n);
        last by rewrite (subnK (ltnW Hsz)) size_addB size_from_nat minnn.
      rewrite (@to_Zpos_low_high bs (size bs - n) n);
        last by rewrite (subnK (ltnW Hsz)).
      rewrite 2!Z.mul_add_distr_r -2!Z.mul_assoc
              -(Z.pow_add_r _ _ _ (Nat2Z.is_nonneg _) (Nat2Z.is_nonneg _)).
      rewrite -Nat2Z.inj_add.
      have->: (size bs - n + n)%coq_nat = size bs - n + n by reflexivity.
      rewrite (subnK (ltnW Hsz)) 2!Z_mod_plus_full.
      have Hbnd : forall ps, (0 <= to_Zpos (low (size bs - n) ps)
                                   * 2 ^ Z.of_nat n < 2 ^ Z.of_nat (size bs))%Z.
      {
        split.
        + apply Z.mul_nonneg_nonneg; [exact: to_Zpos_ge0 | by apply Z.pow_nonneg].
        + rewrite -{2}(subnK (ltnW Hsz)) Nat2Z.inj_add Z.pow_add_r;
            try exact: Nat2Z.is_nonneg.
          apply Zmult_lt_compat_r; first exact: pow2_nat2z_gt0.
          have{2}<-: size (low (size bs - n) ps) = size bs - n by rewrite size_low.
          exact: to_Zpos_bounded.
      }
      rewrite (Z.mod_small); last exact: Hbnd.
      rewrite (Z.mod_small); last exact: Hbnd.
      move: (leq_ltn_trans (leq0n n) Hsz) => Hsz0.
      have Hbnd1 : (0 <= to_Zpos (size bs) -bits of (1) * 2 ^ Z.of_nat n
                      < 2 ^ Z.of_nat (size bs))%Z.
      {
        rewrite (eqP (from_natn1 Hsz0)) to_Zpos_zext Z.mul_1_l.
        split; first (apply Z.lt_le_incl; exact: pow2_nat2z_gt0).
        apply Z.pow_lt_mono_r;
          [done | exact: Nat2Z.is_nonneg | by apply Nat2Z.inj_lt; apply/ltP].
      }
      rewrite (Z.mod_small _ _ Hbnd1) -Z.mul_add_distr_r.
      rewrite low_addB ?size_from_nat; try exact: leq_subr.
      rewrite -{3}(subnK (ltnW Hsz)) low_from_nat. rewrite -subn_gt0 in Hsz.
      have->: to_Zpos (size bs) -bits of (1) = to_Zpos ((size bs - n) -bits of (1))
        by rewrite (eqP (from_natn1 Hsz0)) (eqP (from_natn1 Hsz)) !to_Zpos_zext.
      rewrite -to_Zpos_addB; last by rewrite size_low size_from_nat.
      have{6}->: size bs - n = size (low (size bs - n) bs) by rewrite size_low.
      rewrite joinlsb0_addB1_nocarry; last by rewrite lsb_low.
      by rewrite Z.mul_0_l Z.add_0_r.
  Qed.

  Lemma foo bs : succB bs = from_nat (size bs) (to_nat bs).+1.
  Proof.
    rewrite from_natSn_from_nat from_nat_to_nat addB1. reflexivity.
  Qed.

  Lemma dropmsb_joinlsb_b0_mulB bs1 bs2 :
    size bs1 = size bs2 ->
    dropmsb (joinlsb b0 bs1) *# bs2 = dropmsb (joinlsb b0 (bs1 *# bs2)).
  Proof.
    intros. apply to_Zpos_inj_ss; first rewrite size_mulB !size_dropmsb !size_joinlsb size_mulB//.
    rewrite to_Zpos_mulB' !to_Zpos_dropmsb !to_Zpos_joinlsb to_Zpos_mulB' !Z.add_0_r !size_joinlsb size_mulB size_dropmsb size_joinlsb addnK.
    have -> : (Z.of_nat (size bs1 + 1) - 1 = Z.of_nat (size bs1))%Z.
    {
      rewrite Nat2Z.inj_add Z.add_simpl_r//.
    }
    symmetry; rewrite -Zmult_mod_distr_r Zmod_Zmod_lt; [| exact: pow2_nat2z_gt0 | by auto with zarith].
    rewrite -{2}(Z.mod_small _ _ (conj (@to_Zpos_ge0 bs2) (to_Zpos_bounded bs2))) -H -Zmult_mod.
    by rewrite (Z.mul_shuffle0).
  Qed.

  Lemma dropmsb_joinlsb_b0_b_addB bs1 bs2 b :
    size bs1 = size bs2 ->
    dropmsb (joinlsb b0 bs1) +# dropmsb (joinlsb b bs2) = dropmsb (joinlsb b (bs1 +# bs2)).
  Proof.
    intros. apply to_Zpos_inj_ss; first rewrite size_addB !size_dropmsb !size_joinlsb size_addB !addnK//.
    rewrite to_Zpos_addB'; last rewrite !size_dropmsb !size_joinlsb H//.
    rewrite !to_Zpos_dropmsb size_dropmsb !size_joinlsb size_addB -H minnn addnK !to_Zpos_joinlsb !Z.add_0_r.
    have -> : (Z.of_nat (size bs1 + 1) - 1 = Z.of_nat (size bs1))%Z.
    {
      rewrite Nat2Z.inj_add Z.add_simpl_r//.
    }
    rewrite to_Zpos_addB'//.
    rewrite -Z.add_mod; last (apply Z.pow_nonzero; by auto with zarith).
    rewrite Z.add_assoc Z.add_comm -Zplus_mod_idemp_r -Zmult_mod_distr_r Z.add_mod_idemp_r; last (apply Z.pow_nonzero; by auto with zarith).
    symmetry.
    rewrite Z.add_comm -Z.add_mod_idemp_r; last (apply Z.pow_nonzero; by auto with zarith).
    rewrite Zmod_Zmod_lt; [| exact: pow2_nat2z_gt0 | by auto with zarith].
    by rewrite Zplus_mod_idemp_r Z.mul_add_distr_r//.
  Qed.

  Lemma from_Zpos_Zdiv2_mul2_odd n z : (0 <= z)%Z -> (z < 2 ^ Z.of_nat n)%Z -> from_Zpos (n).+1 z = rcons (from_Zpos (n) z) b0.
  Proof.
    intros.
    rewrite /= Z.div2_div -{2}(to_Zpos_from_Zpos_bounded H H0).
    have -> : (2 = 2 ^ Z.of_nat 1)%Z by done. rewrite -to_Zpos_shrB.
    have Haux : size (from_Zpos n z >># 1) = n by rewrite size_shrB size_from_Zpos//.
    rewrite -{1}Haux from_Zpos_to_Zpos.
    apply to_Zpos_inj_ss; first rewrite size_joinlsb size_shrB size_rcons size_from_Zpos addn1//.
    rewrite to_Zpos_joinlsb to_Zpos_shrB Z.pow_1_r (to_Zpos_from_Zpos_bounded H H0) Z.mul_comm -Z.div2_div -Z.div2_odd.
    rewrite to_Zpos_rcons Z.mul_0_l (to_Zpos_from_Zpos_bounded H H0) Z.add_0_r//.
  Qed.

  Lemma ltB_foo_aux r n b :
    0 < size r -> size r = size n -> r <# n -> n <=# dropmsb (joinlsb b r) -> ~~ (msb r).
  Proof.
    intros.
    rewrite ->to_Zpos_leB in H2; last rewrite size_dropmsb size_joinlsb addnK//. move : H2.
    rewrite (dropmsb_joinlsb b H) to_Zpos_joinlsb => H2.
    rewrite ->to_Zpos_ltB in H1. move : (Z.lt_le_trans _ _ _ H1 H2).
    rewrite -{1}(joinmsb_splitmsb H) to_Zpos_joinmsb -/(msb _) /dropmsb size_splitmsb.
    case Hm : (msb r); try done.
    rewrite Z.mul_1_l -Zred_factor1 Z.add_shuffle0.
    rewrite <-Z.add_lt_mono_r.
    move : (to_Zpos_bounded (splitmsb r).1); rewrite size_splitmsb.
    case b; last rewrite Z.add_0_r.
    - move => /Zlt_not_le Hlt /Zlt_succ_le Hle. by apply Hlt in Hle.
    - move => /Z.lt_asymm => Hlt Hnlt. by apply Hlt in Hnlt.
  Qed.

  Lemma div_foo mtl r n :
    (0 < to_Zpos n)%Z -> r <# n ->
    ((to_Zpos (mtl) + to_Zpos r * 2 ^ Z.of_nat (size mtl)) / to_Zpos n < 2 ^ Z.of_nat (size mtl))%Z.
  Proof.
    move => H0 H1.
    rewrite -(to_Zpos_cat _ _).
    have Haux : (to_Zpos (mtl ++ r) < to_Zpos n * 2 ^ Z.of_nat (size (mtl)))%Z.
    {
      rewrite to_Zpos_cat.
      rewrite ->to_Zpos_ltB in H1. rewrite <-Z.lt_0_sub in H1.
      rewrite Z.lt_add_lt_sub_r -Z.mul_sub_distr_r Z.mul_comm.
      move : (Zlt_le_succ _ _ H1) => H2.
      move : (pow2_nat2z_gt0 (size mtl)) => H3.
      rewrite ->(Z.le_mul_diag_r _ _ H3) in H2.
      exact : (Z.lt_le_trans _ _ _ (to_Zpos_bounded (mtl)) H2).
    }
    apply Z.div_lt_upper_bound; try done.
  Qed.

  Lemma from_Zpos_Zdiv2_mul2 n z : (0 <= z)%Z -> (z < 2 ^ Z.of_nat n)%Z -> from_Zpos (n).+1 (2 ^ Z.of_nat (n) + z) = rcons (from_Zpos (n) z) b1.
  Proof.
    intros. apply to_Zpos_inj_ss; first rewrite size_rcons !size_from_Zpos //.
    rewrite to_Zpos_from_Zpos; last (apply Z.add_nonneg_nonneg; [apply Z.lt_le_incl, pow2_nat2z_gt0| done]).
    rewrite to_Zpos_rcons Z.mul_1_l size_from_Zpos to_Zpos_from_Zpos_bounded//.
    rewrite Z.mod_small; first rewrite Z.add_comm//.
    split; first (apply Z.add_nonneg_nonneg; [apply Z.lt_le_incl, pow2_nat2z_gt0| done]).
    rewrite -addn1 Nat2Z.inj_add Z.pow_add_r; [| by auto with zarith | by auto with zarith].
    rewrite Z.pow_1_r -Zred_factor1.
    exact : (Zplus_lt_compat_l _ _ (2 ^ Z.of_nat n) H0).
  Qed.

  Lemma msb1_to_Zpos_bounded bs : 0 < size bs -> msb bs <-> (2 ^ Z.of_nat (size bs - 1) <= to_Zpos bs)%Z.
  Proof.
    split.
    - intros.
      move : (msb_1_size_gt0 H0) => Hsz. rewrite -{2}(joinmsb_splitmsb Hsz) -/(msb _) H0 to_Zpos_rcons size_splitmsb.
      rewrite Z.mul_1_l -{1}(Z.add_0_l (2 ^ Z.of_nat (size bs - 1))); apply Zplus_le_compat_r, to_Zpos_ge0.
    - rewrite -{2}(joinmsb_splitmsb H) -/(msb _) to_Zpos_rcons.
      case (msb bs); first done. rewrite Z.mul_0_l Z.add_0_r.
      move : (to_Zpos_bounded (splitmsb bs).1); rewrite size_splitmsb => /Zle_not_lt. done.
  Qed.

  Lemma udivB_rec_step :
    forall m n q r, 0 < size m -> 0 < size n -> size n = size m -> size n = size r -> size n = size q ->
                    udivB_rec m n q r
                    = udivB_rec (splitlsb m).2 n ([::(~~ (((to_Zpos r)*2 + (lsb m)) mod 2 ^ Z.of_nat (size r) <? to_Zpos n)%Z)] ++ low (size m).-1 q) (subB (dropmsb (joinlsb (lsb m) r)) (andB (copy (size n)(~~ (((to_Zpos r) * 2 + (lsb m)) mod 2 ^ Z.of_nat (size r) <? to_Zpos n)%Z)) n)).
  Proof.
    elim => [| mhd mtl IH] n q r. done.
    move => Hszm Hszn Hsznm Hsznr Hsznq. rewrite /lsb /=.
    case Hcond : (n <=# dropmsb (joinlsb mhd r)); rewrite andB_copy_case.
    - rewrite -low_dropmsb_joinlsb; last by rewrite -Hsznq Hszn.
      have Hsz : (size n = size (dropmsb (joinlsb mhd r))) by rewrite size_dropmsb size_joinlsb addnK//.
      rewrite ->(to_Zpos_leB_eqn Hsz) in Hcond.
      rewrite to_Zpos_dropmsb to_Zpos_joinlsb size_joinlsb Nat2Z.inj_add Z.add_simpl_r in Hcond.
      rewrite Z.ltb_antisym Hcond/= -Hsznq Hsznm//.
    - rewrite -low_dropmsb_joinlsb; last by rewrite -Hsznq Hszn.
      have Hsz : size n = size (dropmsb (joinlsb mhd r)) by rewrite Hsznr size_dropmsb size_joinlsb addnK.
      rewrite ->(to_Zpos_leB_eqn Hsz) in Hcond.
      rewrite to_Zpos_dropmsb to_Zpos_joinlsb size_joinlsb Nat2Z.inj_add Z.add_simpl_r in Hcond.
      rewrite Z.ltb_antisym Hcond/= -Hsznq Hsznm from_natn0.
      have -> : (dropmsb (joinlsb mhd r) -# (zeros (size (mhd ::mtl)))) = dropmsb (joinlsb mhd r).
      apply to_Zpos_inj_ss; first rewrite size_subB -Hsz size_zeros -Hsznm minnn//.
      rewrite -(size_zeros (size n)) in Hsz; symmetry in Hsz.
      rewrite -Hsznm (to_Zpos_subB Hsz) -(ltB_equiv_borrow_subB Hsz) to_Zpos_zeros Z.sub_0_r ltB_zeros_r ltBn0//.
      done.
  Qed.

  Lemma to_Zpos_udivB_rec_div :
    forall m n q r , size m <= size n -> size r = size n ->size q = size n ->
                     r <# n ->
                     ~~ (n == zeros (size n)) ->
                     (to_Zpos (rev m ++ r) < 2 ^ Z.of_nat (size n))%Z ->
                     (udivB_rec m n q r).1 =
                     ((from_Zpos (size m) (Z.div (to_Zpos (rev m ++ r)) (to_Zpos n)))) ++ (low (size q - size m) q).
    Proof.
    elim => [|mhd mtl IH] n q r Hszmn Hszrn Hszqn Hltrn Hnneq0 Hltadd.
    - rewrite /= subn0 low_size//.
    - rewrite (lock from_Zpos) /lsb/= .
      generalize Hszmn; rewrite /= => /ltnW Hszmn'.
      generalize Hszmn ; rewrite /= -subn_gt0 => Hszmn''.
      generalize Hszmn ; rewrite /= => Haux. move : (leq_ltn_trans (leq0n (size mtl)) Haux) => Hszmn'''{Haux}.
      move : (neq_zeros_to_Zpos_gt0 Hnneq0) => Hgt0n.
      move : (Z.neq_sym _ _ (Z.lt_neq _ _ Hgt0n)) => Hnneq0z.
      move : (neq_zeros_to_Z_gt0 Hnneq0) => Hgt0nb.
      case Hlt : (n <=# dropmsb (joinlsb mhd r)).
      + have Hsznr: size n = size (dropmsb (joinlsb mhd r)).
        { rewrite size_dropmsb size_joinlsb addnK Hszrn//. }
        have Hszrn': size (dropmsb (joinlsb mhd r) -# n) = size n.
        { rewrite size_subB size_dropmsb size_joinlsb Hszrn addnK minnn//. }
        have Hszqn': size (dropmsb (joinlsb true q)) = size n.
        { rewrite size_dropmsb size_joinlsb addnK Hszqn//. }
        generalize Hlt. rewrite ->(to_Zpos_leB Hsznr) => Hzle.
        move : (ltB_dropmsb_joinlsb_ltB mhd Hszrn Hltrn). symmetry in Hsznr.
        generalize Hlt; rewrite leBNlt; last rewrite size_dropmsb size_joinlsb addnK//. move => Hlt'.
        rewrite -ltB_equiv_borrow_subB// (negbTE Hlt') to_Zpos_ltB to_Zpos_cat Z.mul_0_l Z.add_0_r -to_Zpos_ltB => Hlt''.
        generalize Hszmn'''; rewrite -Hszrn => Hszngt0.
        move : (ltB_foo_aux Hszngt0 Hszrn Hltrn Hlt) => Hmsbr.
        rewrite rev_cons to_Zpos_cat to_Zpos_rcons size_rcons size_rev Nat2Z.inj_succ /Z.succ in Hltadd.
        have Hltadd': (to_Zpos (rev mtl ++ dropmsb (joinlsb mhd r) -# n) < 2 ^ Z.of_nat (size n))%Z.
        {
          rewrite to_Zpos_cat (to_Zpos_subB Hsznr) -(ltB_equiv_borrow_subB Hsznr) (negbTE Hlt') Z.mul_0_l Z.add_0_l.
          rewrite size_rev dropmsb_joinlsb// to_Zpos_joinlsb Z.add_sub_swap.
          rewrite Z.mul_add_distr_r Z.mul_sub_distr_r -{1}(Z.pow_1_r 2).
          rewrite -Z.mul_assoc -Z.pow_add_r; [| by auto with zarith | by auto with zarith].
          rewrite (Z.add_comm 1 (Z.of_nat (size mtl))).
          rewrite (Z.add_comm (to_Zpos (dropmsb r) * 2 ^ (Z.of_nat (size mtl) + 1) - to_Zpos n * 2 ^ Z.of_nat (size mtl)) (mhd * 2 ^ Z.of_nat (size mtl))).
          rewrite Z.add_assoc.
          move : Hltadd; rewrite -{1}(joinmsb_splitmsb Hszngt0) -/(msb _) -/(dropmsb _) (negbTE Hmsbr) to_Zpos_joinmsb Z.mul_0_l Z.add_0_l => Hltadd.
          have Haux : (0 < to_Zpos n * 2 ^ Z.of_nat (size mtl))%Z.
          { apply Z.mul_pos_pos; [done| apply pow2_nat2z_gt0 ]. }
          rewrite ->(Z.lt_sub_pos (to_Zpos (dropmsb r) * 2 ^ (Z.of_nat (size mtl) + 1))) in Haux.
          move : (Zplus_lt_compat_l _ _ (to_Zpos (rev mtl) + mhd * 2 ^ Z.of_nat (size mtl)) Haux) => Haux2{Haux}.
          exact : (Z.lt_trans _ _ _ Haux2 Hltadd).
        }
        rewrite (IH _ _ _ Hszmn' Hszrn' Hszqn' Hlt'' Hnneq0 Hltadd').
        rewrite !size_dropmsb !size_joinlsb !addnK.
        rewrite subnS rev_cons cat_rcons -/joinlsb.
        rewrite low_dropmsb; last rewrite /= ltnS leq_subr//.
        rewrite 2!to_Zpos_cat !size_rev.
        have Haux : (to_Zpos (joinlsb mhd r) = to_Zpos (dropmsb (joinlsb mhd r))).
        {
          rewrite dropmsb_joinlsb// 2!to_Zpos_joinlsb -{1}(joinmsb_splitmsb Hszngt0) -/(msb r) (negbTE Hmsbr) to_Zpos_joinmsb Z.mul_0_l//.
        }
        rewrite Haux.
        generalize Hszmn'''; rewrite -{1}Hsznr => Hsz. rewrite -{2}(subB_addB Hsz Hsznr).
        rewrite to_Zpos_addB'//.
        have Hmodsm : ((to_Zpos (dropmsb (joinlsb mhd r) -# n) + to_Zpos n) < 2 ^ Z.of_nat (size (dropmsb (joinlsb mhd r) -# n)))%Z.
        {
          rewrite to_Zpos_subB// -ltB_equiv_borrow_subB// (negbTE Hlt') Z.mul_0_l Z.add_0_l Z.sub_add size_subB -Hsznr minnn.
          apply to_Zpos_bounded.
        }
        rewrite Z.mod_small;
          last (split; [apply Z.add_nonneg_nonneg; apply to_Zpos_ge0| done]).
        symmetry; rewrite Z.mul_add_distr_r Z.add_assoc Z.add_comm Z.mul_comm Z.div_add_l//.
        rewrite -lock from_Zpos_Zdiv2_mul2.
        rewrite cat_rcons -/joinlsb -low_joinlsb Hszqn (ltn_predK Hszmn'')//.
        apply Z.div_pos; try done.
        apply Z.add_nonneg_nonneg; try apply to_Zpos_ge0.
        apply Z.mul_nonneg_nonneg; [apply to_Zpos_ge0| apply Z.lt_le_incl, pow2_nat2z_gt0].
        rewrite -{1 2}(size_rev mtl). by apply div_foo.
      + have Hsznr: size n = size (dropmsb (joinlsb mhd r)).
        { rewrite size_dropmsb size_joinlsb addnK Hszrn//. }
        have Hsznr': size (dropmsb (joinlsb mhd r)) = size n.
        { rewrite size_dropmsb size_joinlsb addnK Hszrn//. }
        have Hszqn': size (dropmsb (joinlsb false q)) = size n.
        { rewrite size_dropmsb size_joinlsb addnK Hszqn//. }
        generalize Hszmn'''; rewrite -Hszrn => Hszrgt0.
        generalize Hlt. rewrite leBNlt// => /negbFE Hzle.
        have Hlt' : (to_Zpos (rev mtl ++ dropmsb (joinlsb mhd r)) < 2 ^ Z.of_nat (size n))%Z.
        {
          rewrite dropmsb_joinlsb// to_Zpos_cat to_Zpos_joinlsb.
          move : Hltadd; rewrite rev_cons cat_rcons to_Zpos_cat -/(joinlsb _ _) to_Zpos_joinlsb.
          rewrite 2!Z.mul_add_distr_r -{1 5}(Z.pow_1_r 2) -Z.mul_assoc -Z.pow_add_r; [| by auto with zarith | by auto with zarith].
          rewrite -Z.mul_assoc -Z.pow_add_r; [| by auto with zarith | by auto with zarith].
          rewrite 2!Z.add_assoc Z.add_shuffle0 => Hltadd. rewrite Z.add_shuffle0.
          have Haux : (to_Zpos (dropmsb r) <= to_Zpos r)%Z.
          {
            rewrite to_Zpos_dropmsb.
            move : (Z.mod_le _ _ (@to_Zpos_ge0 r) (pow2_nat2z_gt0 (size r - 1))).
            rewrite Nat2Z.inj_sub//; last by apply/ltP.
          }
          have Haux2 : (0 <= 2 ^ (1 + Z.of_nat (size (rev mtl))))%Z by apply Z.pow_nonneg.
          move : (Z.mul_le_mono_nonneg_r _ _ _ Haux2 Haux) => {Haux Haux2} Haux.
          move : (Zplus_le_compat_l _ _ (to_Zpos (rev mtl) + mhd * 2 ^ Z.of_nat (size (rev mtl))) Haux) => Haux2.
          exact : (Z.le_lt_trans _ _ _ Haux2 Hltadd).
        }
        rewrite (IH _ _ _ Hszmn' Hsznr' Hszqn' Hzle Hnneq0 Hlt').
        rewrite ->to_Zpos_ltB in Hltrn.
        have Haux : ~~ (msb r).
        {
          have Hltsz : (2 ^ Z.of_nat (size n) <= 2 ^ Z.of_nat (size (rev (mhd :: mtl) ++ r) -1 ))%Z.
          { apply Z.pow_le_mono_r;
              [done
              |apply Nat2Z.inj_le; apply/leP; rewrite size_cat size_rev/= Hszrn addSn subn1 leq_addl//].
          }
          move : (Z.lt_le_trans _ _ _ Hltadd Hltsz).
          rewrite -msb0_to_Zpos_bounded; last rewrite size_cat size_rev//.
          rewrite -(msb_high _ Hszrgt0) high_size_cat//.
        }
        rewrite -{2}(joinmsb_splitmsb Hszrgt0) -/(msb _) (negbTE Haux) rev_cons cat_rcons -/(joinlsb _) -/(dropmsb _).
        rewrite 2!to_Zpos_cat dropmsb_joinlsb// 2!to_Zpos_joinlsb to_Zpos_joinmsb Z.mul_0_l Z.add_0_l.
        rewrite size_dropmsb size_joinlsb addnK subnS low_dropmsb; last rewrite /= Hszqn ltnS leq_subr//.
        rewrite Hszqn -{1}(ltn_predK Hszmn'') low_joinlsb.
        rewrite -lock from_Zpos_Zdiv2_mul2_odd. rewrite cat_rcons//.
        apply Z.div_pos; try done; apply Z.add_nonneg_nonneg; try apply to_Zpos_ge0; apply Z.mul_nonneg_nonneg; try apply Z.lt_le_incl, pow2_nat2z_gt0.
        apply Z.add_nonneg_nonneg; try by case mhd.
        apply Z.mul_nonneg_nonneg; [apply to_Zpos_ge0| by auto with zarith].
        have -> : (to_Zpos (dropmsb r) * 2 + mhd = to_Zpos (dropmsb (joinlsb mhd r)))%Z
          by rewrite dropmsb_joinlsb// to_Zpos_joinlsb.
        rewrite -(size_rev mtl). apply div_foo; done.
    Qed.

  (* Semantics of unsigned division *)

  Lemma to_Zpos_udivB : forall m n , size n = size m -> ~~(n == zeros (size n)) ->
                                     to_Zpos (udivB (rev m) n).1 = (Z.div (to_Zpos (rev m)) (to_Zpos n)).
  Proof.
    intros.  rewrite /udivB revK/=.
    move : (neq_zeros_to_Zpos_neq0 H0) => Hnneq0.
    move : ((neq_zeros_to_Zpos_gt0 H0)) => Hgt0.
    move : (Z.lt_le_incl _ _ (neq_zeros_to_Zpos_gt0 H0)) => Hge0.
    case Hcond : (from_Zpos (size m) (to_Zpos n) == zeros (size m)).
    move : (f_equal to_Zpos (eqP Hcond)). rewrite to_Zpos_from_Zpos_bounded. rewrite to_Zpos_zeros//.
    apply Z.lt_le_incl, neq_zeros_to_Zpos_gt0; done.
    rewrite -H; apply to_Zpos_bounded; done.
    rewrite to_Zpos_udivB_rec_div.
    move : (to_Zpos_bounded n) => Hbdn.
    move : (to_Zpos_bounded (rev m)); rewrite size_rev -H => Hbdm.
    rewrite size_zeros subnn low0/= cats0.
    rewrite to_Zpos_cat !to_Zpos_zeros !Z.mul_0_l !Z.add_0_r !to_Zpos_from_Zpos_bounded//.
    apply Z.div_pos; [apply to_Zpos_ge0|done].
    have Haux : (to_Zpos (rev m) < to_Zpos n * 2 ^ Z.of_nat (size n))%Z.
    {
      case Hc : (Z.eqb (to_Zpos n) 1)%Z. rewrite ->Z.eqb_eq in Hc. rewrite Hc Z.mul_1_l//.
      rewrite ->Z.eqb_neq in Hc. move : (not_Zeq _ _ Hc) => [ Hlt1 |Hgt1]. move/Zlt_le_succ : Hgt0.
      rewrite /= => /Zle_lt_or_eq. move =>[/Z.lt_asymm Hn |Hn']. done. rewrite -Hn' // in Hc.
      rewrite -{1}(Z.mul_1_l (to_Zpos (rev m))).
      apply Zmult_lt_compat; try done.
      split; try done. apply to_Zpos_ge0.
    }
    apply Z.div_lt_upper_bound; done.
    rewrite size_from_Zpos//.
    rewrite size_zeros size_from_Zpos//.
    rewrite size_zeros size_from_Zpos//.
    rewrite to_Zpos_ltB to_Zpos_zeros -H to_Zpos_from_Zpos_bounded//.
    apply to_Zpos_bounded. rewrite size_from_Zpos Hcond//.
    rewrite to_Zpos_cat to_Zpos_zeros Z.mul_0_l Z.add_0_r size_from_Zpos -(size_rev m).
    apply to_Zpos_bounded.
  Qed.

  Lemma to_Zpos_udivB' : forall m n ,
      size n = size m -> ~~ (n == zeros (size n)) ->
      to_Zpos (udivB' m n) = (Z.div (to_Zpos m) (to_Zpos n)).
  Proof.
    move=> m n Hsz Hn. rewrite -(revK m). rewrite -(size_rev m) in Hsz.
    exact: to_Zpos_udivB.
  Qed.

  Lemma udivB_lt bs1 bs2 :
    size bs1 = size bs2 ->
    ~~ (bs1 == zeros (size bs1)) ->
    (from_Zpos (size bs2) 1) <# bs2 ->
    (udivB bs1 bs2).1 <# bs1.
  Proof.
    intros.
    move : (neq_zero_size_gt0 H0) => Hsz1. generalize Hsz1; rewrite H; move => Hsz2.
    generalize H1. rewrite to_Zpos_ltB (to_Zpos_from_Zpos_1 Hsz2).
    move => Hgt1. move : (Z.lt_lt_pred _ _ Hgt1); rewrite/= -(to_Zpos_zeros (size bs2)) -to_Zpos_ltB.
    rewrite ltB_zeros_l ltB0n; move => Hneq0.
    rewrite to_Zpos_ltB -{1}(revK bs1) (to_Zpos_udivB _ Hneq0) ; last by rewrite size_rev.
    rewrite revK.
    apply Z.div_lt. move : (neq_zeros_to_Z_gt0 H0).
    by rewrite to_Zpos_ltB to_Zpos_zeros.
    done.
  Qed.

  Lemma udivB_small bs1 bs2 :
    size bs1 = size bs2 ->
    ~~ (bs2 == zeros (size bs2)) ->
    bs1 <# bs2 ->
    (udivB bs1 bs2).1 = zeros (size bs1).
  Proof.
    move => Hsz12 Hneq02 Hlt12.
    apply to_Zpos_inj_ss; first by rewrite size_zeros size_udivB.
    rewrite to_Zpos_zeros -(revK bs1) (to_Zpos_udivB _ Hneq02); last by rewrite size_rev Hsz12.
    generalize Hlt12; rewrite to_Zpos_ltB; move => Hltz12.
    move : (@to_Zpos_ge0 bs1) => Hge01.
    by rewrite revK Zdiv_small; last by split.
  Qed.

  Lemma udivB_small_iff bs1 bs2 : size bs1 = size bs2 ->
                                  leB (zeros (size bs1)) bs1 -> ltB (zeros (size bs2)) bs2 ->
                                  (udivB bs1 bs2).1 == zeros (size bs1) <-> ltB bs1 bs2.
  Proof.
    intros.
    generalize H1. rewrite ltB_zeros_l ltB0n ; move => Hneq02.
    split.
    - move => Hudiv. move: (f_equal to_Zpos (eqP Hudiv)).
      rewrite (to_Zpos_udivB' _ Hneq02); last done.
      move : H0; rewrite to_Zpos_leB; last by rewrite size_zeros. rewrite to_Zpos_zeros ; move => Hge0.
      move : H1; rewrite to_Zpos_ltB to_Zpos_zeros; move => Hgt0.
      rewrite Z.Private_NZDiv.div_small_iff; try done.
        by rewrite to_Zpos_ltB.
    - move => Hlt. by move/eqP : (udivB_small H Hneq02 Hlt).
  Qed.

  Lemma mulB_udivB_Numulo bs1 bs2 :
    size bs1 = size bs2 -> ~~ Umulo (udivB bs1 bs2).1 bs2 .
  Proof.
    move=> Hsz. symmetry in Hsz. rewrite umulo_to_Zpos size_udivB //=.
    case Hbs2 : (bs2 == zeros (size bs2)).
    - rewrite (eqP Hbs2) to_Zpos_zeros Z.mul_0_r.
      apply Z.pow_pos_nonneg; [done | exact: Nat2Z.is_nonneg].
    - apply negbT in Hbs2. rewrite (to_Zpos_udivB' Hsz Hbs2).
      apply (Z.le_lt_trans _ (to_Zpos bs1)); last exact: to_Zpos_bounded.
      rewrite Z.mul_comm. apply Z.mul_div_le.
      rewrite -ltB0n in Hbs2. apply to_Zpos_ltB in Hbs2. exact: Hbs2.
  Qed.

  Lemma mulB_udivB_leB bs1 bs2 :
    size bs1 = size bs2 -> (udivB bs1 bs2).1 *# bs2 <=# bs1.
  Proof.
    move=> Hsz. apply to_Zpos_leB; first by rewrite size_mulB size_udivB.
    rewrite (to_Zpos_mulB _ (mulB_udivB_Numulo Hsz)); last by rewrite size_udivB.
    case Hbs2 : (bs2 == zeros (size bs2)).
    - rewrite (eqP Hbs2) to_Zpos_zeros Z.mul_0_r. exact: to_Zpos_ge0.
    - apply negbT in Hbs2. symmetry in Hsz. rewrite (to_Zpos_udivB' Hsz Hbs2).
      rewrite Z.mul_comm. apply Z.mul_div_le.
      rewrite -ltB0n in Hbs2. apply to_Zpos_ltB in Hbs2. exact: Hbs2.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of unsigned modulo
  ---------------------------------------------------------------------------*)

  (* Definition *)

  Definition uremB bs1 bs2 := (udivB bs1 bs2).2.

  (* Size *)

  Lemma size_uremB_rec : forall n m q r, size m = size r -> size (udivB_rec n m q r).2 = size r.
  Proof.
    elim =>[|nhd ntl IH]m q r Hsz; first done.
    rewrite/= (IH m (dropmsb (joinlsb (m <=# dropmsb (joinlsb nhd r)) q))
       (if m <=# dropmsb (joinlsb nhd r)
        then dropmsb (joinlsb nhd r) -# m
        else dropmsb (joinlsb nhd r)));
      case H : (m <=# dropmsb (joinlsb nhd r)); try (by rewrite/=size_dropmsb size_joinlsb addnK|| by rewrite/=size_subB size_dropmsb size_joinlsb addnK Hsz minnn).
  Qed.

  Lemma size_uremB : forall n m , size (udivB n m).2 = size n.
  Proof.
    rewrite/udivB. intros.
    case Hm0: (from_Zpos (size (rev n)) (to_Zpos m) == zeros (size (rev n))); first done.
    rewrite size_rev size_uremB_rec; rewrite size_zeros; first done. by rewrite size_from_Zpos.
  Qed.

  Lemma urem0B : forall n (m: bits),
      n = size m ->
      uremB (zeros n) m = zeros n.
  Proof.
    move => n m Hsz. rewrite /uremB.
    case Hm0 : (m == zeros (size m)). rewrite /uremB /udivB (eqP Hm0) size_rev {1}Hsz {1}Hsz to_Zpos_zeros -zeros_from_Zpos size_zeros eq_refl//.
    rewrite /uremB udiv0B// (negbT Hm0)//.
  Qed.

  Lemma to_Zpos_uremB_rec :
    forall m n q r , size m <= size n -> size r = size n ->size q = size n ->
                     r <# n ->
                     ~~ (n == zeros (size n)) ->
                     ((to_Zpos (rev m ++ r)) < 2 ^ Z.of_nat (size n))%Z ->
                     (udivB_rec m n q r).2 =
                     ((from_Zpos (size r) (Zmod (to_Zpos (rev m ++ r)) (to_Zpos n)))).
  Proof.
    elim => [|mhd mtl IH] n q r Hszmn Hszrn Hszqn Hltrn Hnneq0 Hltbd.
    - rewrite /= Z.mod_small. rewrite from_Zpos_to_Zpos//.
      split; [apply to_Zpos_ge0|rewrite -to_Zpos_ltB//].
    - rewrite /lsb/= .
      generalize Hszmn; rewrite /= => /ltnW Hszmn'.
      generalize Hszmn ; rewrite /= -subn_gt0 => Hszmn''.
      generalize Hszmn ; rewrite /= => Haux. move : (leq_ltn_trans (leq0n (size mtl)) Haux) => Hszmn'''{Haux}.
      move : (neq_zeros_to_Zpos_gt0 Hnneq0) => Hgt0n.
      move : (Z.neq_sym _ _ (Z.lt_neq _ _ Hgt0n)) => Hnneq0z.
      move : (neq_zeros_to_Z_gt0 Hnneq0) => Hgt0nb.
      case Hlt : (n <=# dropmsb (joinlsb mhd r)).
      + have Hsznr: size n = size (dropmsb (joinlsb mhd r)).
        { rewrite size_dropmsb size_joinlsb addnK Hszrn//. }
        have Hszrn': size (dropmsb (joinlsb mhd r) -# n) = size n.
        { rewrite size_subB size_dropmsb size_joinlsb Hszrn addnK minnn//. }
        have Hszqn': size (dropmsb (joinlsb true q)) = size n.
        { rewrite size_dropmsb size_joinlsb addnK Hszqn//. }
        generalize Hlt. rewrite ->(to_Zpos_leB Hsznr) => Hzle.
        move : (ltB_dropmsb_joinlsb_ltB mhd Hszrn Hltrn). symmetry in Hsznr.
        generalize Hlt; rewrite leBNlt; last rewrite size_dropmsb size_joinlsb addnK//. move => Hlt'.
        rewrite -ltB_equiv_borrow_subB// (negbTE Hlt') to_Zpos_ltB to_Zpos_cat Z.mul_0_l Z.add_0_r -to_Zpos_ltB => Hlt''.
        generalize Hszmn'''; rewrite -Hszrn => Hszngt0.
        move : (ltB_foo_aux Hszngt0 Hszrn Hltrn Hlt) => Hmsbr.
        have Haux : (to_Zpos (joinlsb mhd r) = to_Zpos (dropmsb (joinlsb mhd r))).
        {
          rewrite dropmsb_joinlsb// 2!to_Zpos_joinlsb -{1}(joinmsb_splitmsb Hszngt0) -/(msb r) (negbTE Hmsbr) to_Zpos_joinmsb Z.mul_0_l//.
        }
        have Hltbd' : (to_Zpos (rev mtl ++ dropmsb (joinlsb mhd r) -# n) < 2 ^ Z.of_nat (size n))%Z.
        {
          rewrite to_Zpos_cat (to_Zpos_subB Hsznr) -(ltB_equiv_borrow_subB Hsznr) (negbTE Hlt') Z.mul_0_l Z.add_0_l.
          rewrite Z.mul_sub_distr_r size_rev.
          have Haux2 : (0 < to_Zpos n * 2 ^ Z.of_nat (size mtl))%Z.
          { apply Z.mul_pos_pos; [done|apply pow2_nat2z_gt0]. }
          rewrite ->(Z.lt_sub_pos (to_Zpos (dropmsb (joinlsb mhd r)) * 2 ^ Z.of_nat (size mtl))) in Haux2.
          move : (Zplus_lt_compat_l _ _ (to_Zpos (rev mtl)) Haux2) => {Haux2} Haux2.
          rewrite rev_cons cat_rcons -/(joinlsb _ _) to_Zpos_cat Haux size_rev in Hltbd.
          exact : (Z.lt_trans _ _ _ Haux2 Hltbd).
        }
        rewrite (IH _ _ _ Hszmn' Hszrn' Hszqn' Hlt'' Hnneq0 Hltbd').
        rewrite Hszrn' Hszrn.
        rewrite rev_cons cat_rcons -/joinlsb.
        rewrite 2!to_Zpos_cat !size_rev Haux.
        generalize Hszmn'''; rewrite -{1}Hsznr => Hsz. rewrite -{2}(subB_addB Hsz Hsznr).
        rewrite to_Zpos_addB'//.
        have Hmodsm : (0 <= (to_Zpos (dropmsb (joinlsb mhd r) -# n) + to_Zpos n) < 2 ^ Z.of_nat (size (dropmsb (joinlsb mhd r) -# n)))%Z.
        {
          split.
          - apply Z.add_nonneg_nonneg; try done; apply to_Zpos_ge0.
          - rewrite to_Zpos_subB// -ltB_equiv_borrow_subB// (negbTE Hlt') Z.mul_0_l Z.add_0_l Z.sub_add size_subB -Hsznr minnn.
            apply to_Zpos_bounded.
        }
        rewrite (Z.mod_small _ _ Hmodsm) Z.mul_add_distr_r Z.add_assoc.
        symmetry; rewrite -Zplus_mod_idemp_r (Z.mul_comm (to_Zpos n) (2 ^ Z.of_nat (size mtl))) Z_mod_mult Z.add_0_r//.
      + have Hsznr: size n = size (dropmsb (joinlsb mhd r)).
        { rewrite size_dropmsb size_joinlsb addnK Hszrn//. }
        have Hsznr': size (dropmsb (joinlsb mhd r)) = size n.
        { rewrite size_dropmsb size_joinlsb addnK Hszrn//. }
        have Hszqn': size (dropmsb (joinlsb false q)) = size n.
        { rewrite size_dropmsb size_joinlsb addnK Hszqn//. }
        generalize Hszmn'''; rewrite -Hszrn => Hszrgt0.
        generalize Hlt. rewrite leBNlt// => /negbFE Hzle.
        have Hltbd' : (to_Zpos (rev mtl ++ dropmsb (joinlsb mhd r)) < 2 ^ Z.of_nat (size n))%Z.
        {
          rewrite dropmsb_joinlsb// to_Zpos_cat to_Zpos_joinlsb.
          move : Hltbd; rewrite rev_cons cat_rcons to_Zpos_cat -/(joinlsb _ _) to_Zpos_joinlsb.
          rewrite 2!Z.mul_add_distr_r -{1 5}(Z.pow_1_r 2) -Z.mul_assoc -Z.pow_add_r; [| by auto with zarith | by auto with zarith].
          rewrite -Z.mul_assoc -Z.pow_add_r; [| by auto with zarith | by auto with zarith ].
          rewrite 2!Z.add_assoc Z.add_shuffle0 => Hltadd. rewrite Z.add_shuffle0.
          have Haux : (to_Zpos (dropmsb r) <= to_Zpos r)%Z.
          {
            rewrite to_Zpos_dropmsb.
            move : (Z.mod_le _ _ (@to_Zpos_ge0 r) (pow2_nat2z_gt0 (size r - 1))).
            rewrite Nat2Z.inj_sub//; last by apply/ltP.
          }
          have Haux2 : (0 <= 2 ^ (1 + Z.of_nat (size (rev mtl))))%Z by apply Z.pow_nonneg.
          move : (Z.mul_le_mono_nonneg_r _ _ _ Haux2 Haux) => {Haux Haux2} Haux.
          move : (Zplus_le_compat_l _ _ (to_Zpos (rev mtl) + mhd * 2 ^ Z.of_nat (size (rev mtl))) Haux) => Haux2.
          exact : (Z.le_lt_trans _ _ _ Haux2 Hltadd).
        }
        rewrite (IH _ _ _ Hszmn' Hsznr' Hszqn' Hzle Hnneq0 Hltbd').
        rewrite ->to_Zpos_ltB in Hltrn.
        have Haux : ~~ (msb r).
        {
          have Hltsz : (2 ^ Z.of_nat (size n) <= 2 ^ Z.of_nat (size (rev (mhd :: mtl) ++ r) -1 ))%Z.
          { apply Z.pow_le_mono_r;
              [done
              |apply Nat2Z.inj_le; apply/leP; rewrite size_cat size_rev/= Hszrn addSn subn1 leq_addl//].
          }
          move : (Z.lt_le_trans _ _ _ Hltbd Hltsz).
          rewrite -msb0_to_Zpos_bounded; last rewrite size_cat size_rev//.
          rewrite -(msb_high _ Hszrgt0) high_size_cat//.
        }
        rewrite -Hsznr Hszrn -{2}(joinmsb_splitmsb Hszrgt0) -/(msb _) -/(dropmsb _) (negbTE Haux).
        rewrite rev_cons cat_rcons -/(joinlsb _ _) 2!to_Zpos_cat dropmsb_joinlsb// 2!to_Zpos_joinlsb to_Zpos_joinmsb Z.mul_0_l Z.add_0_l//.
  Qed.

  (* Semantics of unsigned remainder *)

  Lemma to_Zpos_uremB : forall m n , size n = size m -> ~~(n == zeros (size n)) ->
                                     to_Zpos (udivB (rev m) n).2 = (Zmod (to_Zpos (rev m)) (to_Zpos n)).
  Proof.
    intros. rewrite/udivB revK /=.
    move : (neq_zeros_to_Zpos_gt0 H0) => Hgt0.
    move : (Z.lt_le_incl _ _ Hgt0) => Hge0.
    move : (to_Zpos_bounded (rev m)) => Hbdm.
    move : (to_Zpos_bounded n) => Hbdn. rewrite H in Hbdn.
    case Hcond : (from_Zpos (size m) (to_Zpos n) == zeros (size m)).
    move : (f_equal to_Zpos (eqP Hcond)). rewrite to_Zpos_from_Zpos_bounded//.
    rewrite to_Zpos_zeros// => Heq0. rewrite Heq0 // in Hgt0.
    rewrite to_Zpos_uremB_rec.
    rewrite size_zeros.
    rewrite to_Zpos_cat !to_Zpos_zeros !Z.mul_0_l !Z.add_0_r !to_Zpos_from_Zpos_bounded//.
    move : (Z.mod_pos_bound (to_Zpos (rev m)) _ Hgt0) => [Hge0' Hltbd]. done.
    move : (Z.mod_pos_bound (to_Zpos (rev m)) _ Hgt0) => [Hge0' Hltbd].
    move : (Z.lt_trans _ _ _ Hltbd (to_Zpos_bounded n)). by rewrite H.
    rewrite size_from_Zpos//.
    rewrite size_zeros size_from_Zpos//.
    rewrite size_zeros size_from_Zpos//.
    rewrite to_Zpos_ltB to_Zpos_zeros -H to_Zpos_from_Zpos_bounded//.
    apply to_Zpos_bounded. rewrite size_from_Zpos Hcond//.
    rewrite to_Zpos_cat to_Zpos_zeros Z.mul_0_l Z.add_0_r size_from_Zpos -(size_rev _).
    apply to_Zpos_bounded.
  Qed.

  Lemma to_Zpos_uremB' : forall m n ,
      size n = size m -> ~~ (n == zeros (size n)) ->
      to_Zpos (uremB m n) = (Zmod (to_Zpos m) (to_Zpos n)).
  Proof.
    move=> m n Hsz Hn. rewrite -(revK m). rewrite -(size_rev m) in Hsz.
    exact: to_Zpos_uremB.
  Qed.

  Lemma uremB_small bs1 bs2 :
    size bs1 = size bs2 ->
    ~~ (bs2 == zeros (size bs2)) ->
    bs1 <# bs2 ->
    (udivB bs1 bs2).2 = bs1.
  Proof.
    move => Hsz12 Hneq02 Hlt12.
    apply to_Zpos_inj_ss; first by rewrite size_uremB.
    rewrite -(revK bs1) (to_Zpos_uremB _ Hneq02); last by rewrite size_rev Hsz12.
    generalize Hlt12; rewrite to_Zpos_ltB; move => Hltz12.
    move : (@to_Zpos_ge0 bs1) => Hge01.
    by rewrite revK Zmod_small; last by split.
  Qed.

  Lemma uremB_small_iff bs1 bs2 : size bs1 = size bs2 ->
                                  leB (zeros (size bs1)) bs1 -> ltB (zeros (size bs2)) bs2 ->
                                  (uremB bs1 bs2) == bs1 <-> ltB bs1 bs2.
  Proof.
    intros.
    generalize H1. rewrite ltB_zeros_l ltB0n ; move => Hneq02.
    split.
    - move => Hudiv. move: (f_equal to_Zpos (eqP Hudiv)); rewrite (to_Zpos_uremB' _ Hneq02); last done.
      move : Hneq02.
      rewrite -ltB0n -(ltB_zeros_l (size bs2)) !to_Zpos_ltB to_Zpos_zeros.
      move => Hneq.
      rewrite (Z.mod_small_iff _ _ (Z.neq_sym _ _ (Z.lt_neq _ _ Hneq))).
      move => [[Hge0 Hlt]| [Hle0 Hlt]]; by auto with zarith.
    - rewrite to_Zpos_ltB; move => Hlt. apply/eqP; apply to_Zpos_inj_ss; first by rewrite size_uremB.
      rewrite (to_Zpos_uremB' _ Hneq02); last done.
      move : (@to_Zpos_ge0 bs1) => Hge0.
      rewrite Z.mod_small; by split.
  Qed.

  Lemma uremB_eq sb1 sb2 :
    0 < size sb1 -> size sb1 = size sb2 ->
    ~~(sb2 == zeros (size sb2))->
    uremB sb1 sb2 = subB sb1 (mulB (udivB sb1 sb2).1 sb2).
  Proof.
    intros.
    apply to_Zpos_inj_ss; first by rewrite size_subB size_uremB size_mulB size_udivB minnn.
    rewrite -{1}(revK sb1) (to_Zpos_uremB _ H1); last by rewrite size_rev H0.
    rewrite revK to_Zpos_subB; last by rewrite size_mulB size_udivB.
    rewrite -ltB_equiv_borrow_subB; last by rewrite size_mulB size_udivB.
    rewrite ltBNle; last by rewrite size_mulB size_udivB.
    rewrite (mulB_udivB_leB H0)/= (to_Zpos_mulB);
      [|by rewrite size_udivB H0| apply (mulB_udivB_Numulo H0)].
    rewrite Z.mod_eq; last (move : (neq_zeros_to_Z_gt0 H1); rewrite to_Zpos_ltB to_Zpos_zeros; by auto with zarith).
    rewrite Z.mul_comm -{4}(revK sb1) (to_Zpos_udivB _ H1); last by rewrite size_rev H0.
    by rewrite revK.
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

  (* Definition *)

  Definition sdivB' bs1' bs2' : bits * bits :=
    let bs1 := absB bs1' in
    let bs2 := absB bs2' in
    if (msb bs1' == msb bs2') && negb (msb bs1') then udivB bs1 bs2
    else if (msb bs1' == msb bs2') && (msb bs1')
         then ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2)
         else if (msb bs1' != msb bs2') && negb (msb bs1')
              then ((negB (udivB bs1 bs2).1), (udivB bs1 bs2).2)
              else (negB (udivB bs1 bs2).1, negB (udivB bs1 bs2).2).

  Definition sdivB bs1' bs2' : bits :=
    let bs1 := absB bs1' in
    let bs2 := absB bs2' in
    if (msb bs1' == msb bs2')
    then (udivB bs1 bs2).1
    else negB (udivB bs1 bs2).1.

  (* Size *)

  Lemma size_sdivB bs1 bs2 : size (sdivB bs1 bs2) = size bs1.
  Proof.
    rewrite /sdivB.
    case Hm1 : (msb bs1); case Hm2 : (msb bs2);
      try (by rewrite/= size_negB size_udivB size_absB||
              by rewrite size_udivB size_absB ||
                by rewrite size_udivB||
                   rewrite size_zeros).
  Qed.

  Lemma udivB_same bs : ~~(bs == zeros (size bs))->
                        (udivB bs bs) = (from_Zpos (size bs) 1, zeros (size bs)).
  Proof.
    intros.
    move : (neq_zeros_to_Z_gt0 H); rewrite to_Zpos_ltB to_Zpos_zeros; move => Hgt0.
    apply injective_projections; apply to_Zpos_inj_ss;
      [rewrite size_udivB size_from_Zpos//| |rewrite size_uremB size_zeros//|].
    - rewrite (to_Zpos_udivB' (eqP (eq_refl _)) H) Z.div_same; first by rewrite (to_Zpos_from_Zpos_1 (neq_zero_size_gt0 H)).
      by auto with zarith.
    - rewrite (to_Zpos_uremB' (eqP (eq_refl (size bs))) H) (Z.mod_same); first by rewrite to_Zpos_zeros.
      by auto with zarith.
  Qed.

  Lemma to_Z_zdiv_same sb1 sb2:
      msb sb1 == msb sb2 -> ~~ (sb2 == zeros (size sb2)) ->
      (0 <= to_Z sb1 / to_Z sb2)%Z.
  Proof.
    case Hm1 : (msb sb1); case Hm2 : (msb sb2); move =>//=_ Hn0.
    - rewrite high1_1_to_Z; last by rewrite high1_msb Hm1.
      rewrite high1_1_to_Z; last by rewrite high1_msb Hm2.
      rewrite Zdiv_opp_opp.
      apply Z.div_pos;
        [apply Z.le_le_succ_r; exact: to_Zneg_ge0|apply Zle_lt_succ; exact: to_Zneg_ge0].
    - move : (neq_zeros_to_nat_gt0 Hn0).
      move : (neq_zero_size_gt0 Hn0) => Hszn0.
      rewrite -{1}(to_nat_zeros (size sb2)) -to_nat_ltB.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
      rewrite to_Zpos_ltB to_Zpos_zeros; move => Hgt0.
      apply Z.div_pos;
        [exact: to_Zpos_ge0| done].
  Qed.

  Lemma to_Z_zdiv_diff sb1 sb2:
      ~~ (msb sb1 == msb sb2) -> ~~ (sb2 == zeros (size sb2)) ->
      (to_Z sb1 / to_Z sb2 <= 0)%Z.
  Proof.
    case Hm1 : (msb sb1); case Hm2 : (msb sb2); move =>//=_ Hn0.
    - rewrite high1_1_to_Z; last by rewrite high1_msb Hm1.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
      case Hmodz : (Z.eqb (Zmod (Z.succ (to_Zneg sb1)) (to_Zpos sb2)) 0%Z).
      + rewrite Z_div_zero_opp_full; [rewrite Z.opp_nonpos_nonneg| by move/Z.eqb_eq: Hmodz].
        move : (neq_zeros_to_nat_gt0 Hn0).
        move : (neq_zero_size_gt0 Hn0) => Hszn0.
        rewrite -{1}(to_nat_zeros (size sb2)) -to_nat_ltB.
        rewrite to_Zpos_ltB to_Zpos_zeros; move => Hgt0.
        apply Z.div_pos;
          [apply Z.le_le_succ_r; exact: to_Zneg_ge0| done].
      + rewrite Z_div_nz_opp_full;
          [ rewrite -Z.add_opp_r -Z.opp_add_distr
          | move=> H; move: (to_Zpos0 H) => {} H; rewrite -H eqxx in Hn0; discriminate
          | by move/Z.eqb_neq : Hmodz ].
        apply Z.opp_nonpos_nonneg; apply Z.add_nonneg_nonneg; try done.
        move : (neq_zeros_to_nat_gt0 Hn0).
        move : (neq_zero_size_gt0 Hn0) => Hszn0.
        rewrite -{1}(to_nat_zeros (size sb2)) -to_nat_ltB.
        rewrite to_Zpos_ltB to_Zpos_zeros; move => Hgt0.
        apply Z.div_pos; [apply Z.le_le_succ_r; exact: to_Zneg_ge0| done].
    - rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
      rewrite high1_1_to_Z; last by rewrite high1_msb Hm2.
      case Hmodz : (Z.eqb (Zmod (to_Zpos sb1) (Z.succ (to_Zneg sb2))) 0%Z).
      + rewrite Z_div_zero_opp_r; [rewrite Z.opp_nonpos_nonneg| by move/Z.eqb_eq: Hmodz].
        apply Z.div_pos;
          [apply to_Zpos_ge0| apply Zle_lt_succ; exact: to_Zneg_ge0].
      + case Heq0: (Z.eqb (Z.succ (to_Zneg sb2)) 0)%Z.
        * move/Z.eqb_eq: Heq0 => -> /=. rewrite Zdiv_0_r. exact: Z.le_refl.
        * move/Z.eqb_neq: Heq0 => Heq0.
          rewrite Z_div_nz_opp_r;
            [ rewrite -Z.add_opp_r -Z.opp_add_distr
            | assumption
            | by move/Z.eqb_neq : Hmodz].
          apply Z.opp_nonpos_nonneg; apply Z.add_nonneg_nonneg; try done.
          move : (neq_zeros_to_nat_gt0 Hn0).
          move : (neq_zero_size_gt0 Hn0) => Hszn0.
          rewrite -{1}(to_nat_zeros (size sb2)) -to_nat_ltB.
          rewrite to_Zpos_ltB to_Zpos_zeros; move => Hgt0.
          apply Z.div_pos; [apply to_Zpos_ge0| apply Zle_lt_succ; exact: to_Zneg_ge0].
  Qed.

  Lemma absB_neq0 sb1 : ~~((sb1) == zeros (size (sb1)))
                        -> ~~ (absB sb1 == zeros (size (sb1))).
  Proof.
    rewrite /absB. case (msb sb1); last done.
    apply contraNN; rewrite (negB_zeros' sb1) size_negB//.
  Qed.

  Lemma msb_absB bs : ~~(dropmsb bs == zeros (size bs -1)) ->
                      msb (absB bs) = b0.
  Proof.
    intro. rewrite/absB. case Hm: (msb bs).
    by rewrite -(msb_negB H) Hm. done.
  Qed.

  Lemma to_Z_sdivB_same_msb sb1 sb2 :
    0 < size sb1 -> size sb1 = size sb2 ->
    ~~(dropmsb sb1 == zeros (size sb1 -1)) ->
    ~~(sb2 == zeros (size sb2)) ->
    msb sb1 == msb sb2 ->
    to_Z (sdivB sb1 sb2) = Z.quot (to_Z sb1) (to_Z sb2).
  Proof.
    intros.
    rewrite /sdivB.
    - move : H3. have H' : 0 < size sb2 by rewrite -H0.
      move : (zeros_msb_dropmsb sb1); move : (zeros_msb_dropmsb sb2); rewrite (negbTE H2).
      case Hm1 : (msb sb1); case Hm2 : (msb sb2); move => //= Hz2 Hz1  _.
      + move : (neq_zeros_to_Z_neq0 H2) => Hneq02.
        rewrite (Z.quot_div _ _ Hneq02) (to_Z_sgn_msb (negbT Hz1)) (to_Z_sgn_msb H2).
        rewrite Hm1 Hm2. symmetry.
        rewrite Z.mul_comm -Z.opp_eq_mul_m1 Z.mul_opp_r-Z.opp_eq_mul_m1 Z.opp_involutive.
        symmetry.
        move : (absB_neq0 (negbT Hz1)) => Hanz1. rewrite -{1}(size_absB sb1) in Hanz1.
        move : (absB_neq0 H2) => Hanz2. rewrite -{1}(size_absB sb2) in Hanz2.
        rewrite to_Z_to_Zpos size_udivB size_absB -{1}(revK (absB sb1)) (to_Zpos_udivB _ Hanz2);
          last by rewrite size_rev !size_absB H0.
        rewrite revK.
        have Hszabs : size (absB sb1) = size (absB sb2) by rewrite !size_absB H0.
        case Hlt1 : (from_Zpos (size (absB sb2)) 1 <# absB sb2).
        move: (udivB_lt Hszabs Hanz1 Hlt1) => Hdivlt.
        rewrite (msb_ltB _ (msb_absB H1) Hdivlt); last by rewrite size_udivB.
        rewrite Z.mul_0_l Z.sub_0_r.
        rewrite /absB Hm1 Hm2 high1_1_to_Zpos_negB; last by rewrite high1_msb Hm1.
          by rewrite high1_1_to_Zpos_negB; last by rewrite high1_msb Hm2.
        move : Hlt1. rewrite ltBNle; last by rewrite size_from_Zpos.
        rewrite Bool.negb_false_iff. rewrite to_Zpos_leB_eqn; last by rewrite size_from_Zpos.
        rewrite size_absB (to_Zpos_from_Zpos_1 H') Z.leb_le.
        move : (neq_zeros_to_Z_gt0 Hanz2).
        rewrite to_Zpos_ltB to_Zpos_zeros.
        move => Hgt0.
        move/Zle_lt_or_eq => [Hlt| Heq].
        move/Zlt_le_succ : Hgt0. rewrite/=; move => Hgt1. by auto with zarith.
        rewrite Heq Z.div_1_r.
        generalize Heq. rewrite -(to_Zpos_from_Zpos_1 H'); move => Heq1.
        have Haux :(size (absB sb2) = size (from_Zpos (size sb2) 1)) by rewrite size_absB size_from_Zpos.
        move: (to_Zpos_inj_ss Haux Heq1) => {Haux} Habs1.
        rewrite Habs1/= -H0 -{1}(size_absB sb1).
        rewrite (udivB1 Hanz1)/= (msb_absB H1) Z.mul_0_l Z.sub_0_r.
        move : Habs1; rewrite /absB Hm1 Hm2; move=> Hneg2.
        have Haux: size (-# sb2) = size (from_Zpos (size sb2) 1) by rewrite size_negB size_from_Zpos.
        move : (f_equal to_Zpos Hneg2).
        rewrite high1_1_to_Zpos_negB; last by rewrite high1_msb Hm2.
        rewrite (to_Zpos_from_Zpos_1 H'); move => Habs1. rewrite Habs1.
        rewrite Z.div_1_r.
          by rewrite high1_1_to_Zpos_negB; last by rewrite high1_msb Hm1.
      + rewrite /absB Hm1 Hm2. symmetry.
        rewrite (negbTE H1) in Hz1. symmetry in Hz2.
        rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
        rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
        case Hlt1 : (from_Zpos (size sb2) 1 <# sb2).
        * move : (udivB_lt H0 (negbT Hz1) Hlt1) => Hdivlt.
          move : (msb_ltB (size_udivB sb1 sb2) Hm1 Hdivlt) => Hmu.
          rewrite high1_0_to_Z; last by rewrite high1_msb Hmu.
          rewrite -{2}(revK sb1) (to_Zpos_udivB _ H2); last by rewrite size_rev.
          rewrite revK Z.quot_div_nonneg//; [apply to_Zpos_ge0 | exact : (neq_zeros_to_Zpos_gt0 H2)].
        * move : Hlt1. rewrite ltBNle; last by rewrite size_from_Zpos.
          rewrite Bool.negb_false_iff to_Zpos_leB_eqn; last by rewrite size_from_Zpos.
          rewrite Z.leb_le.
          move/Zle_lt_or_eq => [Hlt| Heq].
          rewrite (to_Zpos_from_Zpos_1 H') in Hlt.
          move : (neq_zeros_to_Zpos_gt0 H2) => Hgt0. by auto with zarith.
          have Haux : size sb2 = size (from_Zpos (size sb2) 1) by rewrite size_from_Zpos.
          rewrite {2}(to_Zpos_inj_ss Haux Heq) Heq (to_Zpos_from_Zpos_1 H') Z.quot_1_r.
          rewrite -H0 (udivB1 (negbT Hz1))/=.
          by rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
  Qed.

  Lemma to_Z_sdivB_diff_msb sb1 sb2 :
    0 < size sb1 -> size sb1 = size sb2 ->
    ~~(dropmsb sb1 == zeros (size sb1 - 1))->
    ~~(sb2 == zeros (size sb2))->
    ~~ (msb sb1 == msb sb2) ->
    to_Z (sdivB sb1 sb2) = (Z.quot (to_Z sb1) (to_Z sb2)).
  Proof.
    intros.
    rewrite /sdivB.
    move : H3.
    have H' : 0 < size sb2 by rewrite -H0 H.
    have Hszabs : size (absB sb1) = size (absB sb2) by rewrite !size_absB H0.
    move : (zeros_msb_dropmsb sb1); move : (zeros_msb_dropmsb sb2); rewrite (negbTE H2).
    case Hm1 : (msb sb1); case Hm2 : (msb sb2);  move => //= Hz2 Hz1 _.
    - move/iffRL/contra: (negB_zeros' sb1) => Hnz1; rewrite Hz1 in Hnz1.
      move : (absB_neq0 (negbT Hz1)) => Hanz1.
      rewrite -(size_absB sb1) in Hanz1.
      rewrite/absB Hm1 Hm2.
      have Hszn12 : size sb2 = size (-# sb1) by rewrite size_negB H0.
      case Hgt1 : (from_Zpos (size (sb2)) 1 <# (sb2)).
      + symmetry in Hszn12.
        move : (udivB_lt Hszn12 (Hnz1 isT) Hgt1) => Hdivlt.
        move : (msb_negB H1); rewrite Hm1/=; move => Hnm1; symmetry in Hnm1.
        move : (msb_ltB (size_udivB (-# sb1) sb2) Hnm1 Hdivlt) => Hmu.
        move : (neq_zeros_to_Z_gt0 (Hnz1 isT)). rewrite to_Zpos_ltB to_Zpos_zeros.
        move => Hngt0.
        move : (Z.lt_le_incl _ _ Hngt0).
        rewrite -{1}(to_Zpos_zeros (size sb1)) -to_Zpos_leB; last by rewrite size_zeros size_negB.
        move => Hnge0. rewrite -(size_negB sb1) in Hnge0.
        generalize Hgt1; rewrite to_Zpos_ltB_eqn (to_Zpos_from_Zpos_1 H') Z.ltb_lt Z.one_succ.
        move/Z.lt_succ_l => Hgt0.
        rewrite -(to_Zpos_zeros (size sb2)) in Hgt0; move : Hgt0; rewrite -to_Zpos_ltB; move => Hgt0.
        generalize Hgt0; rewrite ltB_zeros_l ltB0n; move => Hz2f.
        move : (udivB_small_iff Hszn12 Hnge0 Hgt0).
        case Hlt12 : (-# sb1 <# sb2).
        * move => [_ Hudiv]. rewrite (eqP (Hudiv isT)).
          have Hdz : (dropmsb (udivB (-# sb1) sb2).1 == zeros (size (udivB (-#sb1) sb2).1 - 1))
            by rewrite (eqP (Hudiv isT)) dropmsb_zeros subn1 size_zeros.
          rewrite (eqP (negB_zeros _)) to_Z_zeros.
          rewrite -(Z.opp_involutive (to_Z sb1)) Z.quot_opp_l;
            last exact: (neq_zeros_to_Z_neq0 Hz2f).
          rewrite (to_Z_to_Zpos sb1) -Z.add_opp_r Z.add_comm -Z.opp_sub_distr Hm1 Z.mul_1_l Z.opp_involutive.
          generalize Hlt12; rewrite to_Zpos_ltB_eqn Z.ltb_lt.
          rewrite -sub0B (to_Zpos_subB (size_zeros (size sb1))).
          rewrite -(ltB_equiv_borrow_subB (size_zeros (size sb1))).
          rewrite to_Zpos_zeros Z.add_0_r size_zeros.
          rewrite (neq_zeros_to_Z_gt0 (negbT Hz1)).
          generalize Hngt0.
          rewrite -sub0B (to_Zpos_subB (size_zeros (size sb1))) to_Zpos_zeros Z.add_0_r size_zeros.
          rewrite -(ltB_equiv_borrow_subB (size_zeros (size sb1))) (neq_zeros_to_Z_gt0 (negbT Hz1)).
          rewrite Z.mul_1_l high1_0_to_Z; last by rewrite high1_msb Hm2.
          move => Hgt0s Hlt12'.
          rewrite Z.quot_small; first done.
          split;
            [exact :(Z.lt_le_incl _ _ Hgt0s)|done].
        * rewrite -(Bool.negb_involutive ((udivB (-# sb1) sb2).1 == zeros (size (-#sb1)))).
          move => [Hudiv _]. move : (contraT Hudiv) => {Hudiv} Hudiv.
          have Hszdiv : (0 < size (udivB (-# sb1) sb2).1) by rewrite size_udivB size_negB H.
          move : (zeros_msb_dropmsb (udivB (-# sb1) sb2).1). rewrite size_udivB (negbTE Hudiv) Hmu/=.
          move => Hdnz; symmetry in Hdnz; rewrite -(size_udivB (-# sb1) sb2) in Hdnz.
          move : (msb_negB (negbT Hdnz)); rewrite Hmu/=.
          move => Hmnu; symmetry in Hmnu.
          rewrite to_Z_to_Zpos Hmnu Z.mul_1_l -sub0B to_Zpos_subB;
            last by rewrite size_zeros size_udivB.
          rewrite -ltB_equiv_borrow_subB; last by rewrite size_zeros size_udivB.
          rewrite -(size_udivB (-# sb1) sb2) in Hudiv.
          rewrite (neq_zeros_to_Z_gt0 Hudiv) Z.mul_1_l to_Zpos_zeros Z.add_0_r.
          rewrite size_subB size_zeros minnn size_udivB -Z.sub_add_distr Z.add_comm.
          rewrite Z.sub_add_distr Z.sub_diag Z.sub_0_l -{1}(revK (-# sb1)).
          rewrite (to_Zpos_udivB _ (Hz2f)); last by rewrite size_rev size_negB.
          rewrite revK.
          rewrite -(Z.opp_involutive (to_Z sb1)) Z.quot_opp_l; last exact: (neq_zeros_to_Z_neq0 (Hz2f)).
          rewrite (to_Z_to_Zpos sb1) Z.opp_sub_distr Z.add_comm Z.add_opp_r Hm1 Z.mul_1_l.
          rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
          rewrite -sub0B (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
          rewrite (neq_zeros_to_Z_gt0 (negbT Hz1)) Z.mul_1_l to_Zpos_zeros Z.add_0_r size_zeros.
          move : (to_Zpos_bounded sb1); rewrite -Z.lt_0_sub; move=> Hltbd.
          rewrite Z.quot_div_nonneg;
            [done|exact : (Z.lt_le_incl _ _ Hltbd)
             |move : (neq_zeros_to_Z_gt0 (Hz2f)); by rewrite to_Zpos_ltB to_Zpos_zeros].
      + move : Hgt1. rewrite ltBNle; last by rewrite size_from_Zpos.
        rewrite Bool.negb_false_iff.
        rewrite to_Zpos_leB_eqn; last by rewrite size_from_Zpos.
        rewrite Z.leb_le . move/Zle_lt_or_eq => [Hlt|Heq].
        rewrite (to_Zpos_from_Zpos_1 H') in Hlt.
        move : (neq_zeros_to_Z_gt0 H2).
        rewrite to_Zpos_ltB to_Zpos_zeros. by auto with zarith.
        have Haux : (size (sb2) = size (from_Zpos (size (sb2)) 1)) by rewrite size_from_Zpos.
        move : (to_Zpos_inj_ss Haux Heq) => {Haux} Heqn.
        rewrite Heqn -H0.
        rewrite -{1}(size_negB sb1) (udivB1 (Hnz1 isT))/= negB_involutive.
        have Hm2' : msb (from_Zpos (size sb1) 1) = b0 by rewrite H0 -Heqn Hm2.
        rewrite (to_Z_to_Zpos (from_Zpos (size sb1) 1)) Hm2' Z.mul_0_l Z.sub_0_r (to_Zpos_from_Zpos_1 H).
        by rewrite Z.quot_1_r.
    - rewrite (negbTE H1) in Hz1.
      move/iffRL/contra: (negB_zeros' sb2) => Hnz2; rewrite H2 in Hnz2.
      rewrite/absB Hm1 Hm2.
      have Hszn12 : size (-# sb2) = size (sb1) by rewrite size_negB H0.
      case Hgt1 : (from_Zpos (size (-# sb2)) 1 <# (-# sb2)).
      + symmetry in Hszn12.
        move : (udivB_lt Hszn12 (negbT Hz1) Hgt1) => Hdivlt.
        move : (msb_ltB (size_udivB sb1 (-# sb2)) Hm1 Hdivlt) => Hmu.
        move : (neq_zeros_to_Z_gt0 (negbT Hz1)). rewrite to_Zpos_ltB to_Zpos_zeros.
        move => Hgt0.
        move : (Z.lt_le_incl _ _ Hgt0).
        rewrite -{1}(to_Zpos_zeros (size sb1)) -to_Zpos_leB; last by rewrite size_zeros.
        move => Hge0.
        move : (neq_zeros_to_Z_gt0 (Hnz2 isT)) => Hngt0.
        move : (udivB_small_iff Hszn12 Hge0 Hngt0).
        case Hlt12 : (sb1 <# -# sb2).
        * move => [_ Hudiv]. rewrite (eqP (Hudiv isT)).
          have Hdz : (dropmsb (udivB sb1 (-# sb2)).1 == zeros (size (udivB sb1 (-#sb2)).1 - 1))
            by rewrite (eqP (Hudiv isT)) dropmsb_zeros subn1 size_zeros.
          rewrite (eqP (negB_zeros (size sb1))) to_Z_zeros.
          rewrite -(Z.opp_involutive (to_Z sb2)) Z.quot_opp_r;
            last (rewrite -Z_nonzero_opp; exact: (neq_zeros_to_Z_neq0 H2)).
          rewrite (to_Z_to_Zpos sb2) -Z.add_opp_r Z.add_comm -Z.opp_sub_distr Hm2 Z.mul_1_l Z.opp_involutive.
          generalize Hlt12; rewrite to_Zpos_ltB_eqn Z.ltb_lt.
          rewrite -sub0B (to_Zpos_subB (size_zeros (size sb2))).
          rewrite -(ltB_equiv_borrow_subB (size_zeros (size sb2))).
          rewrite to_Zpos_zeros Z.add_0_r size_zeros.
          generalize Hngt0; rewrite to_Zpos_ltB to_Zpos_zeros -{1}(sub0B sb2).
          rewrite (to_Zpos_subB (size_zeros (size sb2))) to_Zpos_zeros Z.add_0_r size_zeros.
          rewrite -(ltB_equiv_borrow_subB (size_zeros (size sb2))).
          rewrite (neq_zeros_to_Z_gt0 H2) Z.mul_1_l high1_0_to_Z; last by rewrite high1_msb Hm1.
          move => Hgt0s Hlt12'.
          rewrite Z.quot_small; first done.
          split;
            [apply to_Zpos_ge0|done].
        * rewrite -(Bool.negb_involutive ((udivB sb1 (-# sb2)).1 == zeros (size sb1))).
          move => [Hudiv _]. move : (contraT Hudiv) => {Hudiv} Hudiv.
          have Hszdiv : (0 < size (udivB sb1 (-# sb2)).1) by rewrite size_udivB H.
          move : (zeros_msb_dropmsb (udivB sb1 (-# sb2)).1). rewrite size_udivB (negbTE Hudiv) Hmu/=.
          move => Hdnz; symmetry in Hdnz; rewrite -(size_udivB sb1 (-# sb2)) in Hdnz.
          move : (msb_negB (negbT Hdnz)); rewrite Hmu/=.
          move => Hmnu; symmetry in Hmnu.
          rewrite to_Z_to_Zpos Hmnu Z.mul_1_l -sub0B to_Zpos_subB;
            last by rewrite size_zeros size_udivB.
          rewrite -ltB_equiv_borrow_subB; last by rewrite size_zeros size_udivB.
          rewrite -(size_udivB sb1 (-# sb2)) in Hudiv.
          rewrite (neq_zeros_to_Z_gt0 Hudiv) Z.mul_1_l to_Zpos_zeros Z.add_0_r.
          rewrite size_subB size_zeros minnn size_udivB -Z.sub_add_distr Z.add_comm.
          rewrite Z.sub_add_distr Z.sub_diag Z.sub_0_l -{1}(revK (sb1)).
          rewrite (to_Zpos_udivB _ (Hnz2 isT)); last by rewrite size_rev size_negB.
          rewrite revK.
          rewrite -(Z.opp_involutive (to_Z sb2)) Z.quot_opp_r; last (move: (neq_zeros_to_Z_neq0 H2); by rewrite Z_nonzero_opp).
          rewrite (to_Z_to_Zpos sb2) -Z.add_opp_r Z.add_comm -Z.opp_sub_distr Hm2 Z.mul_1_l Z.opp_involutive.
          rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
          rewrite -sub0B (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
          rewrite (neq_zeros_to_Z_gt0 H2) Z.mul_1_l to_Zpos_zeros Z.add_0_r size_zeros.
          move : (to_Zpos_bounded sb2); rewrite -Z.lt_0_sub; move=> Hltbd.
          rewrite Z.quot_div_nonneg; [done|apply to_Zpos_ge0|done].
      + move : Hgt1. rewrite ltBNle; last by rewrite size_negB size_from_Zpos.
        rewrite Bool.negb_false_iff.
        rewrite to_Zpos_leB_eqn; last by rewrite size_negB size_from_Zpos.
        rewrite Z.leb_le . move/Zle_lt_or_eq => [Hlt|Heq].
        rewrite to_Zpos_from_Zpos_1 in Hlt; last by rewrite size_negB H'.
        move : (neq_zeros_to_Z_gt0 (Hnz2 isT)).
        rewrite to_Zpos_ltB to_Zpos_zeros. by auto with zarith.
        have Haux : (size (-# sb2) = size (from_Zpos (size (-# sb2)) 1)) by rewrite size_negB size_from_Zpos.
        move : (to_Zpos_inj_ss Haux Heq) => {Haux} Heqn.
        rewrite Heqn size_negB -H0.
        rewrite (udivB1 (negbT Hz1))/=.
        rewrite -(Z.opp_involutive (to_Z sb2)) Z.quot_opp_r;
          last by (move : (neq_zeros_to_Z_neq0 H2); rewrite Z_nonzero_opp).
        rewrite -(negB_involutive sb2) Heqn size_negB.
        rewrite (to_Z_negB_from_Zpos1 H') Z.opp_involutive Z.quot_1_r.
        have Hmn1 : msb (-# sb1) = true by rewrite -(msb_negB H1) Bool.negb_true_iff Hm1.
        rewrite to_Z_to_Zpos Hmn1 Z.mul_1_l -sub0B (to_Zpos_subB (size_zeros _)).
        rewrite -(ltB_equiv_borrow_subB (size_zeros _)) (neq_zeros_to_Z_gt0 (negbT Hz1)).
        rewrite to_Zpos_zeros Z.mul_1_l Z.add_0_r size_subB size_zeros minnn.
        rewrite -Z.sub_add_distr Z.add_comm Z.sub_add_distr Z.sub_diag Z.sub_0_l.
          by rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
  Qed.

  Lemma sdivB_negB_negB bs1 bs2 :
    0 < size bs1 -> size bs1 = size bs2 ->
    ~~(dropmsb bs1 == zeros (size bs1 - 1))->
    ~~(dropmsb bs2 == zeros (size bs2 - 1))->
    (msb bs1 == msb bs2) ->
    (sdivB (negB bs1) (negB bs2)) = (sdivB bs1 bs2).
  Proof.
    intros. apply to_Z_inj_ss; first by rewrite !size_sdivB size_negB.
    have Hn1 : 0 < size (-# bs1) by rewrite size_negB H.
    have Hn2 : 0 < size (-# bs2) by rewrite size_negB -H0 H.
    have H' : 0 < size bs2 by rewrite -H0 H.
    have Hn12 : size (-# bs1) = size (-#bs2) by rewrite !size_negB H0.
    move : (zeros_msb_dropmsb bs1); rewrite (negbTE H1) andbF; move => Hz1.
    move : (zeros_msb_dropmsb bs2); rewrite (negbTE H2) andbF; move => Hz2.
    move/iffRL/contra : (negB_zeros' bs1) => Hnz1; rewrite Hz1 in Hnz1.
    move/iffRL/contra : (negB_zeros' bs2) => Hnz2; rewrite Hz2 in Hnz2.
    move : H3; case Hm1 : (msb bs1); case Hm2 : (msb bs2); move => //=_.
    - move : (msb_negB H1); rewrite Hm1/=; move=> Hmn1; symmetry in Hmn1.
      move : (msb_negB H2); rewrite Hm2/=; move=> Hmn2; symmetry in Hmn2.
      move : (dropmsb_negB_nonzeros H1) => Hdz1. move : (dropmsb_negB_nonzeros H2) => Hdz2.
      rewrite -(size_negB bs1) in Hdz1; rewrite -(size_negB bs2) in Hdz2.
      rewrite (to_Z_sdivB_same_msb Hn1 Hn12 Hdz1 (Hnz2 isT)); last by rewrite Hmn1 Hmn2.
      rewrite (to_Z_sdivB_same_msb H H0 H1 (negbT Hz2)); last by rewrite Hm1 Hm2.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hmn1.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hmn2.
      rewrite -sub0B (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
      rewrite (neq_zeros_to_Z_gt0 (negbT Hz1)) Z.mul_1_l to_Zpos_zeros Z.add_0_r.
      rewrite -sub0B (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
      rewrite (neq_zeros_to_Z_gt0 (negbT Hz2)) Z.mul_1_l to_Zpos_zeros Z.add_0_r.
      rewrite !size_zeros 2!to_Z_to_Zpos Hm1 Hm2 !Z.mul_1_l.
      move : (to_Zpos_bounded bs1); rewrite -Z.lt_0_sub ; move => Hlts1.
      move : (to_Zpos_bounded bs2); rewrite -Z.lt_0_sub ; move => Hlts2.
      symmetry.
      rewrite -2!Z.add_opp_r Z.add_comm -Z.opp_sub_distr. rewrite Z.add_comm -Z.opp_sub_distr.
      by rewrite Z.quot_opp_opp; last by move/Z.lt_neq/Z.neq_sym : Hlts2.
    - move : (msb_negB H1); rewrite Hm1/=; move=> Hmn1; symmetry in Hmn1.
      move : (msb_negB H2); rewrite Hm2/=; move=> Hmn2; symmetry in Hmn2.
      move : (dropmsb_negB_nonzeros H1) => Hdz1. move : (dropmsb_negB_nonzeros H2) => Hdz2.
      rewrite -(size_negB bs1) in Hdz1; rewrite -(size_negB bs2) in Hdz2.
      rewrite (to_Z_sdivB_same_msb Hn1 Hn12 Hdz1 (Hnz2 isT)); last by rewrite Hmn1  Hmn2.
      rewrite (to_Z_sdivB_same_msb H H0 H1 (negbT Hz2)); last by rewrite Hm1 Hm2.
      symmetry.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
      rewrite 2!to_Z_to_Zpos Hmn1 Hmn2.
      rewrite -sub0B (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
      rewrite (neq_zeros_to_Z_gt0 (negbT Hz1)) Z.mul_1_l to_Zpos_zeros Z.add_0_r.
      rewrite -sub0B (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
      rewrite (neq_zeros_to_Z_gt0 (negbT Hz2)) Z.mul_1_l to_Zpos_zeros Z.add_0_r.
      rewrite !size_subB !size_zeros !minnn !Z.mul_1_l.
      rewrite -2!Z.sub_add_distr Z.add_comm Z.sub_add_distr. rewrite Z.add_comm Z.sub_add_distr.
      rewrite 2!Z.sub_diag 2!Z.sub_0_l.
      move : (to_Zpos_bounded bs1); rewrite -Z.lt_0_sub ; move => Hlts1.
      move : (to_Zpos_bounded bs2); rewrite -Z.lt_0_sub ; move => Hlts2.
      symmetry.
      by rewrite Z.quot_opp_opp;
        last (move : (neq_zeros_to_Z_neq0 (negbT Hz2)); (rewrite high1_0_to_Z; last by rewrite high1_msb Hm2)).
  Qed.

  Lemma sdiv0B bs :
    ~~ (bs == zeros (size bs)) ->
    (sdivB (zeros (size bs)) bs) = zeros (size bs).
  Proof.
    intros.
    move/iffRL/contra : (negB_zeros' bs) => Hnz; rewrite H in Hnz.
    rewrite/sdivB/absB msb_zeros/=.
    case (msb bs); rewrite /=udiv0B; try done;
      try (by rewrite (eqP (negB_zeros (size bs))) ||by rewrite size_negB); try by apply Hnz.
  Qed.

  Lemma sdivB0_msb1 bs :
    1 < size bs ->
    msb bs ->
    (sdivB bs (zeros (size bs))) = from_Zpos (size bs) 1.
  Proof.
    intros. move : (ltn_sub2r H H); rewrite subnn; move => H1.
    rewrite /sdivB/absB H0 msb_zeros.
    rewrite udivB0 -(eqP (negB1_ones_zpos _)) negB_involutive size_negB//.
  Qed.

  Lemma sdivB0_msb0 bs :
    1 < size bs ->
    ~~ (msb bs) ->
    (sdivB bs (zeros (size bs))) = ones (size bs).
  Proof.
    intros. move : (ltn_sub2r H H); rewrite subnn; move => H1.
    rewrite /sdivB/absB (negbTE H0) msb_zeros udivB0//.
  Qed.

  Lemma sdivB_same bs : 1 < size bs -> ~~(bs == zeros (size bs)) -> sdivB bs bs = from_Zpos (size bs) 1.
  Proof.
    intros. rewrite /sdivB/absB eq_refl /=.
    move : (ltn_sub2r H H) => H'; rewrite subnn in H'.
    move/iffRL/contra : (negB_zeros' bs); rewrite H0; move => Hng.
    move : (zeros_msb_dropmsb bs); rewrite (negbTE H0).
    case Hdz : (dropmsb bs == zeros (size bs - 1)); case Hdo : (dropmsb bs == ones (size bs - 1));
      case Hm' : (msb bs);
      try rewrite (eqP Hdz) -(ltn_predK H') -zeros_cons -ones_cons eqseq_cons// in Hdo;
      try rewrite (udivB_same (Hng isT)) size_negB//;
          try rewrite (udivB_same H0)//.
  Qed.

  (* Semantics of signed division *)

  Lemma to_Z_sdivB_full bs1 bs2 :
    1 < size bs1 -> size bs1 = size bs2 ->
    (negb (andb (msb bs1 && (dropmsb bs1 == (zeros (size bs1 - 1)))) (bs2 == ones (size bs2)))) ->
    ~~(bs2 == zeros (size bs2)) ->
    to_Z (sdivB bs1 bs2) = Z.quot (to_Z bs1) (to_Z bs2).
  Proof.
    intros.
    have H' : 1 < size bs2 by rewrite -H0 .
    have Hn2 : ~~ (-# bs2 == zeros (size (-# bs2))).
    {
      apply contraFneq with (bs2 == zeros (size bs2)). move/eqP => Haux; rewrite negB_zeros'//.
      rewrite (negbTE H2)//.
    }
    move : H1 ;
      case Hd1 : (dropmsb bs1 == zeros (size bs1 - 1));
      case His1 : (bs2 == ones (size bs2)); move => //=;try (move => _;
      case Hm : (msb bs1 == msb bs2);
        [rewrite (to_Z_sdivB_same_msb (ltnW H) H0 (negbT Hd1) H2 Hm)//
        |rewrite (to_Z_sdivB_diff_msb (ltnW H) H0 (negbT Hd1) H2 (negbT Hm))//]).
    - rewrite !andbT. case Hm12 : (msb bs1 == msb bs2).
      + rewrite /sdivB Hm12/=. move/negbTE => Hm1.
        rewrite /absB -(eqP Hm12) Hm1.
        move : (zeros_msb_dropmsb bs1); rewrite Hm1/= Hd1; move => Hz1.
        rewrite (eqP Hz1) (udiv0B H0 H2) to_Z_zeros.
        case H02: (Z.eqb 0 (to_Z bs2))%Z;
          [rewrite ->Z.eqb_eq in H02; by rewrite -H02 /Z.quot /=
          |rewrite ->Z.eqb_neq in H02; by rewrite (Z.quot_0_l _ (Z.neq_sym _ _ H02))].
      + rewrite /sdivB Hm12/=. move/negbTE => Hm1.
        rewrite /absB Hm1. rewrite Hm1 eq_sym in Hm12. move : Hm12. case (msb bs2) => //_.
        rewrite -{1 2}(joinmsb_splitmsb (ltnW H)) -/(dropmsb _) -/(msb _) (eqP Hd1) Hm1 /joinmsb zeros_rcons.
        rewrite to_Z_zeros.
        rewrite (Z.quot_0_l _ (neq_zeros_to_Z_neq0 H2)) subn1 (ltn_predK (ltnW H)) udiv0B//.
        rewrite (eqP (negB_zeros _)) to_Z_zeros//. rewrite size_negB//.
    - case Hm : (msb bs1 == msb bs2).
      + rewrite /sdivB /absB andbF => _; rewrite Hm (dropmsb_0_negB_id Hd1).
        case Hd2 : (dropmsb bs2 == zeros (size bs2 - 1)).
        * rewrite (dropmsb_0_negB_id Hd2).
          have -> : bs1 = bs2.
          {
            rewrite -(joinmsb_splitmsb (ltnW H)) -(joinmsb_splitmsb (ltnW H')) -!/(msb _) -!/(dropmsb _).
            rewrite (eqP Hd1) (eqP Hd2) -(eqP Hm) H0//.
          }
          rewrite (Z.quot_same _ (neq_zeros_to_Z_neq0 H2))/=.
          by (case (msb bs2); rewrite udivB_same// to_Z_from_Zpos_1).
        * have Hgt1 : (from_Zpos (size (-#bs2)) 1 <# -#bs2).
          {
            apply leB_neq_ltB.
            generalize H'; rewrite -(size_negB bs2) => /ltnW H''.
            rewrite to_Zpos_leB;
              [rewrite (to_Zpos_from_Zpos_1 H'') Z.one_succ; by apply Zlt_le_succ, neq_zeros_to_Zpos_gt0
              |rewrite size_from_Zpos size_negB//].
            rewrite eq_sym size_negB. apply neq_ones_negB. exact : (negbT His1).
          }
          have H0' : (size bs1 = size (-# bs2)) by rewrite size_negB.
          move : (zeros_msb_dropmsb bs1); rewrite Hd1 (eqP Hm); case Hm2 : (msb bs2); rewrite /= => Hn01.
          {
            move : (udivB_lt H0' (negbT Hn01) Hgt1).
            rewrite -{2}(joinmsb_splitmsb (ltnW H)) -/(dropmsb _) (eqP Hd1) -/(msb _) (eqP Hm) Hm2.
            rewrite -(size_udivB bs1 (-#bs2)). rewrite ->msb_ltB_aux => Hmdiv.
            rewrite to_Z_to_Zpos Hmdiv Z.mul_0_l Z.sub_0_r to_Zpos_udivB'// (Z.quot_div _ _ (neq_zeros_to_Z_neq0 H2)).
            rewrite (to_Z_sgn_msb (negbT Hn01)) (to_Z_sgn_msb H2) (eqP Hm) Hm2.
            rewrite -!high1_1_to_Zpos_negB; [|rewrite high1_msb Hm2//| rewrite high1_msb (eqP Hm) Hm2//].
            rewrite (dropmsb_0_negB_id Hd1) -Z.mul_shuffle0 -Z.opp_eq_mul_m1 Z.mul_comm -Z.opp_eq_mul_m1 Z.opp_involutive//.
          }
          {
            rewrite (eqP Hn01) udiv0B// to_Z_zeros (Z.quot_0_l _ (neq_zeros_to_Z_neq0 H2))//.
          }
      + have H0' : (size bs1 = size (-# bs2)) by rewrite size_negB.
        rewrite /sdivB /absB andbF => _; rewrite Hm (dropmsb_0_negB_id Hd1).
        move : Hm;
          case Hm1 : (msb bs1);
          case Hm2 : (msb bs2);
          rewrite // -(joinmsb_splitmsb (ltnW H)) -/(msb _) -/(dropmsb _) (eqP Hd1) Hm1;
          [|rewrite /joinmsb zeros_rcons subn1 (ltn_predK (ltnW H)) udiv0B// (eqP (negB_zeros _)) to_Z_zeros (Z.quot_0_l _ (neq_zeros_to_Z_neq0 H2))//].
        generalize H2; rewrite zeros_msb_dropmsb Hm2; case Hd2 : (dropmsb bs2 == zeros (size bs2 - 1)); rewrite // =>_ _.
        case H21 : (bs2 == from_Zpos (size bs2) 1).
        * rewrite (eqP H21) -H0 -{2}(subnK (ltnW H)) -{2}(size_zeros (size bs1 - 1)) -(size_joinmsb (zeros (size bs1 - 1)) b1).
          rewrite udivB1; last rewrite size_joinmsb addn1 -zeros_rcons eqseq_rcons andbF//.
          rewrite to_Z_from_Zpos_1// Z.quot_1_r dropmsb_0_negB_id// dropmsb_joinmsb size_joinmsb size_zeros addnK//.
        * have Hgt1 : (from_Zpos (size bs2) 1 <# bs2).
          {
            apply leB_neq_ltB.
            generalize H'; rewrite -(size_negB bs2) => /ltnW H''.
            rewrite to_Zpos_leB;
              [rewrite (to_Zpos_from_Zpos_1 H'') Z.one_succ; by apply Zlt_le_succ, neq_zeros_to_Zpos_gt0
              |rewrite size_from_Zpos size_negB//].
            rewrite eq_sym. exact : (negbT H21).
          }
          have Hn01 : ~~(joinmsb (zeros (size bs1 - 1)) true == zeros (size (joinmsb (zeros (size bs1 - 1)) true))).
          { rewrite size_joinmsb addn1 -zeros_rcons size_zeros eqseq_rcons andbF//. }
          generalize H0; rewrite -{1}(joinmsb_splitmsb (ltnW H)) -/(msb _) -/(dropmsb _) (eqP Hd1) Hm1 => H12.
          move : (udivB_lt H12 Hn01 Hgt1).
          rewrite {2}H0 -H12 -(size_udivB (joinmsb (zeros (size bs1 - 1)) true) bs2) (msb_ltB_aux) => Hmudiv.
          have Hgt12 : ~~ (joinmsb (zeros (size bs1 - 1)) true <# bs2).
          {
            rewrite -(joinmsb_splitmsb (ltnW H')) -/(msb _) Hm2 ltB_rcons_ss; last rewrite size_zeros size_splitmsb H0//.
            rewrite orFb andbF//.
          }
          have Hudivn0 : ~~((udivB (joinmsb (zeros (size bs1 - 1)) true) bs2).1 == zeros (size ((udivB (joinmsb (zeros (size bs1 - 1)) true) bs2).1))).
          {
            have Haux : (zeros (size (joinmsb (zeros (size bs1 - 1)) true)) <=# joinmsb (zeros (size bs1 - 1)) true).
            apply ltB_leB_incl. rewrite size_joinmsb addn1 -zeros_rcons ltB_rcons_ss size_zeros//.
            move : (contra_neqN (iffLR (udivB_small_iff H12 Haux (neq_zeros_to_Z_gt0 H2)))).
            rewrite (negbTE Hgt12) size_udivB/= => {Haux} Haux; by apply Haux.
          }
          move : (zeros_msb_dropmsb (udivB (joinmsb (zeros (size bs1 - 1)) true) bs2).1).
          rewrite Hmudiv andTb (negbTE Hudivn0) => Hdudivn0; symmetry in Hdudivn0; move/negbT: Hdudivn0=> Hdudivn0.
          rewrite msb0_to_Z_negB// to_Zpos_udivB'// (Z.quot_div _ _ (neq_zeros_to_Z_neq0 H2)).
          rewrite -(Z.sgn_abs (to_Z bs2)) (to_Z_sgn_msb H2) Hm2.
          rewrite (to_Z_sgn_msb Hn01) msb_joinmsb !Z.mul_1_r Z.mul_comm -Z.opp_eq_mul_m1 -high1_1_to_Zpos_negB; last rewrite high1_msb msb_joinmsb//.
          rewrite dropmsb_0_negB_id; last rewrite dropmsb_joinmsb size_joinmsb size_zeros addnK//.
          rewrite high1_0_to_Z// high1_msb Hm2//.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of signed remainder
  ---------------------------------------------------------------------------*)

  Definition sremB bs1' bs2' : bits :=
    let bs1 := absB bs1' in
    let bs2 := absB bs2' in
    if (msb bs1')
    then negB (udivB bs1 bs2).2
    else (udivB bs1 bs2).2.

  Definition sremB' bs1 bs2 := (sdivB' bs1 bs2).2.

  Lemma sremB_is_sremB' bs1 bs2 :
    sremB bs1 bs2 = sremB' bs1 bs2.
  Proof.
    rewrite /sremB' /sdivB' /sremB.
      by (case Hdz1 : (dropmsb bs1 == zeros (size bs1 - 1));
          case Hdz2 : (dropmsb bs2 == ones (size bs2 - 1)) ;
          case Hm12 : (msb bs1 == msb bs2); case Hm1 : (msb bs1)).
  Qed.

  Lemma size_sremB bs1 bs2 : size (sremB bs1 bs2) = size bs1.
  Proof.
    rewrite /sremB /sdivB.
    case: (msb bs1) => /=.
    - rewrite size_negB size_uremB size_absB//.
    - rewrite size_uremB size_absB//.
  Qed.

  Lemma size_sremB' bs1 bs2 : size (sremB' bs1 bs2) = size bs1.
  Proof.
    rewrite /sremB' /sdivB'.
    case: ((msb bs1 == msb bs2) && ~~ msb bs1) => /=.
    - rewrite size_uremB size_absB. reflexivity.
    - case: ((msb bs1 == msb bs2) && msb bs1) => /=.
      + rewrite size_negB size_uremB size_absB. reflexivity.
      + case: (~~ (msb bs1 == msb bs2) && ~~ msb bs1) => /=.
        * rewrite size_uremB size_absB. reflexivity.
        * rewrite size_negB size_uremB size_absB. reflexivity.
  Qed.

  Lemma uremB_le bs1 bs2 : size bs1 = size bs2 -> ~~ (bs2 == zeros (size bs2)) -> uremB bs1 bs2 <=# bs1.
  Proof.
    intros. rewrite /uremB (to_Zpos_leB (size_uremB bs1 bs2)) (to_Zpos_uremB' _ H0); last done.
    apply (Z.mod_le _ _ (@to_Zpos_ge0 bs1)).
    rewrite -ltB0n -(ltB_zeros_l (size bs2)) in H0; rewrite ->to_Zpos_ltB in H0; rewrite to_Zpos_zeros// in H0.
  Qed.

  Lemma uremB_lt bs1 bs2 : size bs1 = size bs2 -> ~~ (bs2 == zeros (size bs2))
                           -> bs2 <=# bs1 -> uremB bs1 bs2 <# bs1.
  Proof.
    intros.
    have Haux : (zeros (size bs1) <=# bs1).
    { rewrite (to_Zpos_leB (size_zeros _)) to_Zpos_zeros; apply to_Zpos_ge0. }
    generalize H0; rewrite -ltB0n -(ltB_zeros_l (size bs2)); move => Hltb0.
    move/iffLR/contra : (uremB_small_iff H Haux Hltb0) => Hsmall.
    rewrite leBNlt in H1; last done. move : (Hsmall H1) => Hneq.
    move : (uremB_le H H0) => Hle. by rewrite (leB_neq_ltB Hle Hneq).
  Qed.

  Lemma uremB0' : forall bs1 bs2, size bs1 = size bs2 -> bs2 == zeros (size bs2) -> (udivB bs1 bs2).2 = bs1.
  Proof.
    move => bs1 bs2 Hsz. move/eqP => Heq; by rewrite Heq udivB0.
  Qed.

  Lemma absB_zeros n : absB (zeros n) = zeros n.
  Proof.
      by rewrite /absB msb_zeros.
  Qed.

  Lemma to_Z_sremB sb1 sb2 :
    0 < size sb1 -> size sb1 = size sb2 ->
    ~~(dropmsb sb1 == zeros (size sb1 - 1))->
    to_Z (sremB sb1 sb2) = Z.rem (to_Z sb1) (to_Z sb2).
  Proof.
    intros.
    rewrite /sremB.
    have H' : 0 < size sb2 by rewrite -H0.
    move : (zeros_msb_dropmsb sb1).
    rewrite (negbTE H1) !andbF; move => Hz1.
    move : (neq_zeros_to_Z_neq0 (negbT Hz1)) => Hz1z.
    case Hz2 : (sb2 == zeros (size sb2));
      first (rewrite (eqP Hz2) absB_zeros -H0 -(size_absB sb1) udivB0 to_Z_zeros /absB /Z.rem/Z.quotrem/=; case (msb sb1); [rewrite negB_involutive; by case Htz1: (to_Z sb1)|by case Htz1 : (to_Z sb1)]).
    case Hm1 : (msb sb1); case Hm2 : (msb sb2); move => //= .
    - move/iffRL/contra : (negB_zeros' sb1); rewrite Hz1; move => Hnz1.
      move/iffRL/contra : (negB_zeros' sb2); rewrite Hz2; move => Hnz2.
      move : (absB_neq0 (negbT Hz1)) => Hanz1. rewrite -{1}(size_absB sb1) in Hanz1.
      move : (absB_neq0 (negbT Hz2)) => Hanz2. rewrite -{1}(size_absB sb2) in Hanz2.
      have Hszabs : size (absB sb1) = size (absB sb2) by rewrite !size_absB H0.
      rewrite (Z.rem_eq _ _ (neq_zeros_to_Z_neq0 (negbT Hz2))).
      have H'' : 0< size (absB sb1) by rewrite size_absB.
      rewrite -/(uremB (absB sb1) (absB sb2)) (uremB_eq H'' Hszabs Hanz2).
      rewrite /absB Hm1 Hm2.
      have Hm12 : msb sb1 == msb sb2 by rewrite Hm1 Hm2.
      move : (msb_negB H1); rewrite Hm1/=; move => Hmn1; symmetry in Hmn1.
      rewrite to_Z_to_Zpos.
      case Heq : (-# sb1 == ((udivB (-# sb1) (-# sb2)).1 *# -# sb2)).
      + rewrite {1 3}(eqP Heq) subB_same.
        rewrite (eqP (negB_zeros _)) to_Zpos_zeros msb_zeros Z.mul_0_l/=.
        move/eqP : Heq => Heq. move : (f_equal negB Heq).
        rewrite negB_involutive; move => Heq'.
        rewrite {1}Heq'.
        have Hmm : (msb (-# ((udivB (-# sb1) (-# sb2)).1 *# -# sb2)) = b1) by rewrite -Heq'.
        rewrite to_Z_to_Zpos Hmm Z.mul_1_l -sub0B.
        rewrite to_Zpos_subB; last by rewrite size_mulB size_zeros.
        rewrite -ltB_equiv_borrow_subB; last by rewrite size_mulB size_zeros.
        have Hszu : (0 < size  ((udivB (-# sb1) (-# sb2)).1 *# -# sb2)) by rewrite size_mulB size_udivB size_negB H.
        rewrite -Heq (neq_zeros_to_Z_gt0 (Hnz1 isT)) Z.mul_1_l size_subB size_zeros minnn.
        rewrite to_Zpos_zeros Z.add_0_r.
        rewrite -2!Z.sub_add_distr Z.add_comm 2!Z.sub_add_distr Z.sub_diag Z.sub_0_l.
        have Hszn1 : 0 < size (negB sb1) by rewrite size_negB H.
        have Hszn12 : size (negB sb1) = size ( negB sb2) by rewrite !size_negB H0.
        rewrite Heq to_Zpos_mulB; [|by rewrite size_udivB !size_negB H0|exact : (mulB_udivB_Numulo Hszn12)].
        rewrite -{1}(revK (-#sb1)) (to_Zpos_udivB _ (Hnz2 isT)); last by rewrite size_rev !size_negB -H0.
        rewrite revK !to_Z_to_Zpos -!sub0B !(to_Zpos_subB (size_zeros _)) -!(ltB_equiv_borrow_subB (size_zeros _)).
        rewrite Hm1 Hm2 (neq_zeros_to_Z_gt0 (negbT Hz2)) (neq_zeros_to_Z_gt0 (negbT Hz1)).
        rewrite !Z.mul_1_l !to_Zpos_zeros !Z.add_0_r !size_zeros.
        rewrite Z.mul_comm -Z.add_opp_r. rewrite -!Z.add_opp_r.
        rewrite (Z.add_comm (to_Zpos sb1)  (- 2 ^ Z.of_nat (size sb1))).
        rewrite (Z.add_comm (to_Zpos sb2)  (- 2 ^ Z.of_nat (size sb2))).
        move : (to_Zpos_bounded sb1); rewrite -Z.lt_0_sub; move => Hlt1.
        move : (to_Zpos_bounded sb2); rewrite -Z.lt_0_sub; move => Hlt2.
        rewrite -!Z.opp_sub_distr Z.quot_opp_opp; last by auto with zarith.
        rewrite Z.quot_div_nonneg; [| by auto with zarith | by auto with zarith ].
        rewrite Z.mul_opp_r !Z.add_opp_r. by auto with zarith.
      + have Hszn1 : 0 < size (negB sb1) by rewrite size_negB H.
        have Hszn12 : size (negB sb1) = size ( negB sb2) by rewrite !size_negB H0.
        move : (mulB_udivB_leB Hszn12) => Hle.
        move/negbT : Heq; rewrite eq_sym; move => Heq.
        move : (leB_neq_ltB Hle Heq) => Hlt.
        rewrite -sub0B.
        rewrite (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
        have Hszaux : size ((udivB (-# sb1) (-# sb2)).1 *# -# sb2)= size (-# sb1).
        by rewrite size_mulB size_udivB !size_negB.
        move : ((ltB_subB_nonzero Hszaux Hlt)).
        have {1}->: (size ((udivB (-# sb1) (-# sb2)).1 *# -# sb2) = size (-# sb1 -# ((udivB (-# sb1) (-# sb2)).1 *# -# sb2))).
          by rewrite size_subB size_mulB size_udivB minnn.
        move => Hneq0.
        rewrite sub0B (neq_zeros_to_Z_gt0 Hneq0) Z.mul_1_l.
        move : (msb_ltB Hszaux Hmn1 Hlt) => Hmmul.
        have Hmaux : (msb ((udivB (-# sb1) (-# sb2)).1 *# -# sb2) == msb (-# sb1)) by rewrite Hmn1 Hmmul.
        move : (ltB_dropmsb_subB_nonzero Hszaux Hmaux Hlt).
        have -> : (size ((udivB (-# sb1) (-# sb2)).1 *# -# sb2)) = size (-# sb1 -# ((udivB (-# sb1) (-# sb2)).1 *# -# sb2)).
        by rewrite size_subB size_mulB size_udivB minnn.
        move => Hdnz.
        rewrite -(msb_negB Hdnz) (ltB_msb_subB Hszaux Hmaux Hlt) Z.mul_1_l.
        rewrite to_Zpos_zeros Z.add_0_r size_zeros !size_negB !size_subB size_mulB size_udivB minnn size_negB.
        rewrite to_Zpos_subB; last by rewrite size_mulB size_udivB .
        rewrite -ltB_equiv_borrow_subB; last by rewrite size_mulB size_udivB .
        rewrite ltBNle; last by rewrite size_mulB size_udivB.
        rewrite Hle Z.mul_0_l Z.add_0_l.
        rewrite to_Zpos_mulB; [| by rewrite size_udivB !size_negB|apply (mulB_udivB_Numulo Hszn12)].
        have -> : (2 ^ Z.of_nat (size sb1) -
                       (to_Zpos (-# sb1) - to_Zpos (udivB (-# sb1) (-# sb2)).1 * to_Zpos (-# sb2)) -
                       2 ^ Z.of_nat (size sb1))%Z
                  = (- (to_Zpos (-# sb1) - to_Zpos (udivB (-# sb1) (-# sb2)).1 * to_Zpos (-# sb2)))%Z
          by auto with zarith.
        rewrite -{2}(revK (-# sb1)) (to_Zpos_udivB _ (Hnz2 isT)); last by rewrite size_rev !size_negB H0.
        rewrite revK !to_Z_to_Zpos Hm1 Hm2 !Z.mul_1_l.
        rewrite -sub0B (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
        rewrite (neq_zeros_to_Z_gt0 (negbT Hz1)) Z.mul_1_l to_Zpos_zeros Z.add_0_r.
        rewrite -sub0B (to_Zpos_subB (size_zeros _)) -(ltB_equiv_borrow_subB (size_zeros _)).
        rewrite (neq_zeros_to_Z_gt0 (negbT Hz2)) Z.mul_1_l to_Zpos_zeros Z.add_0_r.
        rewrite !size_zeros.
        have -> :(to_Zpos sb1 - 2 ^ Z.of_nat (size sb1) = - (2 ^ Z.of_nat (size sb1) - to_Zpos sb1))%Z
          by auto with zarith.
        have -> :(to_Zpos sb2 - 2 ^ Z.of_nat (size sb2) = - (2 ^ Z.of_nat (size sb2) - to_Zpos sb2))%Z
          by auto with zarith.
        move: (to_Zpos_bounded sb1); rewrite -Z.lt_0_sub; move => Hneq1.
        move: (to_Zpos_bounded sb2); rewrite -Z.lt_0_sub; move => Hneq2.
        rewrite Z.quot_opp_opp; last by auto with zarith.
        rewrite Z.mul_opp_l Z.sub_opp_r Z.quot_div_nonneg; [| by auto with zarith | by auto with zarith].
          by rewrite -Z.opp_sub_distr Z.mul_comm.
    - rewrite /absB Hm1 Hm2.
      move/iffRL/contra : (negB_zeros' sb1); rewrite Hz1; move => Hnz1.
      move : (neq_zeros_to_Z_neq0 (negbT Hz1)) => Hneq01.
      have Hsz12 : size (-# sb1) = size sb2 by rewrite size_negB.
      have Hsz1 : 0< size (-# sb1) by rewrite size_negB.
      move : (uremB_eq Hsz1 Hsz12 (negbT Hz2)) => Hurem.
      rewrite /uremB in Hurem.
      rewrite Hurem.
      have Hszaux : size ((udivB (-# sb1) (sb2)).1 *# sb2)= size (-# sb1).
        by rewrite size_mulB size_udivB !size_negB.
      move : (mulB_udivB_leB Hsz12) => Hlediv.
      move : (msb_negB H1); rewrite Hm1/=; move => Hnm1; symmetry in Hnm1.
      move : (msb_leB Hszaux Hnm1 Hlediv) => Hmnu.
      have Hmeq: msb ((udivB (-# sb1) sb2).1 *# sb2) ==  msb (-# sb1) by rewrite Hnm1 Hmnu.
      move : (leB_msb_subB Hszaux Hmeq Hlediv) => Hmsu.
      case Heq0: (sb1 == (-#((udivB (-# sb1) sb2).1 *# sb2))).
      + have Heq0' : ((-# sb1 == ((udivB (-# sb1) sb2).1 *# sb2))) by rewrite {1}(eqP Heq0) negB_involutive.
        rewrite {1}(eqP Heq0') subB_same (eqP (negB_zeros _)) to_Z_zeros.
        rewrite (Z.rem_eq _ _ (neq_zeros_to_Z_neq0 (negbT Hz2))).
        rewrite {1}to_Z_to_Zpos Hm1 Z.mul_1_l {1}(eqP Heq0).
        rewrite neq_zeros_to_Zpos_negB; last by rewrite -(eqP Heq0') Hnz1.
        rewrite size_mulB size_udivB size_negB.
        rewrite (to_Zpos_mulB _ (mulB_udivB_Numulo Hsz12)) ; last by rewrite size_udivB Hsz12.
        rewrite (to_Zpos_udivB' _ (negbT Hz2)); last done.
        rewrite -{4}(negB_involutive sb1) (msb0_to_Z_negB Hnm1).
        move : (neq_zeros_to_Z_neq0 (negbT Hz2)) => Hneq0.
        rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
        generalize Hneq0; rewrite {1}to_Z_to_Zpos Hm2/= Z.sub_0_r; move => Hneq0'.
        rewrite (Z.quot_opp_l _ _ Hneq0') Z.mul_opp_r Z.mul_comm.
        rewrite Z.quot_div_nonneg;
          [by auto with zarith |apply to_Zpos_ge0
           |move : (neq_zeros_to_Z_gt0 (negbT Hz2)); by rewrite to_Zpos_ltB to_Zpos_zeros].
      + rewrite eq_sym in Heq0.
        case Heq0' : (((udivB (-# sb1) sb2).1 *# sb2 == -# sb1)).
        by rewrite (eqP Heq0') negB_involutive eq_refl in Heq0.
        move : (leB_neq_ltB Hlediv (negbT Heq0')) => Hltdiv.
        move : (ltB_subB_nonzero Hszaux Hltdiv) => Hsneq.
        rewrite Hszaux in Hsneq.
        move : (zeros_msb_dropmsb (-# sb1 -# ((udivB (-# sb1) sb2).1 *# sb2))); rewrite Hmsu size_subB Hszaux minnn (negbTE Hsneq)/=.
        move => Hdsneq; symmetry in Hdsneq.
        rewrite (msb0_to_Z_negB Hmsu). symmetry in Hszaux.
        rewrite (to_Zpos_subB Hszaux) -(ltB_equiv_borrow_subB Hszaux) (ltBNle Hszaux).
        move : (neq_zeros_to_Z_neq0 (negbT Hz2)) => Hneq0z.
        rewrite Hlediv/= (to_Zpos_mulB _ (mulB_udivB_Numulo Hsz12)); last by rewrite size_udivB Hsz12.
        rewrite (to_Zpos_udivB' _ (negbT Hz2)); last done.
        rewrite -{3}(negB_involutive sb1) (msb0_to_Z_negB Hnm1).
        rewrite (Z.rem_eq _ _ Hneq0z) (Z.quot_opp_l _ _ Hneq0z).
        rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
        rewrite Z.mul_opp_r Z.opp_sub_distr Z.mul_comm.
        rewrite Z.quot_div_nonneg;
          [by auto with zarith |apply to_Zpos_ge0
           |move : (neq_zeros_to_Z_gt0 (negbT Hz2)); by rewrite to_Zpos_ltB to_Zpos_zeros].
    - rewrite /absB Hm1 Hm2.
      move/iffRL/contra : (negB_zeros' sb1); rewrite Hz1; move => Hnz1.
      move/iffRL/contra : (negB_zeros' sb2); rewrite Hz2; move => Hnz2.
      have Hsz12 : size (sb1) = size (-#sb2) by rewrite size_negB.
      move : (uremB_eq H Hsz12 (Hnz2 isT)) => Hurem.
      rewrite /uremB in Hurem.
      rewrite Hurem.
      have Hszaux : size ((udivB sb1 (-# sb2)).1 *# -#sb2)= size (sb1).
        by rewrite size_mulB size_udivB.
      move : (mulB_udivB_leB Hsz12) => Hlediv.
      move : (msb_negB H1); rewrite Hm1/=; move => Hnm1; symmetry in Hnm1.
      move : (msb_leB Hszaux Hm1 Hlediv) => Hmnu.
      have Hmeq: msb ((udivB (sb1) (-#sb2)).1 *# -#sb2) ==  msb (sb1) by rewrite Hm1 Hmnu.
      move : (leB_msb_subB Hszaux Hmeq Hlediv) => Hmsu.
      case Heq0: (sb1 == (((udivB (sb1) (-#sb2)).1 *# -#sb2))).
      + rewrite {1}(eqP Heq0) subB_same to_Z_zeros.
        rewrite (Z.rem_mod _ _ (neq_zeros_to_Z_neq0 (negbT Hz2))) (to_Z_sgn_msb (negbT Hz1)) Hm1 Z.mul_1_l.
        rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
        move/iffRL : (Z.abs_eq_iff (to_Zpos sb1)) => Habs1. move : (Habs1 (@to_Zpos_ge0 sb1)) => {Habs1}Habs1; rewrite Habs1.
        rewrite -high1_1_to_Zpos_negB; last by rewrite high1_msb Hm2.
        rewrite (Z.mod_eq _ _ (neq_zeros_to_Zpos_neq0 (Hnz2 isT))).
        rewrite {1}(eqP Heq0) (to_Zpos_mulB _ (mulB_udivB_Numulo Hsz12)); last by rewrite size_udivB Hsz12.
        rewrite (to_Zpos_udivB' _ (Hnz2 isT)); last done.
        by rewrite Z.mul_comm Z.sub_diag.
      + rewrite eq_sym in Heq0.
        move : (leB_neq_ltB Hlediv (negbT Heq0)) => Hltdiv.
        move : (ltB_subB_nonzero Hszaux Hltdiv) => Hsneq; rewrite Hszaux in Hsneq.
        rewrite high1_0_to_Z; last by rewrite high1_msb Hmsu.
        symmetry in Hszaux; rewrite (to_Zpos_subB Hszaux) -(ltB_equiv_borrow_subB Hszaux) (ltBNle Hszaux) Hlediv.
        rewrite (to_Zpos_mulB _ (mulB_udivB_Numulo Hsz12)); last by rewrite size_udivB Hsz12.
        move : (neq_zeros_to_Z_neq0 (negbT Hz2)) => Hneq0z. move : (neq_zeros_to_Zpos_neq0 (Hnz2 isT)) => Hneqnz2.
        rewrite /=Z.mul_comm (to_Zpos_udivB' _ (Hnz2 isT)); last done.
        rewrite (Z.rem_eq _ _ Hneq0z) high1_0_to_Z; last by rewrite high1_msb Hm1.
        move/iffLR : (msb1_to_Z_lt0 sb2); rewrite Hm2; move => Hlt0.
        rewrite -(Z.abs_sgn (to_Z sb2)) (Z.sgn_neg _ (Hlt0 isT)) -Z.opp_eq_mul_m1 -high1_1_to_Zpos_negB; last by rewrite high1_msb Hm2.
        rewrite Z.quot_opp_r; last by auto with zarith. move : (@to_Zpos_ge0 sb1) => Hge0.
        rewrite Z.mul_opp_opp Z.quot_div_nonneg; [by auto with zarith | by auto with zarith |].
        move : (neq_zeros_to_Z_gt0 (Hnz2 isT)); by rewrite to_Zpos_ltB to_Zpos_zeros.
    - rewrite /absB Hm1 Hm2.
      rewrite -/(uremB sb1 sb2) (uremB_eq H H0 (negbT Hz2)).
      move : (mulB_udivB_leB H0) => Hle.
      case His1 : (((udivB sb1 sb2).1 *# sb2) == sb1).
      rewrite (eqP His1) subB_same to_Z_zeros.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
      rewrite -(eqP His1) (to_Zpos_mulB _ (mulB_udivB_Numulo _ )); [|by rewrite size_udivB H0|by rewrite H0].
      rewrite -{1}(revK sb1) (to_Zpos_udivB _ (negbT Hz2)); last by rewrite size_rev H0.
      by rewrite revK Z.rem_mul;
        last (move : (neq_zeros_to_Z_gt0 (negbT Hz2)); rewrite to_Zpos_ltB to_Zpos_zeros; by auto with zarith).
      move : (leB_neq_ltB Hle (negbT His1)) => Hlt.
      have Hsz : size ((udivB sb1 sb2).1 *# sb2) = size sb1 by rewrite size_mulB size_udivB.
      move : (msb_ltB Hsz Hm1 Hlt) => Hmu.
      have Hm12 : msb ((udivB sb1 sb2).1 *# sb2) == msb sb1 by rewrite Hmu Hm1.
      move : (ltB_msb_subB Hsz Hm12 Hlt) => Hms0.
      rewrite high1_0_to_Z ; last by rewrite high1_msb Hms0.
      rewrite to_Zpos_subB; last by rewrite size_mulB size_udivB.
      rewrite -(ltB_equiv_borrow_subB); last by rewrite size_mulB size_udivB.
      rewrite ltBNle; last by rewrite size_mulB size_udivB.
      rewrite Hle Z.mul_0_l Z.add_0_l to_Zpos_mulB; [|by rewrite size_udivB|exact :(mulB_udivB_Numulo H0)].
      rewrite -{2}(revK sb1) (to_Zpos_udivB _ (negbT Hz2)); last by  rewrite size_rev.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm1.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hm2.
      rewrite Z.rem_eq; last (move : (neq_zeros_to_Z_gt0 (negbT Hz2)); rewrite to_Zpos_ltB to_Zpos_zeros; by auto with zarith).
      rewrite Z.mul_comm revK Z.quot_div_nonneg; [reflexivity | by apply to_Zpos_ge0 |].
      move : (neq_zeros_to_Z_gt0 (negbT Hz2)); rewrite to_Zpos_ltB to_Zpos_zeros; by apply.
  Qed.

  Lemma mulB_udivB_gt0 bs1 bs2 :
    size bs1 = size bs2 ->
    zeros (size bs1) <# bs1 -> zeros (size bs2) <# bs2 ->
    bs2 <=# bs1 -> zeros (size bs1) <# (udivB bs1 bs2).1 *# bs2.
  Proof.
    move=> Hsz Hbs1 Hbs2 Hle. rewrite to_Zpos_ltB to_Zpos_zeros.
    rewrite (to_Zpos_mulB _ (mulB_udivB_Numulo Hsz)); last by rewrite size_udivB.
    rewrite to_Zpos_udivB' ?Hsz ?neq_zeros_gt0 //=.
    move: Hbs1 Hbs2 Hle. symmetry in Hsz.
    rewrite !to_Zpos_ltB !to_Zpos_zeros (to_Zpos_leB Hsz) => Hbs1 Hbs2 Hle.
    apply Z.mul_pos_pos; last exact: Hbs2.
    apply Z.div_str_pos. by split.
  Qed.

  Lemma to_Z_sremB_full bs1 bs2 : 1 < size bs1 -> size bs1 = size bs2 ->
                                  to_Z (sremB bs1 bs2) = Z.rem (to_Z bs1) (to_Z bs2).
  Proof.
    intros. generalize H; rewrite H0; move => H'.
    move : (joinmsb_splitmsb (ltnW H));  move : (joinmsb_splitmsb (ltnW H')).
    move : (zeros_msb_dropmsb bs1); move : (zeros_msb_dropmsb bs2).
    rewrite -/(msb bs1) -/(dropmsb bs1) -/(msb bs2) -/(dropmsb bs2).
    case Hd1 : (dropmsb bs1 == zeros (size bs1 - 1));
      first (case Hm1 : (msb bs1); case Hm2 : (msb bs2)); rewrite /=; move => Hz2 Hz1.
    - move => H2 H1; rewrite /sremB /absB Hm1 Hm2/=.
      move/iffRL/contra : (negB_zeros' bs2); rewrite Hz2; move => Hnz2.
      case Hones2 : (dropmsb bs2 == ones (size bs2 - 1)); rewrite (dropmsb_0_negB_id Hd1)/=.
      + rewrite (eqP Hones2) /joinmsb ones_rcons subn1 (ltn_predK (ltnW H')) in H2.
        move : (f_equal negB H2); rewrite -(eqP (negB1_ones_zpos (size bs2))) negB_involutive; move => Hn2.
        rewrite -Hn2 -H0 (udivB1 (negbT Hz1)) (eqP (negB_zeros _)) to_Z_zeros -(Z.abs_sgn (to_Z bs2)) Z.sgn_neg;
          last by (rewrite <-msb1_to_Z_lt0; rewrite Hm2).
        rewrite -Z.opp_eq_mul_m1 -high1_1_to_Zpos_negB; last by rewrite high1_msb Hm2.
        move : (f_equal to_Zpos Hn2); rewrite (to_Zpos_from_Zpos_1 (ltnW H')).
        move => {Hn2} Hn2.
        by rewrite (Z.rem_opp_r _ _ (neq_zeros_to_Zpos_neq0 (Hnz2 isT))) -Hn2 Z.rem_1_r.
      + have Hszn :  size (dropmsb (-# bs2)) = size (dropmsb bs1) by rewrite !size_dropmsb size_negB H0.
        have Hsz : size bs1 = size (-# bs2) by rewrite size_negB.
        move : (uremB_le Hsz (Hnz2 isT)) => Hle.
        case Hd2 : (dropmsb bs2 == zeros (size bs2 - 1)).
        * have H12 : bs1 = bs2 .
          {
            rewrite -(joinmsb_splitmsb (ltnW H)) -(joinmsb_splitmsb (ltnW H')) -/(dropmsb bs1) -/(dropmsb bs2) (eqP Hd1) (eqP Hd2) -/(msb bs1) -/(msb bs2) Hm1 Hm2 H0//.
          }
          rewrite (dropmsb_0_negB_id Hd2) H12 (udivB_same (negbT Hz2)) (eqP (negB_zeros _)) (Z.rem_same _ (neq_zeros_to_Z_neq0 (negbT Hz2))) to_Z_zeros//.
        * move : (msb_negB (negbT Hd2)); rewrite Hm2/=; move => Hmn2; symmetry in Hmn2; symmetry in Hszn.
          move : (ltB_rcons_ss (msb bs1) (msb (-#bs2)) Hszn); rewrite {2 3}Hm1 {2 3}Hmn2/= andbF -/joinmsb.
          rewrite !joinmsb_splitmsb; [|rewrite size_negB (ltnW H')//|rewrite (ltnW H)//]; move => H12.
          rewrite -/(uremB bs1 (-#bs2)) (uremB_eq (ltnW H) Hsz (Hnz2 isT)).
          case Hcond : (bs1 == ((udivB bs1 (-# bs2)).1 *# -# bs2)).
          rewrite -(eqP Hcond) subB_same (eqP (negB_zeros _)) to_Z_zeros (Z.rem_mod _ _ (neq_zeros_to_Z_neq0 (negbT Hz2))).
          rewrite -high1_1_to_Zpos_negB; last by rewrite high1_msb Hm1.
          rewrite -high1_1_to_Zpos_negB; last by rewrite high1_msb Hm2.
          move/iffLR : (msb1_to_Z_lt0 bs1) => Haux; move : (Haux Hm1). rewrite -Z.sgn_neg_iff; move => {Haux} Haux.
          rewrite (dropmsb_0_negB_id Hd1) Haux Z.mul_opp_l Z.mul_1_l (Z.mod_eq _ _ (neq_zeros_to_Zpos_neq0 (Hnz2 isT))).
          rewrite {1}(eqP Hcond) (to_Zpos_mulB _ (mulB_udivB_Numulo Hsz)); last rewrite size_udivB//.
          rewrite (to_Zpos_udivB' _ (Hnz2 isT)); last done.
          by rewrite Z.mul_comm Z.sub_diag.
          rewrite eq_sym in Hcond.
          move : (leB_neq_ltB (mulB_udivB_leB Hsz) (negbT Hcond)) => Hltdiv.
          have Hszsub : size (bs1 -# ((udivB bs1 (-# bs2)).1 *# -# bs2)) = size bs1.
          {
            rewrite size_subB size_mulB size_udivB minnn//.
          }
          have Hszmul : size ((udivB bs1 (-# bs2)).1 *# -# bs2) = size bs1 by rewrite size_mulB size_udivB.
          have Hmsub : msb (bs1 -# ((udivB bs1 (-# bs2)).1 *# -# bs2)) = b0.
          symmetry in Hszmul.
          generalize H12; rewrite (ltBNle Hsz). move => H21; apply negbFE in H21.
          move : (mulB_udivB_gt0 Hsz (neq_zeros_to_Z_gt0 (negbT Hz1)) (neq_zeros_to_Z_gt0 (Hnz2 isT)) H21); rewrite Hszmul; move => Hmdgt0.
          move : (ltB_subBr Hszmul Hmdgt0 (ltB_leB_incl Hltdiv)); rewrite -{3}H1 (eqP Hd1).
          move => Hlt10. move/iffLR : (msb_ltB_aux (bs1 -# ((udivB bs1 (-# bs2)).1 *# -# bs2))).
          rewrite Hszsub; move => Hmsbsub; exact : (Hmsbsub Hlt10).
          move : (ltB_subB_nonzero Hszmul Hltdiv).
          move : (zeros_msb_dropmsb (bs1 -# ((udivB bs1 (-# bs2)).1 *# -# bs2))).
          rewrite Hszmul; move => Hsubd Hsubz.
          rewrite Hszsub (negbTE Hsubz) Hmsub /= -Hszsub in Hsubd; symmetry in Hsubd.
          move : (msb_negB (negbT Hsubd)); rewrite Hmsub/=; move => Hmnsub.
          rewrite (high1_0_to_Z_negB _); last by rewrite high1_msb Hmsub.
          symmetry in Hszmul.
          rewrite (to_Zpos_subB Hszmul) -(ltB_equiv_borrow_subB Hszmul) (ltBNle Hszmul) (ltB_leB_incl Hltdiv)/=.
          rewrite (to_Zpos_mulB _ (mulB_udivB_Numulo Hsz)); last rewrite size_udivB Hsz//.
          rewrite (to_Zpos_udivB' _ (Hnz2 isT)); last done.
          rewrite (Z.rem_mod _ _ (neq_zeros_to_Z_neq0 (negbT Hz2))).
          rewrite high1_1_to_Zpos_negB; last by rewrite high1_msb Hm2.
          move/iffLR : (msb1_to_Z_lt0 bs1) => Haux; move : (Haux Hm1) => {Haux}Haux.
          rewrite (Z.sgn_neg _ Haux); symmetry; rewrite Z.mul_comm -Z.opp_eq_mul_m1.
          rewrite -high1_1_to_Zpos_negB; last by rewrite high1_msb Hm1.
          move : (neq_zeros_to_Z_neq0 (negbT Hz2)); rewrite -Z.abs_pos; move/Z.lt_neq/Z.neq_sym =>{Haux}Haux.
          rewrite (dropmsb_0_negB_id Hd1) (Z.mod_eq _ _ Haux) Z.mul_comm//.
    - move => H2 H1.
      rewrite /sremB /absB Hm1 Hm2.
      case Hd2 : (dropmsb bs2 == zeros (size bs2 - 1)); rewrite Hd2 in Hz2.
      + rewrite (eqP Hz2) -H0 udivB0 to_Z_zeros negB_involutive /Z.rem /Z.quotrem; by case (to_Z bs1).
      + rewrite (dropmsb_0_negB_id Hd1) -/(uremB bs1 bs2) (uremB_eq (ltnW H) H0 (negbT Hz2)).
        * case Hcond : (bs1 == ((udivB bs1 bs2).1 *# bs2)).
          rewrite -(eqP Hcond) subB_same (eqP (negB_zeros _)) to_Z_zeros (Z.rem_mod _ _ (neq_zeros_to_Z_neq0 (negbT Hz2))).
          rewrite -high1_1_to_Zpos_negB; last by rewrite high1_msb Hm1.
          move/iffLR : (msb1_to_Z_lt0 bs1) => Haux; move : (Haux Hm1). rewrite -Z.sgn_neg_iff; move => {Haux} Haux.
          rewrite (dropmsb_0_negB_id Hd1) Haux Z.mul_opp_l Z.mul_1_l high1_0_to_Z; last by rewrite high1_msb Hm2.
          move : (@to_Zpos_ge0 bs2); rewrite <-Z.abs_eq_iff; move => Habs.
          rewrite Habs (Z.mod_eq _ _ (neq_zeros_to_Zpos_neq0 (negbT Hz2))).
          rewrite {1}(eqP Hcond) (to_Zpos_mulB _ (mulB_udivB_Numulo H0)); last rewrite size_udivB//.
          rewrite (to_Zpos_udivB' _ (negbT Hz2)); last done.
          by rewrite Z.mul_comm Z.sub_diag.
        * rewrite eq_sym in Hcond.
          move : (leB_neq_ltB (mulB_udivB_leB H0) (negbT Hcond)) => Hltdiv.
          have Hszsub : size (bs1 -# ((udivB bs1 bs2).1 *# bs2)) = size bs1.
          {
            rewrite size_subB size_mulB size_udivB minnn//.
          }
          have Hszmul : size ((udivB bs1 bs2).1 *# bs2) = size bs1 by rewrite size_mulB size_udivB.
          have Hmsub : msb (bs1 -# ((udivB bs1 bs2).1 *# bs2)) = b0.
          generalize Hm2; move => Hm2'. rewrite <-(msb_ltB_aux) in Hm2'. rewrite -H0 -(eqP Hd1) H1 in Hm2'.
          move : (mulB_udivB_gt0 H0 (neq_zeros_to_Z_gt0 (negbT Hz1)) (neq_zeros_to_Z_gt0 (negbT Hz2)) (ltB_leB_incl Hm2')); rewrite -Hszmul; move => Hmdgt0.
          symmetry in  Hszmul.
          move : (ltB_subBr Hszmul Hmdgt0 (ltB_leB_incl Hltdiv)); rewrite -{3}H1 (eqP Hd1).
          move => Hlt10. move/iffLR : (msb_ltB_aux (bs1 -# ((udivB bs1 (bs2)).1 *# bs2))).
          rewrite Hszsub; move => Hmsbsub; exact : (Hmsbsub Hlt10).
          move : (ltB_subB_nonzero Hszmul Hltdiv).
          move : (zeros_msb_dropmsb (bs1 -# ((udivB bs1 bs2).1 *# bs2))).
          rewrite Hszmul; move => Hsubd Hsubz.
          rewrite Hszsub (negbTE Hsubz) Hmsub /= -Hszsub in Hsubd; symmetry in Hsubd.
          move : (msb_negB (negbT Hsubd)); rewrite Hmsub/=; move => Hmnsub.
          rewrite (high1_0_to_Z_negB _); last by rewrite high1_msb Hmsub.
          symmetry in Hszmul.
          rewrite (to_Zpos_subB Hszmul) -(ltB_equiv_borrow_subB Hszmul) (ltBNle Hszmul) (ltB_leB_incl Hltdiv)/=.
          rewrite (to_Zpos_mulB _ (mulB_udivB_Numulo H0)); last rewrite size_udivB H0//.
          rewrite (to_Zpos_udivB' _ (negbT Hz2)); last done.
          rewrite (Z.rem_mod _ _ (neq_zeros_to_Z_neq0 (negbT Hz2))).
          rewrite -high1_1_to_Zpos_negB; last by rewrite high1_msb Hm1.
          move/iffLR : (msb1_to_Z_lt0 bs1) => Haux; move : (Haux Hm1) => {Haux}Haux.
          rewrite (Z.sgn_neg _ Haux); symmetry; rewrite Z.mul_comm -Z.opp_eq_mul_m1.
          rewrite (dropmsb_0_negB_id Hd1) high1_0_to_Z; last by rewrite high1_msb Hm2.
          move/iffRL : (Z.abs_eq_iff (to_Zpos bs2)) => {Haux}Haux; rewrite (Haux (@to_Zpos_ge0 bs2)).
          rewrite (Z.mod_eq _ _ (neq_zeros_to_Zpos_neq0 (negbT Hz2))) Z.mul_comm//.
    - move => H2 H1. rewrite (eqP Hz1) /sremB msb_zeros absB_zeros/=.
      move/iffRL/contra : (negB_zeros' bs2) => Hnz2; rewrite Hz2 in Hnz2.
      rewrite {1}H0 -{1}(size_absB bs2) udiv0B /absB Hm2; [|done|by apply Hnz2].
      rewrite !to_Z_zeros (Z.rem_0_l _ (neq_zeros_to_Z_neq0 (negbT Hz2)))//.
    - move => H2 H1. rewrite (eqP Hz1) /sremB msb_zeros absB_zeros/= -/(uremB _ _).
      rewrite {1}H0 -{1}(size_absB bs2) urem0B /absB Hm2; last done.
      rewrite !to_Z_zeros /Z.rem//.
    - move => _ _. rewrite /sremB' (to_Z_sremB (ltnW H) H0 (negbT Hd1))//.
  Qed.

  (*---------------------------------------------------------------------------
    Properties of signed modulo
  ---------------------------------------------------------------------------*)

  Definition smodB bs1 bs2 : bits :=
  let r_sdiv := sremB bs1 bs2 in
  if (msb bs1 == msb bs2) || (r_sdiv == (zeros (size r_sdiv)))
  then
    r_sdiv
  else addB r_sdiv bs2.

  Definition smodB' bs1 bs2 : bits :=
  let r_sdiv := sremB' bs1 bs2 in
  if (msb bs1 == msb bs2) || (r_sdiv == (zeros (size r_sdiv)))
  then
    r_sdiv
  else addB r_sdiv bs2.

  Lemma smodB_is_smodB' bs1 bs2 :
    smodB bs1 bs2 = smodB' bs1 bs2.
  Proof.
    rewrite /smodB /smodB' . rewrite sremB_is_sremB'//.
  Qed.

  Lemma size_smodB bs1 bs2 :
    size (smodB bs1 bs2) =
    if (msb bs1 == msb bs2) || is_zero (sremB bs1 bs2)
    then size bs1
    else minn (size (sremB bs1 bs2)) (size bs2).
  Proof.
    rewrite /smodB.
    case H: ((msb bs1 == msb bs2) ||
             ((sremB bs1 bs2) == zeros (size (sremB bs1 bs2)))).
    - case/orP: H => H.
      + rewrite H /=. rewrite size_sremB. reflexivity.
      + rewrite (eqP H) /=. rewrite zeros_is_zero orbT /=.
        rewrite size_zeros size_sremB. reflexivity.
    - move/Bool.orb_false_iff: H => [H1 H2]. rewrite H1 /=.
      have ->: is_zero (sremB bs1 bs2) = false.
      { apply/negP=> H3. move/negP: H2. apply. rewrite {1}(is_zero_zeros H3).
        exact: eqxx. }
      rewrite size_addB. reflexivity.
  Qed.

  Lemma size_smodB_ss bs1 bs2 :
    size bs1 = size bs2 -> size (smodB bs1 bs2) = size bs1.
  Proof.
    move=> Hs. rewrite size_smodB.
    case: ((msb bs1 == msb bs2) || is_zero (sremB bs1 bs2)).
    - reflexivity.
    - rewrite size_sremB Hs minnn. reflexivity.
  Qed.

  (*---------------------------------------------------------------------------
    Others
  ---------------------------------------------------------------------------*)
  Lemma to_nat_not_zero (q : bits) : (q == zeros (size q))=false -> (to_nat q == 0)=false.
  Proof.
    intro. apply negbT in H; rewrite -ltB0n to_nat_ltB/= in H.
    apply/eqP. rewrite-(prednK H). apply Nat.neq_succ_0.
  Qed.

  (*---------------------------------------------------------------------------
    Lemmas used in coq-cryptoline
  ---------------------------------------------------------------------------*)
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

  Lemma bv2z_cshl_unsigned' bsh bsl n :
    size bsh = size bsl ->
    n <= size bsl ->
    high n (bsl ++ bsh) == zeros n ->
    (to_Zpos (low (size bsl) ((bsl ++ bsh) <<# n) >># n)%bits +
     to_Zpos (high (size bsh) ((bsl ++ bsh) <<# n)%bits) *
     2 ^ Z.of_nat (size bsl - n))%Z =
    (to_Zpos bsh * 2 ^ Z.of_nat (size bsl) + to_Zpos bsl)%Z.
  Proof.
    move=> Hs Hn Hzeros.
    apply: (proj1
              (Z.mul_cancel_r
                 (to_Zpos (low (size bsl) ((bsl ++ bsh) <<# n) >># n) +
                  to_Zpos (high (size bsh) ((bsl ++ bsh) <<# n)) *
                  2 ^ Z.of_nat (size bsl - n))%Z
                 (to_Zpos bsh * 2 ^ Z.of_nat (size bsl) + to_Zpos bsl)%Z
                 (2 ^ Z.of_nat n)%Z (@pow2_nat2z_nonzero n))).
    rewrite Z.mul_add_distr_r. rewrite -Z.mul_assoc.
    rewrite -(Z.pow_add_r _ _ _ (Nat2Z.is_nonneg _) (Nat2Z.is_nonneg _)).
    rewrite -Nat2Z.inj_add. replace (size bsl - n + n)%coq_nat with
                                (size bsl - n + n)%N by reflexivity.
    rewrite (subnK Hn). exact: (bv2z_cshl_unsigned Hs Hzeros).
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

  Lemma bv2z_cshl_signed' bsh bsl n :
    size bsh = size bsl ->
    n <= size bsl ->
    (high (n + 1) (bsl ++ bsh) == zeros (n + 1))
    || (high (n + 1) (bsl ++ bsh) == ones (n + 1)) ->
    (to_Zpos (low (size bsl) ((bsl ++ bsh) <<# n) >># n)%bits +
     to_Z (high (size bsh) ((bsl ++ bsh) <<# n)%bits) *
     2 ^ Z.of_nat (size bsl - n))%Z =
    (to_Z bsh * 2 ^ Z.of_nat (size bsl) + to_Zpos bsl)%Z.
  Proof.
    move=> Hs Hn Hzeros.
    apply: (proj1
              (Z.mul_cancel_r
                 (to_Zpos (low (size bsl) ((bsl ++ bsh) <<# n) >># n) +
                  to_Z (high (size bsh) ((bsl ++ bsh) <<# n)) *
                  2 ^ Z.of_nat (size bsl - n))%Z
                 (to_Z bsh * 2 ^ Z.of_nat (size bsl) + to_Zpos bsl)%Z
                 (2 ^ Z.of_nat n)%Z (@pow2_nat2z_nonzero n))).
    rewrite Z.mul_add_distr_r. rewrite -Z.mul_assoc.
    rewrite -(Z.pow_add_r _ _ _ (Nat2Z.is_nonneg _) (Nat2Z.is_nonneg _)).
    rewrite -Nat2Z.inj_add. replace (size bsl - n + n)%coq_nat with
                                (size bsl - n + n)%N by reflexivity.
    rewrite (subnK Hn). exact: (bv2z_cshl_signed Hs Hzeros).
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
      rewrite ?Z.mul_0_l ?Z.mul_1_l ?Z.sub_0_r //=; by auto with zarith.
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

  Lemma to_Z_adcB_ex bs1 bs2 (c : bool) :
    size bs1 = size bs2 ->
    exists d,
      (c + to_Z bs1 + to_Z bs2)%Z =
        (d * Z.pow 2 (Z.of_nat (size bs1)) + to_Z (adcB c bs1 bs2).2)%Z.
  Proof.
    move=> Hs12. rewrite !to_Z_to_Zpos. rewrite size_adcB Hs12 minnn.
    replace (c + (to_Zpos bs1 - msb bs1 * 2 ^ Z.of_nat (size bs2)) +
               (to_Zpos bs2 - msb bs2 * 2 ^ Z.of_nat (size bs2)))%Z
      with (c + to_Zpos bs1 + to_Zpos bs2 -
              msb bs1 * 2 ^ Z.of_nat (size bs2) - msb bs2 * 2 ^ Z.of_nat (size bs2))%Z by ring.
    rewrite -(to_Zpos_adcB _ Hs12). rewrite Hs12.
    exists ((adcB c bs1 bs2).1 - msb bs1 - msb bs2 + msb (adcB c bs1 bs2).2)%Z. ring.
  Qed.

  Lemma to_Z_addB_ex bs1 bs2 :
    size bs1 = size bs2 ->
    exists d,
      (to_Z bs1 + to_Z bs2)%Z =
        (d * Z.pow 2 (Z.of_nat (size bs1)) + to_Z (addB bs1 bs2))%Z.
  Proof.
    move=> Hs12. rewrite /addB. move: (to_Z_adcB_ex false Hs12) => [d H].
    exists d. rewrite -H. replace (Z.b2z false)%Z with 0%Z by reflexivity.
    rewrite Z.add_0_l. reflexivity.
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
      rewrite ?Z.mul_0_l ?Z.mul_1_l ?Z.sub_0_r //=; by auto with zarith.
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
    by auto with zarith.
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
    by auto with zarith.
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
      by auto with zarith.
  Qed.

  Lemma bv2z_sbbs_signed bs1 bs2 bsc :
    1 < size bs1 ->
    size bs1 = size bs2 -> size bsc = 1 ->
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (bs1 -# bs2)%bits (zext (size bs1 - 1) bsc) ->
    to_Z (sbbB (to_bool bsc) bs1 bs2).2 = (to_Z bs1 - to_Z bs2 - to_Zpos bsc)%Z.
  Proof.
    exact: bv2z_sbb_signed.
  Qed.

  Lemma to_Z_sbc_ex bs1 bs2 (c : bool) :
    0 < size bs1 ->
    size bs1 = size bs2 ->
    exists d,
      (to_Z bs1 - to_Z bs2 - (1 - c))%Z =
        (d * Z.pow 2 (Z.of_nat (size bs1)) + to_Z (adcB c bs1 (~~# bs2)%bits).2)%Z.
  Proof.
    move=> Hs1 Hs12. have Hs: (size bs1 = size (~~# bs2)) by rewrite size_invB.
    move: (to_Z_adcB_ex c Hs) => [d H].
    rewrite (Z.add_comm (d * 2 ^ Z.of_nat (size bs1))) in H. move/Z.sub_move_r: H.
    move=> <-. rewrite bv2z_not_signed; last by (rewrite -Hs12; auto with zarith).
    exists d. replace (Z.b2z true)%Z with 1%Z by reflexivity.
    replace Z.one with 1%Z by reflexivity. ring.
  Qed.

  Lemma to_Z_subc_ex bs1 bs2 :
    0 < size bs1 ->
    size bs1 = size bs2 ->
    exists d,
      (to_Z bs1 - to_Z bs2)%Z =
        (d * Z.pow 2 (Z.of_nat (size bs1)) + to_Z (adcB true bs1 (~~# bs2)).2)%Z.
  Proof.
    move=> Hs1 Hs12. move: (to_Z_sbc_ex true Hs1 Hs12) => [d H].
    exists d. rewrite -H. replace (Z.b2z true)%Z with 1%Z by reflexivity.
    ring.
  Qed.

  Lemma to_Z_sbb_ex bs1 bs2 (b : bool) :
    size bs1 = size bs2 ->
    exists d,
      (to_Z bs1 - to_Z bs2 - b)%Z =
        (d * Z.pow 2 (Z.of_nat (size bs1)) + to_Z (sbbB b bs1 bs2).2)%Z.
  Proof.
    move=> Hs12. rewrite !to_Z_to_Zpos. rewrite (to_Zpos_sbbB b Hs12).
    rewrite size_sbbB Hs12 minnn.
    exists (- msb bs1 + msb bs2 - (sbbB b bs1 bs2).1 + msb (sbbB b bs1 bs2).2)%Z.
    ring.
  Qed.

  Lemma to_Z_subB_ex bs1 bs2 :
    size bs1 = size bs2 ->
    exists d,
      (to_Z bs1 - to_Z bs2)%Z =
        (d * Z.pow 2 (Z.of_nat (size bs1)) + to_Z (subB bs1 bs2))%Z.
  Proof.
    move=> Hs12. rewrite /subB. move: (to_Z_sbb_ex false Hs12) => [d H].
    exists d. rewrite -H. replace (Z.b2z false)%Z with 0%Z by reflexivity.
    rewrite Z.sub_0_r. reflexivity.
  Qed.



  Lemma Z_mul_to_Z_msb_same bs1 bs2 :
    msb bs1 == msb bs2 -> (0 <= to_Z bs1 * to_Z bs2)%Z.
  Proof.
    case Hmsb1 : (msb bs1); case Hmsb2 : (msb bs2); move=> //= _.
    - rewrite high1_1_to_Z; last by rewrite high1_msb Hmsb1.
      rewrite high1_1_to_Z; last by rewrite high1_msb Hmsb2.
      rewrite Z.mul_opp_opp.
      apply Z.mul_nonneg_nonneg; apply Z.le_le_succ_r; exact: to_Zneg_ge0.
    - rewrite high1_0_to_Z; last by rewrite high1_msb Hmsb1.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hmsb2.
      apply Z.mul_nonneg_nonneg; exact: to_Zpos_ge0.
  Qed.

  Lemma Z_mul_to_Z_msb_diff bs1 bs2 :
    ~~ (msb bs1 == msb bs2) -> (to_Z bs1 * to_Z bs2 <= 0)%Z.
  Proof.
    case Hmsb1 : (msb bs1); case Hmsb2 : (msb bs2); move=> //= _.
    - rewrite high1_1_to_Z; last by rewrite high1_msb Hmsb1.
      rewrite high1_0_to_Z; last by rewrite high1_msb Hmsb2.
      apply Z.mul_nonpos_nonneg; last exact: to_Zpos_ge0.
      rewrite Z.opp_nonpos_nonneg. apply Z.le_le_succ_r; exact: to_Zneg_ge0.
    - rewrite high1_0_to_Z; last by rewrite high1_msb Hmsb1.
      rewrite high1_1_to_Z; last by rewrite high1_msb Hmsb2.
      apply Z.mul_nonneg_nonpos; first exact: to_Zpos_ge0.
      rewrite Z.opp_nonpos_nonneg. apply Z.le_le_succ_r; exact: to_Zneg_ge0.
  Qed.


  Lemma bv2z_mul_unsigned bs1 bs2 :
    size bs1 = size bs2 -> ~~ Umulo bs1 bs2 ->
    to_Zpos (bs1 *# bs2)%bits = (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
    exact: to_Zpos_mulB.
  Qed.

  Lemma bv2z_mul_signed bs1 bs2 :
    0 < size bs1 -> size bs1 = size bs2 -> ~~ Smulo bs1 bs2 ->
    to_Z (bs1 *# bs2)%bits = (to_Z bs1 * to_Z bs2)%Z.
  Proof.
    case Hbs1 : (bs1 == zeros (size bs1));
      first by rewrite (eqP Hbs1) mul0B to_Z_zeros Z.mul_0_l.
    case Hbs2 : (bs2 == zeros (size bs2));
      first by rewrite (eqP Hbs2) mulB0' 2!to_Z_zeros Z.mul_0_r.
    move=> Hgt Hsz Hov. move: (to_Zpos_full_mul bs1 bs2).
    move/Z.add_move_r: (to_Z_to_Zpos (full_mul bs1 bs2)).
    move/Z.add_move_r: (to_Z_to_Zpos bs1); move/Z.add_move_r: (to_Z_to_Zpos bs2).
    move=> <- <- <-.
    rewrite size_full_mul Nat2Z.inj_add Z.pow_add_r; try exact: Nat2Z.is_nonneg.
    rewrite Z.mul_add_distr_r 2!Z.mul_add_distr_l -Hsz.
    rewrite [(_*_*_)%Z](Z.mul_comm _ (to_Z bs2)) !Z.mul_assoc -!Z.add_assoc
            -!Z.mul_add_distr_r => H.
    apply (f_equal (fun z => Z.modulo z (2 ^ Z.of_nat (size bs1)))) in H; move: H.
    repeat (rewrite Z.mod_add; last exact: pow2_nat2z_nonzero).
    rewrite to_Z_mod_pow2; last by rewrite size_full_mul leq_addr.
    rewrite (to_Z_to_Zpos (_ *# _)) size_mulB => ->.
    apply negbT in Hbs1; apply negbT in Hbs2.
    case Hmsb : (msb bs1 == msb bs2);
      rewrite (msb_mulB_signed Hsz Hov Hbs1 Hbs2) Hmsb /negb ?Z.mul_0_l ?Z.mul_1_l.
    - rewrite Z.sub_0_r Z.mod_small; first reflexivity.
      split; first exact: Z_mul_to_Z_msb_same.
      move: (to_Z_smulo Hsz Hgt Hov) => [_ Hbnd]. apply (Z.lt_trans _ _ _ Hbnd).
      apply Z.pow_lt_mono_r; try done;
        [ exact: Nat2Z.is_nonneg | rewrite Z.sub_1_r; exact: Z.lt_pred_l].
    - apply negbT in Hmsb. move: (Z_mul_to_Z_msb_diff Hmsb) => Hle0.
      have Hmul : ((to_Z bs1 * to_Z bs2) mod - 2 ^ Z.of_nat (size bs1))%Z =
                  (to_Z bs1 * to_Z bs2)%Z.
      {
        rewrite -(Z.mod_unique _ _ 0 (to_Z bs1 * to_Z bs2)); first reflexivity.
        + right. split; last exact: Hle0.
          move: (to_Z_smulo Hsz Hgt Hov) => [Hbnd _].
          apply: (Z.lt_le_trans _ _ _ _ Hbnd). rewrite -Z.opp_lt_mono.
          apply Z.pow_lt_mono_r; try done;
            [ exact: Nat2Z.is_nonneg | rewrite Z.sub_1_r; exact: Z.lt_pred_l].
        + by rewrite Z.mul_0_r Z.add_0_l.
      }
      rewrite -{1}(Z.opp_involutive (2 ^ _)) Z.mod_opp_r_nz.
      + rewrite Hmul Z.sub_opp_r Z.add_simpl_r. reflexivity.
      + rewrite -Z_nonzero_opp. exact: pow2_nat2z_nonzero.
      + rewrite Hmul Z.mul_eq_0.
        case=> H0; apply to_Z0 in H0; [move: Hbs1 | move: Hbs2];
          by rewrite {1}H0 eqxx.
  Qed.

  Lemma bv2z_mull_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    (to_Zpos (low (size bs2) (zext (size bs1) bs1 *# zext (size bs1) bs2)%bits) +
     to_Zpos (high (size bs1) (zext (size bs1) bs1 *# zext (size bs1) bs2)%bits) *
     2 ^ Z.of_nat (size bs2))%Z =
    (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. rewrite {1 4}Hsz -full_mul_mulB_zext.
    rewrite -to_Zpos_full_mul -to_Zpos_low_high; first reflexivity.
    by rewrite size_full_mul addnC.
  Qed.

  Lemma bv2z_mull_signed bs1 bs2 :
    0 < size bs1 ->
    size bs1 = size bs2 ->
    (to_Zpos (low (size bs2) (sext (size bs1) bs1 *# sext (size bs1) bs2)%bits) +
     to_Z (high (size bs1) (sext (size bs1) bs1 *# sext (size bs1) bs2)%bits) *
     2 ^ Z.of_nat (size bs2))%Z =
    (to_Z bs1 * to_Z bs2)%Z.
  Proof.
    move=> Hbs1 Hsz.
    rewrite -(to_Z_low_high Hbs1); last by rewrite size_mulB size_sext Hsz.
    rewrite bv2z_mul_signed; [by rewrite 2!to_Z_sext | rewrite size_sext; by apply ltn_addl | by rewrite 2!size_sext Hsz |].
    by rewrite {1}Hsz smulo_sext.
  Qed.

  Lemma bv2z_mulj_unsigned bs1 bs2 :
    size bs1 = size bs2 ->
    to_Zpos (zext (size bs1) bs1 *# zext (size bs1) bs2)%bits =
    (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
    move=> Hsz. rewrite {1}Hsz -full_mul_mulB_zext. exact: to_Zpos_full_mul.
  Qed.

  Lemma bv2z_mulj_signed bs1 bs2 :
    0 < size bs1 -> size bs1 = size bs2 ->
    to_Z (sext (size bs1) bs1 *# sext (size bs1) bs2)%bits = (to_Z bs1 * to_Z bs2)%Z.
  Proof.
    move=> Hgt Hsz.
    rewrite bv2z_mul_signed; [by rewrite 2!to_Z_sext | rewrite size_sext; by apply ltn_addl | by rewrite 2!size_sext Hsz |].
    by rewrite {1}Hsz smulo_sext.
  Qed.

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

  (*---------------------------------------------------------------------------
    Semantics of operations w.r.t. N
  ---------------------------------------------------------------------------*)

  (* succB *)

  Lemma to_N_succB bs :
    to_N (succB bs) = ((to_N bs + 1) mod 2 ^ N.of_nat (size bs))%num.
  Proof.
    rewrite to_N_Zpos to_Zpos_succB. move: (@to_Zpos_ge0 bs) => Hbs.
    rewrite Z2N_inj_mod;
      [ | by auto with zarith | exact: pow2_nat2z_gt0].
    rewrite Z2N.inj_add; try by auto with zarith.
    rewrite Z2N.inj_pow; [ | done | exact: Nat2Z.is_nonneg].
    rewrite -!to_N_Zpos nat_Z_N. reflexivity.
  Qed.

  Lemma from_N_succB bs : succB bs = from_N (size bs) ((to_N bs) + 1).
  Proof.
    move: (to_N_succB bs) => H. apply (f_equal (from_N (size bs))) in H.
    move: (size_succB bs) => Hsz. rewrite -{1}Hsz from_N_to_N in H. rewrite H.
    rewrite {2}(N.div_mod' (to_N bs + 1) (2 ^ N.of_nat (size bs))).
    rewrite N.mul_comm [in RHS]N.add_comm -from_N_wrapMany. reflexivity.
  Qed.

  (* negB *)

  Lemma to_N_negB bs :
    to_N (negB bs) = ((2 ^ N.of_nat (size bs) - to_N bs) mod 2 ^ N.of_nat (size bs))%num.
  Proof.
    rewrite to_N_Zpos to_Zpos_negB -(Z.mod_add _ 1); last exact: pow2_nat2z_nonzero.
    rewrite Z.mul_1_l Z.add_comm Z.add_opp_r.
    move: (to_Zpos_bounded bs) => Hbnd; apply Z.lt_0_sub in Hbnd.
    rewrite Z2N_inj_mod; [ | by auto with zarith | exact: pow2_nat2z_gt0].
    rewrite Z2N.inj_sub; last exact: to_Zpos_ge0.
    rewrite Z2N.inj_pow; [ | done | exact: Nat2Z.is_nonneg].
    rewrite -!to_N_Zpos nat_Z_N. reflexivity.
  Qed.

  Lemma from_N_negB bs :
    negB bs = from_N (size bs) (2 ^ N.of_nat (size bs) - to_N bs).
  Proof.
    move: (to_N_negB bs) => H. apply (f_equal (from_N (size bs))) in H.
    move: (size_negB bs) => Hsz. rewrite -{1}Hsz from_N_to_N in H. rewrite H.
    rewrite {2}(N.div_mod' (2 ^ _ - to_N bs) (2 ^ N.of_nat (size bs))).
    rewrite N.mul_comm [in RHS]N.add_comm -from_N_wrapMany. reflexivity.
  Qed.

  (* addB *)

  Lemma to_N_addB bs1 bs2 :
    size bs1 = size bs2 ->
    to_N (addB bs1 bs2) = ((to_N bs1 + to_N bs2) mod 2 ^ N.of_nat (size bs1))%num.
  Proof.
    move=> Hsz. rewrite to_N_Zpos (to_Zpos_addB' Hsz).
    move: (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2) => Hbs1 Hbs2.
    rewrite Z2N_inj_mod; [ | by auto with zarith | exact: pow2_nat2z_gt0].
    rewrite Z2N.inj_add; try by auto with zarith.
    rewrite Z2N.inj_pow; [ | done | exact: Nat2Z.is_nonneg].
    rewrite -!to_N_Zpos nat_Z_N. reflexivity.
  Qed.

  (* subB *)

  Lemma to_N_subB bs1 bs2 :
    size bs1 = size bs2 ->
    to_N (subB bs1 bs2) =
    ((2 ^ N.of_nat (size bs1) + to_N bs1 - to_N bs2) mod 2 ^ N.of_nat (size bs1))%num.
  Proof.
    move=> Hsz.
    rewrite to_N_Zpos (to_Zpos_subB' Hsz).
    rewrite -(Z.mod_add _ 1); last exact: pow2_nat2z_nonzero.
    rewrite Z.mul_1_l -Z.add_sub_swap -Z.add_sub_assoc.
    move: (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2) (to_Zpos_bounded bs2) => H1 H2 Hbnd.
    have H : (0 <= 2 ^ Z.of_nat (size bs1) - to_Zpos bs2)%Z by rewrite Hsz; auto with zarith.
    rewrite Z2N_inj_mod; [ | by auto with zarith | exact: pow2_nat2z_gt0].
    rewrite Z2N.inj_add; try done.
    rewrite Z2N.inj_sub; last exact: H2.
    rewrite N.add_sub_assoc; last by apply (Z2N.inj_le _ _ H2); rewrite Hsz; auto with zarith.
    rewrite Z2N.inj_pow; [ | done | exact: Nat2Z.is_nonneg].
    rewrite N.add_comm -!to_N_Zpos nat_Z_N. reflexivity.
  Qed.

  (* mulB *)

  Lemma to_N_mulB bs1 bs2 :
    to_N (mulB bs1 bs2) = ((to_N bs1 * to_N bs2) mod 2 ^ N.of_nat (size bs1))%num.
  Proof.
    rewrite to_N_Zpos to_Zpos_mulB'.
    move: (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2) => Hbs1 Hbs2.
    rewrite Z2N_inj_mod; [ | by apply Z.mul_nonneg_nonneg | exact: pow2_nat2z_gt0].
    rewrite Z2N.inj_mul; try done.
    rewrite Z2N.inj_pow; [ | done | exact: Nat2Z.is_nonneg].
    rewrite -!to_N_Zpos nat_Z_N. reflexivity.
  Qed.

  (* udivB *)

  Lemma to_N_udivB_zero bs n : udivB' bs (zeros n) = ones (size bs).
  Proof. by rewrite /udivB' udivB0. Qed.

  Lemma to_N_udivB_nonzero bs1 bs2 :
    size bs1 = size bs2 -> ~~ (bs2 == zeros (size bs2)) ->
    to_N (udivB' bs1 bs2) = ((to_N bs1) / (to_N bs2))%num.
  Proof.
    move=> Hsz Hn0. symmetry in Hsz. rewrite to_N_Zpos (to_Zpos_udivB' Hsz Hn0).
    move: (@to_Zpos_ge0 bs1) (@to_Zpos_ge0 bs2) => Hbs1 Hbs2.
    rewrite Z2N.inj_div; try done. by rewrite -!to_N_Zpos.
  Qed.

  (* uremB *)

  Lemma to_N_uremB_zero bs n : uremB bs (zeros n) = bs.
  Proof. by rewrite /uremB udivB0. Qed.

  Lemma to_N_uremB_nonzero bs1 bs2 :
    size bs1 = size bs2 -> ~~ (bs2 == zeros (size bs2)) ->
    to_N (uremB bs1 bs2) = ((to_N bs1) mod (to_N bs2))%num.
  Proof.
    move=> Hsz Hn0. symmetry in Hsz. rewrite to_N_Zpos (to_Zpos_uremB' Hsz Hn0).
    move: (@to_Zpos_ge0 bs1) (neq_zeros_to_Zpos_gt0 Hn0) => Hbs1 Hbs2.
    rewrite Z2N_inj_mod; [ | by auto with zarith | by auto with zarith].
    by rewrite -!to_N_Zpos.
  Qed.

  (* ltB *)

  Lemma to_N_ltB bs1 bs2 : ltB bs1 bs2 <-> (to_N bs1 < to_N bs2)%num.
  Proof.
    rewrite to_Zpos_ltB !to_N_Zpos Z2N.inj_lt; try done; exact: to_Zpos_ge0.
  Qed.

  Lemma to_N_ltB_eqn bs1 bs2 : ltB bs1 bs2 = (to_N bs1 <? to_N bs2)%num.
  Proof.
    case HltB : (ltB bs1 bs2); case Hltb : (to_N bs1 <? to_N bs2)%num; try done.
    - apply to_N_ltB, N.ltb_lt in HltB. by rewrite -HltB -Hltb.
    - apply N.ltb_lt, to_N_ltB in Hltb. by rewrite -HltB -Hltb.
  Qed.

  (* leB *)

  Lemma to_N_leB bs1 bs2 :
    size bs1 = size bs2 -> leB bs1 bs2 <-> (to_N bs1 <= to_N bs2)%num.
  Proof.
    move=> Hsz.
    rewrite (to_Zpos_leB Hsz) !to_N_Zpos Z2N.inj_le; try done; exact: to_Zpos_ge0.
  Qed.

  Lemma to_N_leB_eqn bs1 bs2 :
    size bs1 = size bs2 -> leB bs1 bs2 = (to_N bs1 <=? to_N bs2)%num.
  Proof.
    move=> Hsz.
    case HleB : (leB bs1 bs2); case Hleb : (to_N bs1 <=? to_N bs2)%num; try done.
    - apply (to_N_leB Hsz), N.leb_le in HleB. by rewrite -HleB -Hleb.
    - apply N.leb_le, (to_N_leB Hsz) in Hleb. by rewrite -HleB -Hleb.
  Qed.

End Lemmas.
