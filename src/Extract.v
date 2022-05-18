
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt.
From Coq Require Import Arith List.
From mathcomp Require Import seq.
From nbits Require Import NBits.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String.

Cd "src/ocaml".
Extraction "extracted"
         (* Basic operations *)
         nseq zeros ones splitlsb splitmsb droplsb dropmsb joinlsb joinmsb lsb msb
         (* Bitwise operations *)
         high low extract slice zext sext repeat
         invB succB predB andB orB xorB negB
         rolB rorB shrB shrBB sarB sarBB shlB shlBB
         (* Arithmetic operations *)
         adcB addB carry_addB addB_ovf sbbB subB borrow_subB Saddo Ssubo
         full_mul mulB Umulo Smulo udivB' uremB sdivB' sdivB sremB smodB
         (* Comparison operations *)
         ltB leB gtB geB sltB sleB sgtB sgeB
         (* Testing operations *)
         is_zero
         (* Casting *)
         ucastB scastB
         (* Conversions *)
         to_nat from_nat from_bool to_bool to_N from_N
         to_Zpos to_Zneg to_Z from_Zpos from_Zneg from_Z
         from_bin from_hex from_string to_hex to_bin.
Cd "../..".
