(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Export Datatypes.

(* Parsing of things in Datatypes.v *)

Grammar constr constr1 :=
  pair_expl [ "<" lconstr($l1) "," lconstr($c2) ">" "(" lconstr($c3) ","
    lconstr($c4) ")" ] -> [ (pair $l1 $c2 $c3 $c4) ]
| fst_expl [ "<" lconstr($l1) "," lconstr($c2) ">" "Fst" "("
    lconstr($l) ")" ] -> [ (fst $l1 $c2 $l) ]
| snd_expl [ "<" lconstr($l1) "," lconstr($c2) ">" "Snd" "("
    lconstr($l) ")" ] -> [ (snd $l1 $c2 $l) ]

with constr0 :=
  pair [ "(" lconstr($lc1) "," lconstr($lc2) ")" ] ->
         [ (pair ? ? $lc1 $lc2) ]

with constr3 :=
  prod [ constr2($c1) "*" constr3($c2) ] -> [ (prod $c1 $c2) ].

(* Pretty-printing of things in Datatypes.v *)

Syntax constr
  level 4:
    sum [ (sum $t1 $t2) ] -> [ [<hov 0> $t1:E [0 1] "+" $t2:L ] ]
  ;

  level 3:
    product [ (prod $t1 $t2) ] -> [ [<hov 0>  $t1:L [0 1] "*" $t2:E ] ]
  ;

  level 1:
    pair
      [ (pair $_ $_ $t3 $t4) ] -> [ [<hov 0> "(" $t3:E ","[0 1] $t4:E ")" ] ]
  | fst_imp [ (fst $_ $_ $t2) ] -> [ [<hov 0> "(Fst " $t2:E ")"] ]
  | snd_imp [ (snd $_ $_ $t2) ] -> [ [<hov 0> "(Snd " $t2:E ")"] ].
