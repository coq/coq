(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Export Logic.

(** Parsing of things in Logic.v *)

Grammar constr constr1 :=
  conj [ "<" lconstr($l1) "," lconstr($c2) ">" "{" constr($c3) ","
        constr($c4) "}" ] -> [ (conj $l1 $c2 $c3 $c4) ]
| proj1 [ "<" lconstr($l1) "," lconstr($c2) ">" "Fst" "{"
        lconstr($l) "}" ] -> [ (proj1 $l1 $c2 $l) ]
| proj2 [ "<" lconstr($l1) "," lconstr($c2) ">" "Snd" "{"
        lconstr($l) "}" ] -> [ (proj2 $l1 $c2 $l) ]
| all [ "<" lconstr($l1) ">" "All" "(" lconstr($l2) ")" ] ->
      [ (all $l1 $l2) ]
| eq_expl [ "<" lconstr($l1) ">" constr0($c1) "=" constr0($c2) ] ->
          [ (eq $l1 $c1 $c2) ]
| eq_impl [ constr0($c) "=" constr0($c2) ] -> [ (eq ? $c $c2) ]
| IF [ "IF" constr($c1) "then" constr($c2) "else" constr($c3)] ->
     [ (IF $c1 $c2 $c3) ]
with constr10 :=
  allexplicit [ "ALL" ident($x) ":" constr($t) "|" constr($p) ]
                          -> [ (all $t [$x : $t]$p) ]
| allimplicit [ "ALL" ident($x) "|" constr($p) ]
                          -> [ (all ? [$x]$p) ]
| exexplicit [ "EX" ident($v) ":" constr($t) "|" constr($c1) ]
                          -> [ (ex $t [$v : $t]$c1) ]
| eximplicit [ "EX" ident($v) "|" constr($c1) ] 
                          -> [ (ex ? [$v]$c1) ]
| ex2explicit [ "EX" ident($v) ":" constr($t) "|" constr($c1) "&"
           constr($c2) ] -> [ (ex2 $t [$v : $t]$c1 [$v : $t]$c2) ]
| ex2implicit [ "EX" ident($v) "|" constr($c1) "&" 
           constr($c2) ] -> [ (ex2 ? [$v]$c1 [$v]$c2) ].

Distfix RIGHTA 2 "~ _" not.

Infix RIGHTA 6 "/\\" and.

Infix RIGHTA 7 "\\/" or.

Infix RIGHTA 8 "<->" iff.

(** Pretty-printing of things in Logic.v *)

Syntax constr
  level 1:
    equal [ (eq $a  $t1  $t2) ] ->
	 [ [<hov 0> (ANNOT $a) $t1:E [0 1]  "=" $t2:E ] ]
  | annotskip [ << (ANNOT $_) >> ] -> [ ]
  | annotmeta [ << (ANNOT (META ($NUM $n))) >> ] -> [ "<" "?" $n ">" ]
  | conj [ (conj $t1 $t2 $t3 $t4) ]
      -> [ [<hov 1> [<hov 1> "<" $t1:L "," [0 0] $t2:L ">" ] [0 0]
                    [<hov 1> "{" $t3:L "," [0 0] $t4:L "}"] ] ]
  | IF [(IF $c1 then $c2 else $c3)] ->
       [ [<hov 0> "IF " $c1:E [1 0]
                  "then " $c2:E [1 0]
                  "else " $c3:E ] ]
  ;
  level 10:
    all_pred [ (all $_ $p) ] -> [ [<hov 4> "All " $p:L ] ]
  | all_imp [ (all $_ [$x : $T]$t) ]
       -> [ [<hov 3> "ALL " $x ":" $T:L " |" [1 0] $t:L ] ]

  | ex_pred [ (ex $_ $p) ] -> [ [<hov 0> "Ex " $p:L ] ]
  | ex [ (ex $_ [$x : $T]$P) ] 
       -> [ [<hov 2> "EX " $x ":" $T:L " |" [1 0] $P:L ] ]

  | ex2_pred [ (ex2 $_ $p1 $p2) ]
       -> [ [<hov 3> "Ex2 " $p1:L [1 0] $p2:L ] ]
  | ex2 [ (ex2 $_ [$x : $T]$P1 [$x : $T]$P2) ] 
       -> [ [<hov 2> "EX " $x ":" $T:L " |" [1 2] $P1:L [1 0] "& " $P2:L] ].
