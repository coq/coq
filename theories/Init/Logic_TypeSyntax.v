(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Logic_Type.

(** Parsing of things in [Logic_type.v] *)

Grammar constr constr1 :=
  eqT_expl [ "<" lconstr($l1) ">" constr0($c1) "==" constr0($c2) ] ->
          [ (eqT $l1 $c1 $c2) ]
| eqT_impl [ constr0($c) "==" constr0($c2) ] -> [ (eqT ? $c $c2) ]
| idT_expl [ "<" lconstr($l1) ">" constr0($c1) "===" constr0($c2) ] ->
          [ (identityT $l1 $c1 $c2) ]
| idT_impl [ constr0($c) "===" constr0($c2) ] -> [ (identityT ? $c $c2) ]

with constr10 :=
  allTexplicit [ "ALLT" ident($v) ":" constr($t) "|" constr($c1) ]
                          -> [ (allT $t [$v : $t]$c1) ]
| allTimplicit [ "ALLT" ident($v) "|" constr($c1) ] 
                          -> [ (allT ? [$v]$c1) ]
| exTexplicit [ "EXT" ident($v) ":" constr($t) "|" constr($c1) ]
                          -> [ (exT $t [$v : $t]$c1) ]
| exTimplicit [ "EXT" ident($v) "|" constr($c1) ] 
                          -> [ (exT ? [$v]$c1) ]
| exT2explicit [ "EXT" ident($v) ":" constr($t) "|" constr($c1) "&"
           constr($c2) ] -> [ (exT2 $t [$v : $t]$c1 [$v : $t]$c2) ]
| exT2implicit [ "EXT" ident($v) "|" constr($c1) "&" 
           constr($c2) ] -> [ (exT2 ? [$v]$c1 [$v]$c2) ].

(** Pretty-printing of things in [Logic_type.v] *)

Syntax constr
  level 10:
    allT_pred [ (allT $_ $p) ] -> [ [<hov 0> "AllT " $p:L ] ]
  | allT [ (allT $T [$x : $T]$p) ]
       -> [ [<hov 3> "ALLT " $x ":" $T:L " |" [1 0] $p:L ] ]

  | exT_pred [ (exT $_ $p) ] -> [ [<hov 4> "ExT " $p:L ] ]
  | exT [ (exT $t1 [$x : $T]$p) ] 
       -> [ [<hov 4> "EXT " $x ":" $T:L " |" [1 0] $p:L ] ]

  | exT2_pred [ (exT2 $_ $p1 $p2) ]
       -> [ [<hov 4> "ExT2 " $p1:L [1 0] $p2:L ] ]
  | exT2 [ (exT2 $T [$x : $T]$P1 [$x : $T]$P2) ] 
       -> [ [<hov 2> "EXT " $x ":" $T:L " |" [1 2] $P1:L [1 0] "& " $P2:L] ]
  ;

  level 1:
    eqT [ (eqT $a $c1 $c2) ] -> [ [<hov 1> (ANNOT $a) $c1:E [0 0] "==" $c2:E ] ]
  | identityT [ (identityT $_ $c1 $c2) ]
       -> [ [<hov 1> $c1:E [0 0] "===" $c2:E ] ].
