(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require LogicSyntax.
Require Specif.

(** Parsing of things in Specif.v *)

(* To accept {x:A|P}*B without parentheses *)
Grammar constr constr6 :=
  sig [ "{" lconstr($lc) ":" constr($c1) "|" lconstr($c2) "}" "*" constr6($c) ]
       -> [ (prod (sig $c1 [$lc : $c1]$c2) $c) ]

| sig2 [ "{" lconstr($lc) ":" lconstr($c1)
           "|" lconstr($c2) "&" lconstr($c3) "}" "*" constr6($c) ]
       -> [ (prod (sig2 $c1 [$lc : $c1]$c2 [$lc : $c1]$c3) $c) ]

| sigS [ "{" lconstr($lc) ":" lconstr($c1) "&" lconstr($c2) "}"
         "*" constr6($c)]
       -> [ (prod (sigS $c1 [$lc : $c1]$c2) $c) ]

| sigS2 [ "{" lconstr($lc) ":" lconstr($c1)
             "&" lconstr($c2) "&" lconstr($c3) "}" "*" constr6($c) ]
       -> [ (prod (sigS2 $c1 [$lc : $c1]$c2 [$lc : $c1]$c3) $c) ].

(* To factor with {A}+{B} *)
Grammar constr constr6 :=
  sig [ "{" lconstr($lc) ":" constr($c1) "|" lconstr($c2) "}" ]
       -> [ (sig $c1 [$lc : $c1]$c2) ]

| sig2 [ "{" lconstr($lc) ":" constr($c1)
           "|" lconstr($c2) "&" lconstr($c3) "}" ]
       -> [ (sig2 $c1 [$lc : $c1]$c2 [$lc : $c1]$c3) ]

| sigS [ "{" lconstr($lc) ":" constr($c1) "&" lconstr($c2) "}" ]
       -> [ (sigS $c1 [$lc : $c1]$c2) ]

| sigS2 [ "{" lconstr($lc) ":" constr($c1)
             "&" lconstr($c2) "&" lconstr($c3) "}" ]
       -> [ (sigS2 $c1 [$lc : $c1]$c2 [$lc : $c1]$c3) ].

Grammar constr constr6 :=
  sumbool [ "{" lconstr($lc) "}" "+" "{" lconstr($lc2) "}" ] -> 
    [ (sumbool $lc $lc2) ].

Grammar constr constr7 :=
  sumor [ constr7($c1) "+" "{" lconstr($c2) "}" ] ->
    [ (sumor $c1 $c2) ]

| sumsig [ constr7($c) "+" "{" lconstr($lc) ":" constr($c1) "|" lconstr($c2) "}" ] ->
    [ (sum $c (sig $c1 [$lc : $c1]$c2)) ]

| sumsig2 [ constr7($c) "+" "{" lconstr($lc) ":" constr($c1)
           "|" lconstr($c2) "&" lconstr($c3) "}" ]
       -> [ (sum $c (sig2 $c1 [$lc : $c1]$c2 [$lc : $c1]$c3)) ]

| sumsigS [ constr7($c) "+" "{" lconstr($lc) ":" constr($c1) "&" lconstr($c2) "}" ]
       -> [ (sum $c (sigS $c1 [$lc : $c1]$c2)) ]

| sumsigS2 [ constr7($c) "+" "{" lconstr($lc) ":" constr($c1)
             "&" lconstr($c2) "&" lconstr($c3) "}" ]
       -> [ (sum $c (sigS2 $c1 [$lc : $c1]$c2 [$lc : $c1]$c3)) ]
.


(** Pretty-printing of things in Specif.v *)

Syntax constr
  level 1:
(** Pretty-printing of [sig] *)
  | sig_nb [ (sig $c1 [_:$1]$c2) ]
      -> [ [<hov 0> "{_:" $c1:E " |" [1 3] $c2:E "}" ] ]
  | sigma_b [ (sig $c1 [$id:$1]$c2) ]
      -> [ [<hov 0> "{" $id ":" $c1:E " |" [1 3] $c2:E "}" ] ]

(** Pretty-printing of [sig2] *)
  | sig2_b_b
      [ (sig2 $c1 [$id:$c1]$c2 [$id:$c1]$c3) ]
       -> [ [<hov 0> "{"$id":"$c1:E"|" [1 3]$c2:E [1 3]"& "$c3:E "}" ] ]
  | sig2_nb_b
      [ (sig2 $c1 [_:$c1]$c2 [$id:$c1]$c3) ]
       -> [ [<hov 0> "{"$id":"$c1:E"|" [1 3]$c2:E [1 3]"& "$c3:E "}" ] ]
  | sig2_b_nb
      [ (sig2 $c1 [$id:$c1]$c2 [_:$c1]$c3) ]
       -> [ [<hov 0> "{"$id":"$c1:E"|" [1 3]$c2:E [1 3]"& "$c3:E "}" ] ]
  | sig2_nb_nb
      [ (sig2 $c1 [_:$c1]$c2 [_:$c1]$c3) ]
       -> [ [<hov 0> "{_:"$c1:E "|" [1 3] $c2:E [1 3]"& " $c3:E "}" ] ]

(** Pretty-printing of [sigS] *)
  | sigS_nb [ (sigS $c1 [_:$c1]$c2) ]
       -> [ [<hov 0> "{_:" $c1:E [1 3]"& " $c2:E  "}" ] ]
  | sigS_b [ (sigS $c1 [$id:$c1]$c2) ]
       -> [ [<hov 0> "{" $id  ":" $c1:E [1 3] "& " $c2:E "}" ] ]

(** Pretty-printing of [sigS2] *)
  | sigS2_b_b
      [ (sigS2 $c1 [$id:$c1]$c2 [$id:$c1]$c3) ]
       -> [ [<hov 0> "{"$id ":" $c1:E [1 3]"& "$c2:E [1 3]"& "$c3:E "}" ] ]
  | sigS2_nb_b
      [ (sigS2 $c1 [_:$c1]$c2 [$id:$c1]$c3) ]
       -> [ [<hov 0> "{"$id ":" $c1:E [1 3]"& "$c2:E [1 3]"& "$c3:E "}" ] ]
  | sigS2_b_nb
      [ (sigS2 $c1 [$id:$c1]$c2 [_:$c1]$c3) ]
       -> [ [<hov 0> "{"$id ":" $c1:E [1 3]"& "$c2:E [1 3]"& "$c3:E "}" ] ]
  | sigS2_nb_nb
      [ (sigS2 $c1 [_:$c1]$c2 [_:$c1]$c3) ]
       -> [ [<hov 0> "{_:"$c1:E [1 3]"& "$c2:E [1 3]"& "$c3:E "}" ] ]

(** Pretty-printing of [projS1] and [projS2] *)
  | projS1_imp [ (projS1 ? ? $a) ] -> ["(ProjS1 " $a:E ")"]  
  | projS2_imp [ (projS2 ? ? $a) ] -> ["(ProjS2 " $a:E ")"]
  ;

(** Pretty-printing of [sumbool] and [sumor] *)
  level 4:
    sumbool [ (sumbool $t1 $t2) ]
       -> [ [<hov 0> "{" $t1:E "}" [0 1] "+" "{" $t2:L "}"] ]
  | sumor [ (sumor $t1 $t2) ]
       -> [ [<hov 0> $t1:E [0 1]  "+" "{" $t2:L "}"] ]
  ;

(** Pretty-printing of [except] *)
  level 1:
    Except_imp [ (except $1 $t2) ] -> [ [<hov 0> "Except " $t2 ] ]

(** Pretty-printing of [error] and [value] *)
  | Error_imp [ (error $t1) ]     -> [ [<hov 0> "Error" ] ]
  | Value_imp [ (value $t1 $t2) ] -> [ [<hov 0> "(Value " $t2 ")" ] ].

