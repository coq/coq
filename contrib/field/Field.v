(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export Field_Compl.
Require Export Field_Theory.
Require Export Field_Tactic.

Declare ML Module "field".

Grammar vernac opt_arg_list : List :=
| noal [] -> []
| minus [ "minus" ":=" constrarg($aminus) opt_arg_list($l) ] ->
  [ "minus" $aminus ($LIST $l) ]
| div [ "div" ":=" constrarg($adiv) opt_arg_list($l) ] ->
  [ "div" $adiv ($LIST $l) ]

with extra_args : List :=
| nea [] -> []
| with_a [ "with" opt_arg_list($l)] -> [ ($LIST $l) ]

with vernac : ast := 
  addfield [ "Add" "Field" 
      	     constrarg($a) constrarg($aplus) constrarg($amult) constrarg($aone)
      	     constrarg($azero) constrarg($aopp) constrarg($aeq)
             constrarg($ainv) constrarg($rth) constrarg($ainv_l) extra_args($l)
             "." ]
    -> [(AddField $a $aplus $amult $aone $azero $aopp $aeq $ainv $rth
                  $ainv_l ($LIST $l))].

Grammar tactic simple_tactic: ast :=
  | field [ "Field" ] -> [(Field)].

Syntax tactic level 0:
  | field [(Field)] -> ["Field"].
