(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(**************************************************************************)
(*                                                                        *)
(* Omega: a solver of quantifier-free problems in Presburger Arithmetic   *)
(*                                                                        *)
(* Pierre Crégut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Eterm

TACTIC EXTEND eterm
  [ "eterm" ] -> [ 
    (fun gl ->
       let evm = Tacmach.project gl and t = Tacmach.pf_concl gl in
         Eterm.etermtac (evm, t) gl) ]
END
