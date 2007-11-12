(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: goal.ml aspiwack $ *)

(* This module implements the abstract interface to goals *)

(* type of the goals *)
type goal = {
  content : Evd.evar_info; (* logical information hyps |- concl and alike *)
  name : string option     (* optional name of the goal to be displayed *)
}

(* access primitive *)
let hyps gl = gl.content.hyps
let concl gl = gl.content.concl
let name gl = gl.name

let build ?name ~hyps ~concl =
  { content = Evd.make_evar hyps concl ;
    name = name
  }

(* arnaud: à commenter bien sûr *)
let refine defs env check_type step gl =
  (* Builds an environment containing (hyps gl) *)
