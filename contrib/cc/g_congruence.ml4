(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Cctac
open Tactics
open Tacticals

(* Tactic registration *)
      
TACTIC EXTEND CC
 [ "Congruence" ] -> [ tclORELSE 
			 (tclTHEN (tclREPEAT introf) (cc_tactic [])) 
			 cc_fail ]
END
      
TACTIC EXTEND CCwith
 [ "Congruence" "with" ne_constr_list(l) ] -> [ tclORELSE 
			 (tclTHEN (tclREPEAT introf) (cc_tactic l)) 
			 cc_fail]
END
