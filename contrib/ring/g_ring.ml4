(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Quote
open Ring

TACTIC EXTEND Ring
  [ "Ring" constr_list(l) ] -> [ polynom l ]
END

(* The vernac commands "Add Ring" and co *)

let cset_of_constrarg_list l = 
  List.fold_right ConstrSet.add (List.map constr_of l) ConstrSet.empty

VERNAC COMMAND EXTEND AddRing
  [ "Add" "Ring" 
          constr(a) constr(aplus) constr(amult) constr(aone) constr(azero)
          constr(aopp) constr(aeq) constr(t) "[" ne_constr_list(l) "]" ] 
  -> [ add_theory true false false
			 (constr_of a)
			 None
			 None
			 None
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (Some (constr_of aopp))
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_constrarg_list l) ]

| [ "Add" "Semi" "Ring" 
      	  constr(a) constr(aplus) constr(amult) constr(aone) constr(azero)
          constr(aeq) constr(t) "[" ne_constr_list(l) "]" ] 
  -> [ add_theory false false false
			 (constr_of a)
			 None
			 None
			 None
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 None
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_constrarg_list l) ]

| [ "Add" "Abstract" "Ring" 
    	  constr(a) constr(aplus) constr(amult) constr(aone)
          constr(azero) constr(aopp) constr(aeq) constr(t) ] 
  -> [ add_theory true true false
			 (constr_of a)
			 None
			 None
			 None
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (Some (constr_of aopp))
			 (constr_of aeq)
			 (constr_of t)
			 ConstrSet.empty ]

| [ "Add" "Abstract" "Semi" "Ring" 
          constr(a) constr(aplus) constr(amult) constr(aone)
          constr(azero) constr(aeq) constr(t) ] 
  -> [ add_theory false true false
			 (constr_of a)
			 None
			 None
			 None
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 None
			 (constr_of aeq)
			 (constr_of t)
			 ConstrSet.empty ]

| [ "Add" "Setoid" "Ring"
      	  constr(a) constr(aequiv) constr(asetth) constr(aplus) constr(amult) 
	  constr(aone) constr(azero) constr(aopp) constr(aeq) constr(pm)
	  constr(mm) constr(om) constr(t) "[" ne_constr_list(l) "]" ] 
  -> [ add_theory true false true
			 (constr_of a)
			 (Some (constr_of aequiv))
			 (Some (constr_of asetth))
			 (Some {
			    plusm = (constr_of pm);
			    multm = (constr_of mm);
			    oppm = Some (constr_of om) })
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (Some (constr_of aopp))
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_constrarg_list l) ]

| [ "Add" "Semi" "Setoid" "Ring" 
          constr(a) constr(aequiv) constr(asetth) constr(aplus)
	  constr(amult) constr(aone) constr(azero) constr(aeq) 
          constr(pm) constr(mm) constr(t) "[" ne_constr_list(l) "]" ] 
  -> [ add_theory false false true
			 (constr_of a)
			 (Some (constr_of aequiv))
			 (Some (constr_of asetth))
			 (Some {
			    plusm = (constr_of pm);
			    multm = (constr_of mm);
			    oppm = None })
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 None
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_constrarg_list l) ]
END
