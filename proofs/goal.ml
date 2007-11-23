(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* This module implements the abstract interface to goals *)

(* type of the goals *)
type goal = {
  content : Evd.evar_info; (* logical information hyps |- concl and alike *)
  name : string option     (* optional name of the goal to be displayed *)
}

(* access primitive *)
let hyps gl = gl.content.Evd.evar_hyps
let concl gl = gl.content.Evd.evar_concl
let name gl = gl.name


(* Builds a new goal named [name] with hypotheses [hyps] and conclusion [gl] *)
let build ?name ~hyps ~concl =
  { content = Evd.make_evar hyps concl ;
    name = name
  }

(* builds a goal out of an evar_info, not quite meant to be exported *)
let of_info ?name evi = 
  { content = evi ;
    name = name
  }

(* return type of the Goal.refine function *)
type refinement = { reconstruct: Term.constr array -> Term.constr ;
                    subgoals: goal array ;
                    new_defs: Evd.evar_defs}

(* a pessimistic (i.e : there won't be many positive answers) filter
   over evar_maps *)
let evar_map_filter f evm =
  Evd.fold (fun ev evi r -> 
	      if f ev evi then 
		Evd.add r ev evi 
	      else 
		r
	   ) 
           evm 
           Evd.empty

(* arnaud: à commenter bien sûr *)
let refine defs env check_type step gl =
  (* building an environement containing [env] and [hyps gl] *)
  let env = Environ.reset_with_named_context (hyps gl) env in
  (* if [check_type] is true, then creates a type constraint for the 
     proof-to-be *)
  let tycon = Pretyping.OfType (if check_type then Some (concl gl) else None) in
  (* the [defs] must be passed as a reference, redefs will be modified by
     the [understand_...] procedure *)
  let rdefs = ref defs in
  (* call to [understand_tcc_evars] returns a constr with undefined evars
     these evars will be our new goals *)
  let refine_step = Pretyping.Default.understand_tcc_evars rdefs env tycon step in
  (* [!rdefs] contains the modified evar_defs *)
  let new_defs = !rdefs in
  (* [delta_evars] holds the evars that have been introduced by this
     refinement (but not immediatly solved) *)
  let delta_evars = evar_map_filter (fun ev evi ->
                                      evi.Evd.evar_body = Evd.Evar_empty &&
                                      not (Evd.mem (Evd.evars_of defs) ev)
				   )
                                   (Evd.evars_of new_defs)
  in
  (* [delta_evars] in the shape of an array *)
  let subst_array = Array.of_list (Evd.to_list delta_evars) in
  (* subgoals to return *)
  (* arbaud: et les noms? *)
  let subgoals = Array.map (fun (_, evi) -> of_info evi ) subst_array in
  let subst = (*arnaud: inverse de subst_array*)
  ()
