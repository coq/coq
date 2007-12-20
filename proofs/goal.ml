(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term

(* This module implements the abstract interface to goals *)
(* A general invariant of the module, is that a goal whose associated 
   evar is defined in the current evar_defs, should not be accessed. *)

(* type of the goals *)
type goal = {
  content : Evd.evar;      (* Corresponding evar. Allows to retrieve
			      logical information once put together
			      with an evar_map. *)
  name : string option     (* Optional name of the goal to be displayed *)
}

(* access primitive *)
(* invariant : [e] must exist in [em] *)
let content evars { content = e } = Evd.find evars e
let name { name = n } = n


(* Builds a new goal named [name] with evar [e] *)
let build ?name e =
  { content = e ;
    name = name
  }


(* Returns [true] if the goal has been partially resolved. *)
let is_defined evars { content = e } = Evd.is_defined evars e


(*** Refine tactic ***)


(* return type of the Goal.refine function *)
(* it contains the new subgoals to produce, a function to reconstruct
   the proof to the current goal knowing the result of the subgoals,
   the type and constraint information about the evars of the proof
   (which has been extended with new ones), and the definitions of
   the evars to instantiate *)
type refinement = { subgoals: goal list ;
                    new_defs: Evd.evar_defs }

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


(* arnaud: à commenter un brin  *)
let refine defs env check_type step gl =
  (* retrieving the current [evar_info] associated to [gl] *)
  let info = content (Evd.evars_of defs) gl in
  (* building an environement containing [env] and the hypotheses of [gl] *)
  let env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
  (* if [check_type] is true, then creates a type constraint for the 
     proof-to-be *)
  let tycon = Pretyping.OfType (Option.init check_type (Evd.evar_concl info)) in
  (* the [defs] must be passed as a reference, [rdefs] will be modified by
     the [understand_...] procedure *)
  let rdefs = ref defs in
  (* call to [understand_tcc_evars] returns a constr with undefined evars
     these evars will be our new goals *)
  let refine_step = Pretyping.Default.understand_tcc_evars rdefs env tycon step
  in
  (* [!rdefs] contains the evar_defs outputed by  [understand_...] *)
  let post_defs = !rdefs in
  (* [delta_evars] holds the evars that have been introduced by this
     refinement (but not immediatly solved) *)
  (* arnaud: probablement à speeder up un bit *)
  (* arnaud: il va probablement même falloir renvoyer les existentials.
     Parce que sinon c'est trop laid à trouver ! *)
  let delta_evars = evar_map_filter (fun ev evi ->
                                      evi.Evd.evar_body = Evd.Evar_empty &&
                                      (* arnaud: factoriser la map ?*)
                                      not (Evd.mem (Evd.evars_of defs) ev)
				   )
                                   (Evd.evars_of post_defs)
  in
  (* [delta_evars] in the shape of a list *)
  let subst_list = Evd.to_list delta_evars in
  (* subgoals to return *)
  (* arnaud: et les noms? *)
  let subgoals = List.map (fun (e, _) -> build e) subst_list in
  (* creates the new [evar_defs] by defining the evar of the current goal
     as being [refine_step]. *)
  let new_defs = Evd.evar_define gl.content refine_step post_defs in
  { subgoals = subgoals ;
    new_defs = new_defs ;
  }



(*** Other tactics ***)

(* Implements the clear tactics *)
let clear indents defs gl =
  let rdefs = ref defs in
  
(* arnaud: remplacer par un "print goal" I guess suppose. 
(* This function returns a new goal where the evars have been
   instantiated according to an evar_map *)
(* arnaud Evarutil ou Reductionops ou Pretype_errors ? *)
let instantiate em gl =
  (* note: goals don't have an evar_body *)
  let content = gl.content in
  let instantiate =  Evarutil.nf_evar em in
  { gl with
  
    content = { content with
                (* arnaud: map_named_val est a priori ok: si [t] n'a pas
		   d'evar alors [instantiate t] = [t], sinon [t] n'a
                   pas de forme compilé donc ça reste correct. Commenter
                   dans environ.ml(i) (et pre_env.ml(i)?) si ça fonctionne.*)
		Evd.evar_hyps = Environ.map_named_val instantiate content.Evd.evar_hyps;
		Evd.evar_concl = instantiate content.Evd.evar_concl
	      }
  }
*)
