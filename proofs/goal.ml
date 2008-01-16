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


(* arnaud: à commenter un brin plus *)
let refine env check_type step defs gl =
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

(* arnaud: faut franchement nettoyer tout ça. Ça mérite une réflexion de fond
   mais ya du nettoyage à faire *)

(* arnaud: c'est évidemment faux. Evarutil.clear_hyps_in_evi change toutes
   les evars en les instanciant, ce qui crée des bugs dans les dépendances.
   Dès les phases où ça doit devenir crédible il faudra repenser sérieusement
   la sémantique de ce truc.
   L'idée serait de ne pas instancier les vieilles evars avec de nouveau
   trucs, mais de faire de nouveau trucs instanciés par les vieilles evars.
   Ou bien de demander à l'autre but de suivre l'instanciation du clear.
   Je pense. *)
(* Implements the clear tactic *)
let clear idents defs gl =
  let rdefs = ref defs in
  let info = content (Evd.evars_of defs) gl in
  let cleared_info = Evarutil.clear_hyps_in_evi rdefs info idents in
  let cleared_env = Environ.reset_with_named_context (Evd.evar_hyps cleared_info) 
                                                     Environ.empty_env in
  let cleared_concl = Evd.evar_concl cleared_info in
  let clearing_constr = Evarutil.e_new_evar rdefs cleared_env cleared_concl in
  let cleared_evar = match kind_of_term clearing_constr with
                     | Evar (e,_) -> e
		     | _ -> Util.anomaly "Goal.clear: e_new_evar failure"
  in
  let cleared_goal = build cleared_evar in
  let new_defs = Evd.evar_define gl.content clearing_constr !rdefs in
  { subgoals = [cleared_goal] ;
    new_defs = new_defs
  }

(* arnaud: générer les erreurs en deux temps sans doute ? *)
(* arnaud: qu'est-ce qui doit être failure, et qu'est-ce qui doit juste
   failer de progresser ?*)
(* the four following functions implement the clearbody tactic *)
let apply_to_hyp_and_dependent_on sign id f g =
  try Environ.apply_to_hyp_and_dependent_on sign id f g 
  with Environ.Hyp_not_found -> 
    (*arnaud: if !check then*) Util.error "No such assumption" (*arnaud: error ou pas ?*)
    (*arnaud: ça va avec le !check d'au dessus: else sign*)

let check_typability env sigma c =
  (*arnaud:if !check then*) let _ = Typing.type_of env sigma c in () 

(* arnaud: est-il intéressant de rajouter un no-check flag ? *)
let recheck_typability (what,id) env sigma t =
  try check_typability env sigma t
  with _ ->
    let s = match what with
      | None -> "the conclusion"
      | Some id -> "hypothesis "^(Names.string_of_id id) in
    Util.error (*arnaud: error ou pas ?*)
      ("The correctness of "^s^" relies on the body of "^(Names.string_of_id id))

let remove_hyp_body env sigma id =
  let sign =
    apply_to_hyp_and_dependent_on (Environ.named_context_val env) id
      (fun (_,c,t) _ ->
	match c with
	| None -> Util.error ((Names.string_of_id id)^" is not a local definition") (*arnaud: erroor ou pas ?*)
	| Some c ->(id,None,t))
      (fun (id',c,t as d) sign ->
	((* arnaud: if !check then*)
	  begin 
	    let env = Environ.reset_with_named_context sign env in
	    match c with
	    | None ->  recheck_typability (Some id',id) env sigma t
	    | Some b ->
		let b' = mkCast (b,DEFAULTcast, t) in
		recheck_typability (Some id',id) env sigma b'
	  end;d))
  in
  Environ.reset_with_named_context sign env 

(* arnaud: on fait autant de passe qu'il y a d'hypothèses, ça permet un 
   message d'erreur plus fin, mais c'est un peu lourdingue...*)
let clear_body env idents defs gl =
  let info = content (Evd.evars_of defs) gl in
  let full_env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
  let aux env id = 
     let env' = remove_hyp_body env (Evd.evars_of defs) id in
       (*arnaud: if !check then*) recheck_typability (None,id) env' (Evd.evars_of defs) (Evd.evar_concl info);
       env'
  in
  let new_env = 
    List.fold_left aux full_env idents
  in
  let concl = Evd.evar_concl info in
  let (defs',new_constr) = Evarutil.new_evar defs new_env concl in
  let new_evar = match kind_of_term new_constr with
                     | Evar (e,_) -> e
		     | _ -> Util.anomaly "Goal.clear: e_new_evar failure"
  in
  let new_goal = build new_evar in
  let new_defs = Evd.evar_define gl.content new_constr defs' in
  { subgoals = [new_goal] ;
    new_defs = new_defs
  }

(* arnaud Evarutil ou Reductionops ou Pretype_errors .nf_evar? *)














  
(* arnaud: remplacer par un "print goal" I guess suppose. 
(* This function returns a new goal where the evars have been
   instantiated according to an evar_map *)
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
