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



(*** Goal tactics ***)



(* return type of the excution of goal tactics *)
(* it contains the new subgoals to produce, and the definitions of
   the evars to instantiate *)
type refinement = { subgoals: goal list ;
                    new_defs: Evd.evar_defs }



(* type of the base elements of the goal API.*)
(* it has an extra evar_info with respect to what would be expected,
   it is supposed to be the evar_info of the goal in the evar_defs.
   The idea is that it is computed by the [run] function as an 
   optimisation, since it will generaly not change during the 
   evaluation. As a matter of fact it should only change as far
   as caching is concerned, which is of no concern for the tactics
   themselves. *)
type 'a expression = Environ.env -> Evd.evar_defs ref -> goal -> Evd.evar_info -> 'a


(* type of the goal tactics*)
type tactic = refinement expression

(* type of constr with holes manipulated by the API *)
type open_constr = {
  me: constr;
  my_evars: Evd.evar list
}
let constr_of_open_constr { me=c } = c
let open_of_closed c = { me = c; my_evars = []}
let make_open_constr c el = { me = c ; my_evars = el }
(* arnaud: pas bonne idée, le defs doit changer..
   au pire je peux le faire dans la monade expression, 
   mais ça me paraît casse-gueule
let open_of_weak (sigma,c) = 
  let sigma_list = List.map fst (Evd.to_list sigma) in
  { me = c ; my_evars = List.rev sigma_list }
*)


(* runs a goal tactic on a given goal (knowing the current evar_defs). *)
(* the evar_info corresponding to the goal is computed at once
   as an optimisation (it usually won't change during the evaluation). 
   As a matter of fact it should only change as far as caching is 
   concerned, which is of no concern for the tactics themselves. *)
let run t env defs gl =
  let info = content (Evd.evars_of defs) gl in
  let env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
  let rdefs = ref defs in
  t env rdefs gl info


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

(*arnaud: à déplacer ou du moins à paramètrer. Peut-être à construire
          dans la monade. *)
let open_constr_of_raw check_type rawc env rdefs gl info =
  (* We need to keep trace of what [rdefs] was originally*)
  let init_defs = !rdefs in
  (* if [check_type] is true, then creates a type constraint for the 
     proof-to-be *)
  let tycon = Pretyping.OfType (Option.init check_type (Evd.evar_concl info)) in
  (* call to [understand_tcc_evars] returns a constr with undefined evars
     these evars will be our new goals *)
  let open_constr = Pretyping.Default.understand_tcc_evars rdefs env tycon rawc
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
                                      not (Evd.mem (Evd.evars_of init_defs) ev)
				   )
                                   (Evd.evars_of post_defs)
  in
  (* [delta_evars] in the shape of a list of [evar]-s*)
  let delta_list = List.map fst (Evd.to_list delta_evars) in
  (* arnaud: à nettoyer: peut-être proposer une helper fonction ?
  Evd.make_open_constr ~global_defs: post_defs
                       ~my_evars: delta_list
                       ~me: open_constr
  *)
  (* The variables in [myevars] are supposed to be stored
     in decreasing order. Breaking this invariant might cause
     many things to go wrong. *)
  { me = open_constr ; my_evars = List.rev delta_list }

(* arnaud: à commenter un brin plus *)
let refine step env rdefs gl info =
  (* subgoals to return *)
  (* arnaud: et les noms? *)
  (* The evars in [my_evars] are stored in reverse order.
     It is expectingly better however to display the goal
     in increasing order. *)
  let subgoals = List.map build (List.rev step.my_evars) in
  (* creates the new [evar_defs] by defining the evar of the current goal
     as being [refine_step]. *)
  let new_defs = Evd.evar_define gl.content (step.me) !rdefs in
  rdefs := new_defs; 
  { subgoals = subgoals ;
    new_defs = new_defs ;
  }


(* arnaud: faut franchement nettoyer tout ça. Ça mérite une réflexion de fond
   mais ya du nettoyage à faire *)

(* arnaud: c'est évidemment faux. Evarutil.clear_hyps_in_evi change toutes
   les evars en les instanciant, ce qui crée des bugs dans les dépendances.
   Dès les phases où ça doit devenir crédible il faudra repenser sérieusement
   la sémantique de ce truc.
   L'idée serait de ne pas instancier les vieilles evars avec de nouveau
   trucs, mais de faire de nouveau trucs instanciés par les vieilles evars.
   Ou bien de demander à l'autre but de suivre l'instanciation du clear.
   Je pense.
   - A la réflexion, si un but fait référence à l'evar ?x et qu'on prétend
   (sémantique de clear) qu'on peut le résoudre sans y, alors on prétend aussi
   que y n'a pas d'importance dans ?x. Cependant, on peut enlever ?x avant si
   il faut. Le défaut de ce procédé c'est qu'on modifie des buts auquels on
   n'a censément pas accès à ce moment de l'exécution de cette tactique.
   Il faut donc un moyen de les faire "avancer", (car sinon il vont 
   disparaître). Peut-être une info dans l'evar_info, il est là pour ça
   après tout.
   *)
(* Implements the clear tactic *)
(* arnaud: wrapper les erreurs autour de [clear_in_evi] dans une tactic
   failure, avec une output stream inspirée de l'ancien clear_in_evi *)
let clear idents _ rdefs gl info =
  let cleared_info = Evarutil.clear_in_evi rdefs info idents in
  let cleared_env = Environ.reset_with_named_context (Evd.evar_hyps cleared_info) 
                                                     Environ.empty_env in
  let cleared_concl = Evd.evar_concl cleared_info in
  let clearing_constr = Evarutil.e_new_evar rdefs cleared_env cleared_concl in
  let cleared_evar = match kind_of_term clearing_constr with
                     | Evar (e,_) -> e
		     | _ -> Util.anomaly "Goal.clear: e_new_evar failure"
  in
  let cleared_goal = build cleared_evar in
  rdefs := Evd.evar_define gl.content clearing_constr !rdefs;
  { subgoals = [cleared_goal] ;
    new_defs = !rdefs
  }





(* arnaud: est-il possible de faire plus propre ? *)
(* arnaud: générer les erreurs en deux temps sans doute ? *)
(* arnaud: qu'est-ce qui doit être failure, et qu'est-ce qui doit juste
   failer de progresser ?*)
(* the four following functions implement the clearbody tactic *)
let wrap_apply_to_hyp_and_dependent_on sign id f g =
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
    wrap_apply_to_hyp_and_dependent_on (Environ.named_context_val env) id
      (fun (_,c,t) _ ->
	match c with
	| None -> Util.error ((Names.string_of_id id)^" is not a local definition") (*arnaud: error ou pas ?*)
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
let clear_body idents env rdefs gl info =
  let info = content (Evd.evars_of !rdefs) gl in
  let full_env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
  let aux env id = 
     let env' = remove_hyp_body env (Evd.evars_of !rdefs) id in
       (*arnaud: if !check then*) recheck_typability (None,id) env' (Evd.evars_of !rdefs) (Evd.evar_concl info);
       env'
  in
  let new_env = 
    List.fold_left aux full_env idents
  in
  let concl = Evd.evar_concl info in
  let (defs',new_constr) = Evarutil.new_evar !rdefs new_env concl in
  let new_evar = match kind_of_term new_constr with
                     | Evar (e,_) -> e
		     | _ -> Util.anomaly "Goal.clear: e_new_evar failure"
  in
  let new_goal = build new_evar in
  rdefs := Evd.evar_define gl.content new_constr defs';
  { subgoals = [new_goal] ;
    new_defs = !rdefs
  }



(*** Implementation of the "apply" tactic ***)




(* arnaud Evarutil ou Reductionops ou Pretype_errors .nf_evar? *)




(*** Expressions & Tacticals ***)


(* arnaud: peut-être pas besoin de cond/map/map2 ? *)
(* if then else on expressions *)
let cond b ~thn ~els env rdefs goal info =
  if b env rdefs goal info then
    thn env rdefs goal info
  else 
    els env rdefs goal info

(* monadic bind on expressions *)
let bind e f env rdefs goal info =
  f (e env rdefs goal info) env rdefs goal info

(* monadic return on expressions *)
let return v _ _ _ _ = v

(* changes a list of expressions into an list expression *)
let expr_of_list l env rdefs goal info = 
  List.map (fun x -> x env rdefs goal info) l

(* map combinator which may usefully complete [bind] *)
let map f e env rdefs goal info =
  f (e env rdefs goal info)

(* binary map combinator *)
let map2 f e1 e2 env rdefs goal info =
  f (e1 env rdefs goal info) (e2 env rdefs goal info)


(* [concl] is the conclusion of the current goal *)
let concl _ _ _ info =
  Evd.evar_concl info

(* [hyps] is the [named_context_val] representing the hypotheses
   of the current goal *)
let hyps _ _ _ info =
  Evd.evar_hyps info

(* [env] is the current [Environ.env] containing both the 
   environment in which the proof is ran, and the goal hypotheses *)
let env env _ _ _ = env

(* [defs] is the [Evd.evar_defs] at the current evaluation point *)
let defs _ rdefs _ _ =
  !rdefs






(*** Stuff for the apply tactics ***)



(* Replaces the metas of a goal by evars. [apply] and [eapply]
   do unification on metas, we need to replace these metas by
   evars to be able to use it in [refine]. *)
(* These functions expectingly respect the invariant that 
   the evars in [my_evars] are given in decreasing order. *)
let rec process_metas ot ty env rdefs goal info =
  fst (main_process_metas ot ty env rdefs goal info)
and main_process_metas ot ty env rdefs goal info =
  let hyps = info.Evd.evar_hyps in
  match kind_of_term ot.me with
  | Meta _ ->
      if Termops.occur_meta ty then
	Util.anomaly "Goal.main_process_metas: mettre une vrai erreur"
	(* arnaud: original (à plus ou moins restaurer):
	   (sachant que conclty = ty) :
	   raise (RefinerError (OccurMetaGoal conclty)); *)
      else
	let new_me = Evarutil.e_new_evar rdefs 
	                                 (Environ.reset_with_named_context hyps 
					                                   env)
					 (Reductionops.nf_betaiota ty)
	in
	let (e,_) = Term.destEvar new_me in
        { me = new_me ; my_evars = e::ot.my_evars }, ty
  | Cast (t, _, ty') ->
      let sigma = Evd.evars_of !rdefs in
      check_typability env sigma ty';
      (* arnaud: original: Logic.check_conv_leq_goal: une histoire d'erreur *)
      if not (Reductionops.is_conv_leq env sigma ty ty') then
	Util.anomaly "Goal.main_process_metas: mettre une vrai erreur(2)"
      else
	main_process_metas { ot with me=t } ty' env rdefs goal info
  | App (f,l) ->
      let (ot',hdty) =
	match kind_of_term f with
	| (Ind _ (* needed if defs in Type are polymorphic: | Const _*))
	    when not (Util.array_exists Termops.occur_meta l) (* we could be finer *) ->
	    (* Sort-polymorphism of definition and inductive types *)
	    ot, 
              let sigma = Evd.evars_of !rdefs in
	      Retyping.type_of_global_reference_knowing_parameters env sigma f l
	| _ -> 
	    process_head_metas { ot with me = f} env rdefs goal info
      in
      let (l',o',ty') =
	process_arg_metas (Array.to_list l) 
	                  (ot'.my_evars) 
	                  hdty
	                  env rdefs goal info
      in
	(* arnaud: à nettoyer mk_arggoals sigma goal acc' hdty (Array.to_list l) in*)
      (* arnaud: original: check_conv_leq_goal env sigma trm conclty' conclty;*)
      let sigma = Evd.evars_of !rdefs in
      if not (Reductionops.is_conv_leq env sigma ty ty') then
	Util.anomaly "Goal.main_process_metas: mettre une vrai erreur(3)"
      else
	let new_ot = { me = Term.mkApp (ot'.me, l) ;
		       my_evars = o' }
	in
	( new_ot , ty')
  | Case (_,p,c,lf) ->
      Util.anomaly "Goal.main_process_evars: Case: à restaurer"
      (* arnaud: à restaurer
      let (acc',lbrty,conclty') = process_case_metas sigma goal goalacc p c in
      check_conv_leq_goal env sigma trm conclty' conclty;
      let acc'' = 
	array_fold_left2
          (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
          acc' lbrty lf 
      in
      (acc'',conclty')
      *)
  | _ -> 
      if Termops.occur_meta ot.me then 
	Util.anomaly "Goal.main_process_metas: mettre une vrai erreur (4)"(*arnaud:original :raise (RefinerError (OccurMeta trm));*)
      else
	(* arnaud: original:
	   let t'ty = goal_type_of env sigma trm in
	   check_conv_leq_goal env sigma trm t'ty conclty;
	*)
	let sigma = Evd.evars_of !rdefs in
	let t'ty = Retyping.get_type_of env sigma ot.me in
        if not (Reductionops.is_conv_leq env sigma ty t'ty) then
	  Util.anomaly "Goal.main_process_metas: mettre une vrai erreur (4)"
	else
	  (ot,t'ty)


(* Same as main_process_metas but without knowing the type of the term. 
   Therefore, Metas should be cast. *)

and process_head_metas ot env rdefs goal info =
  let hyps = info.Evd.evar_hyps in
  match kind_of_term ot.me with
    | Cast (c,_, ty) when isMeta c ->
	let sigma = Evd.evars_of !rdefs in
	check_typability env sigma ty;
	let new_me = Evarutil.e_new_evar rdefs 
	                        (Environ.reset_with_named_context hyps env)
	 			(Reductionops.nf_betaiota ty)
	in
	let (e,_) = Term.destEvar new_me in
	{ me=new_me ; my_evars=e::ot.my_evars }, ty
        (* arnaud: à nettoyer 
	(mk_goal hyps (nf_betaiota ty))::goalacc,ty
	*)

    | Cast (t,_, ty) ->
	let sigma = Evd.evars_of !rdefs in
	check_typability env sigma ty;
	main_process_metas { ot with me=t } ty env rdefs goal info

    | App (f,l) ->
	let (ot',hdty) = 
	  if isInd f or isConst f 
	     & not (Util.array_exists Termops.occur_meta l) (* we could be finer *)
	  then
	    ({ot with me=f},
	     let sigma = Evd.evars_of !rdefs in
	     Retyping.type_of_global_reference_knowing_parameters env sigma f l)
	  else 
	    process_head_metas { ot with me=f } env rdefs goal info
	in
	let (l',o',ty') =
	  process_arg_metas (Array.to_list l) 
	                    (ot'.my_evars) 
	                    hdty 
	                    env rdefs goal info
	in
	let new_ot = { me = Term.mkApp (ot'.me, l) ;
		       my_evars = o' }
	in
	( new_ot , ty')
	  (* arnaud: à nettoyer 
	mk_arggoals sigma goal acc' hdty (Array.to_list l)
	  *)

    | Case (_,p,c,lf) ->
	Util.anomaly "Goal.process_head_metas: Case: à restaurer"
	(* arnaud: à restaurer:
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	(acc'',conclty')
	*)

    | _ -> ot, 
        let sigma = Evd.evars_of !rdefs in
	Retyping.get_type_of env sigma (ot.me)(* arnaud: original: goal_type_of env sigma trm *)


and process_arg_metas l acc funty env rdefs goal info =
  match l with
  | [] -> [],acc,funty
  | harg::tlargs as allargs ->
      let sigma = Evd.evars_of !rdefs in
      let t = Reductionops.whd_betadeltaiota env sigma funty in
      match kind_of_term t with
	| Prod (_,c1,b) ->
	    let (ot',hargty) = main_process_metas { me = harg; my_evars = acc }
	                                          c1
						  env rdefs goal info
	    in
	    let (l', acc', ty') = process_arg_metas tlargs (ot'.my_evars)
	                                                   (subst1 harg b)
							   env rdefs goal info
	    in
	    (ot'.me::l', acc', ty')
	| LetIn (_,c1,_,b) ->
	    process_arg_metas allargs acc (subst1 c1 b) env rdefs goal info
	| _ -> Util.anomaly "Goal.process_arg_metas: mettre une vrai erreur"
	    (* arnaud: original: raise (RefinerError (CannotApply (t,harg)))*)

(* arnaud: à nettoyer
let rec mk_refgoals sigma goal goalacc conclty trm =
  let env = evar_env goal in
  let hyps = goal.evar_hyps in
  let mk_goal hyps concl = mk_goal hyps concl goal.evar_extra in
(*
   if  not (occur_meta trm) then
    let t'ty = (unsafe_machine env sigma trm).uj_type in 	
    let _ = conv_leq_goal env sigma trm t'ty conclty in
      (goalacc,t'ty)
  else
*)
  match kind_of_term trm with
    | Meta _ ->
	if occur_meta conclty then
          raise (RefinerError (OccurMetaGoal conclty));
	(mk_goal hyps (nf_betaiota conclty))::goalacc, conclty

    | Cast (t,_, ty) ->
	check_typability env sigma ty;
	check_conv_leq_goal env sigma trm ty conclty;
	mk_refgoals sigma goal goalacc ty t

    | App (f,l) ->
	let (acc',hdty) =
	  match kind_of_term f with
	    | (Ind _ (* needed if defs in Type are polymorphic: | Const _*))
		when not (array_exists occur_meta l) (* we could be finer *) ->
		(* Sort-polymorphism of definition and inductive types *)
		goalacc, 
		type_of_global_reference_knowing_parameters env sigma f l
	    | _ -> 
		mk_hdgoals sigma goal goalacc f
	in
	let (acc'',conclty') =
	  mk_arggoals sigma goal acc' hdty (Array.to_list l) in
	check_conv_leq_goal env sigma trm conclty' conclty;
        (acc'',conclty')

    | Case (_,p,c,lf) ->
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	check_conv_leq_goal env sigma trm conclty' conclty;
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	(acc'',conclty')

    | _ -> 
	if occur_meta trm then raise (RefinerError (OccurMeta trm));
      	let t'ty = goal_type_of env sigma trm in
	check_conv_leq_goal env sigma trm t'ty conclty;
        (goalacc,t'ty)

(* Same as mkREFGOALS but without knowing te type of the term. Therefore,
 * Metas should be casted. *)

and mk_hdgoals sigma goal goalacc trm =
  let env = evar_env goal in
  let hyps = goal.evar_hyps in
  let mk_goal hyps concl = mk_goal hyps concl goal.evar_extra in
  match kind_of_term trm with
    | Cast (c,_, ty) when isMeta c ->
	check_typability env sigma ty;
	(mk_goal hyps (nf_betaiota ty))::goalacc,ty

    | Cast (t,_, ty) ->
	check_typability env sigma ty;
	mk_refgoals sigma goal goalacc ty t

    | App (f,l) ->
	let (acc',hdty) = 
	  if isInd f or isConst f 
	     & not (array_exists occur_meta l) (* we could be finer *)
	  then
	    (goalacc,type_of_global_reference_knowing_parameters env sigma f l)
	  else mk_hdgoals sigma goal goalacc f
	in
	mk_arggoals sigma goal acc' hdty (Array.to_list l)

    | Case (_,p,c,lf) ->
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	(acc'',conclty')

    | _ -> goalacc, goal_type_of env sigma trm

and mk_arggoals sigma goal goalacc funty = function
  | [] -> goalacc,funty
  | harg::tlargs as allargs ->
      let t = whd_betadeltaiota (evar_env goal) sigma funty in
      match kind_of_term t with
	| Prod (_,c1,b) ->
	    let (acc',hargty) = mk_refgoals sigma goal goalacc c1 harg in
	    mk_arggoals sigma goal acc' (subst1 harg b) tlargs
	| LetIn (_,c1,_,b) ->
	    mk_arggoals sigma goal goalacc (subst1 c1 b) allargs
	| _ -> raise (RefinerError (CannotApply (t,harg)))

and mk_casegoals sigma goal goalacc p c =
  let env = evar_env goal in
  let (acc',ct) = mk_hdgoals sigma goal goalacc c in 
  let (acc'',pt) = mk_hdgoals sigma goal acc' p in
  let pj = {uj_val=p; uj_type=pt} in 
  let indspec =
    try find_mrectype env sigma ct
    with Not_found -> anomaly "mk_casegoals" in
  let (lbrty,conclty) =
    type_case_branches_with_names env indspec pj c in
  (acc'',lbrty,conclty)

*)











  
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
