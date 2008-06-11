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
  itags: int list;         (* Heriditary internal tags, used to
			      keep some track of inheritance *)
  tags : string list       (* Heriditary? tags to be displayed *)
}

(* access primitive *)
(* invariant : [e] must exist in [em] *)
let content evars { content = e } = Evd.find evars e
(* let name { name = n } = n*)


(* arnaud: commentaire ? *)
(* Builds a new goal named [name] with evar [e] *)
let build e =
  { content = e ;
    itags = [];
    tags = []
  }

(* Builds a new goal with content evar [e] and 
   inheriting from goal [gl]*)
let descendent gl e =
  { gl with content = e}

(* Returns [true] if the goal has been partially resolved. *)
let is_defined evars { content = e } = Evd.is_defined evars e

(*** Goal tactics ***)



(* return type of the excution of goal tactics *)
(* it contains the new subgoals to produce, and the definitions of
   the evars to instantiate *)
type proof_step = { subgoals: goal list ;
                    new_defs: Evd.evar_defs }



(* type of the base elements of the goal API.*)
(* it has an extra evar_info with respect to what would be expected,
   it is supposed to be the evar_info of the goal in the evar_defs.
   The idea is that it is computed by the [run] function as an 
   optimisation, since it will generaly not change during the 
   evaluation. As a matter of fact it should only change as far
   as caching is concerned, which is of no concern for the tactics
   themselves. *)
type 'a sensitive = 
    Environ.env -> Evd.evar_defs ref -> goal -> Evd.evar_info -> 'a



(* type of constr with holes manipulated by the API *)
type open_constr = {
  me: constr;
  my_evars: Evd.evar list
}

let constr_of_open_constr { me=c } = c
let open_of_closed c = { me = c; my_evars = []}
let make_open_constr c el = { me = c ; my_evars = el }
(* arnaud: pas bonne idée, le defs doit changer..
   au pire je peux le faire dans la monade sensitive, 
   mais ça me paraît casse-gueule
   Je ne sais plus à quoi c'est utile de toute façon
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

(* This is a tactic which does nothing. Its main purpose
   is to enforce a full duality betweens [Proofview.tactic]-s
   and [Goal.tactic]-s.
   Indeed, given this [null] tactic, [Proofview. will know
   how to transform its tactics to [Goal.tactic].*)
let null _ rdefs gl _ =
  { subgoals = [gl] ; new_defs = !rdefs }


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
  let subgoals = List.map (descendent gl) (List.rev step.my_evars) in
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
  let (cleared_evar,_) = Term.destEvar clearing_constr in
  let cleared_goal = descendent gl cleared_evar in
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
  let (new_evar,_) = destEvar new_constr in
  let new_goal = descendent gl new_evar in
  rdefs := Evd.evar_define gl.content new_constr defs';
  { subgoals = [new_goal] ;
    new_defs = !rdefs
  }




(*** Sensitive expressions & Tacticals ***)


(* arnaud: peut-être pas besoin de cond/map/map2 ? *)
(* if then else on sensitive expressions *)
let cond b ~thn ~els env rdefs goal info =
  if b env rdefs goal info then
    thn env rdefs goal info
  else 
    els env rdefs goal info

(* monadic bind on sensitive expressions *)
let bind e f env rdefs goal info =
  f (e env rdefs goal info) env rdefs goal info

(* monadic return on sensitive expressions *)
let return v _ _ _ _ = v

(* changes a list of sensitive expressions into a sensitive list. *)
let sensitive_list l env rdefs goal info = 
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


(* This function takes an [constr] with metas, and introduces
   a evar for each meta. The metas must be casted and 
   pairwise distinct. *)
let process_typed_metas t env rdefs goal info =
  (* uses an external reference as an accumulator to be able to use
     the [map_constr] idiom *)
  let acc = ref [] in
  let rec process_typed_metas t env =
    match kind_of_term t with
    | Meta _ -> 
	Util.anomaly "Goal.process_typed_metas: fed with an uncasted meta"
    | Cast (c, k, t) when isMeta c ->
	let new_c = Evarutil.e_new_evar rdefs env t in
	let (e,_) = destEvar new_c in
	acc := e::!acc;
	mkCast (c, k, t)
    | Prod (n, t, c) -> 
	let deep_env = match n with
	               | Names.Anonymous -> env
		       | Names.Name i -> Environ.push_named (i,None,t) env
	in
	mkProd (n, process_typed_metas t env, process_typed_metas c deep_env)
    | Lambda (n, t, c) ->
	let deep_env = match n with
	               | Names.Anonymous -> env
		       | Names.Name i -> Environ.push_named (i,None,t) env
	in
	mkLambda (n, process_typed_metas t env, process_typed_metas c deep_env)
    | LetIn (n,b,t,e) ->
        let new_b = process_typed_metas b env in
	let deep_env = match n with
	               | Names.Anonymous -> env
		       | Names.Name i -> Environ.push_named (i,Some new_b,t) env
	in
	mkLetIn (n, b, process_typed_metas t env, 
		    process_typed_metas e deep_env)
    (* arnaud: do Fix, CoFix, and case!*)
    | Fix _ | CoFix _ -> Util.anomaly "Goal.process_typed_metas:Fix/CoFix:todo"
    (* arnaud: ordre non spécifié = danger ? *)
    | _ -> map_constr (fun t -> process_typed_metas t env) t
  in
  let me = process_typed_metas t env in
  { me = me;
    my_evars = !acc
  }

(*** Stuff for the apply tactics ***)



(* Replaces the metas of a goal by evars. [apply] and [eapply]
   do unification on metas, we need to replace these metas by
   evars to be able to use it in [refine]. *)
(* These functions expectingly respect the invariant that 
   the evars in [my_evars] are given in decreasing order. *)
(* arnaud: repasser sur les cas "cast" pour éviter de casser
   des vm_cast. *)
let rec process_apply_case_metas ot ty env rdefs goal info =
  fst (main_process_apply_case_metas ot ty env rdefs goal info)
and main_process_apply_case_metas ot ty env rdefs goal info =
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
	main_process_apply_case_metas { ot with me=t } ty' env rdefs goal info
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
      (* arnaud: original: check_conv_leq_goal env sigma trm conclty' conclty;*)
      let sigma = Evd.evars_of !rdefs in
      if not (Reductionops.is_conv_leq env sigma ty ty') then
	Util.anomaly "Goal.main_process_metas: mettre une vrai erreur(3)"
      else
	let new_ot = { me = Term.mkApp (ot'.me, (Array.of_list l')) ;
		       my_evars = o' }
	in
	( new_ot , ty')
  | Case (k,p,c,lf) ->
      let (ip,ic,evars,lbrty,ty') = 
	process_case_metas ot.my_evars p c env rdefs goal info
      in
      (* arnaud: original: check_conv_leq_goal env sigma trm conclty' conclty; *)
      if not (Reductionops.is_conv_leq env (Evd.evars_of !rdefs) ty ty') then
	Util.anomaly "Goal.main_process_metas: mettre une vrai erreur(4)"
      else
	let (ilf,new_evars) = 
	  Util.array_fold_right2
            (fun ty fi (l,evars) -> 
	       let { me = me ; my_evars = new_evars } = 
		 fst (main_process_apply_case_metas {me=fi;my_evars=evars} ty
			                             env rdefs goal info) 
	       in
		 (me::l,new_evars)
	    )
	    lbrty lf ([] , evars)
	in
	({ me = Term.mkCase(k,ip,ic,Array.of_list ilf) ; 
	   my_evars = new_evars } ,
	   ty')
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

    | Cast (t,_, ty) ->
	let sigma = Evd.evars_of !rdefs in
	check_typability env sigma ty;
	main_process_apply_case_metas { ot with me=t } ty env rdefs goal info

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

    | Case (k,p,c,lf) ->
	let (ip,ic,evars,lbrty,ty') = 
	  process_case_metas ot.my_evars p c env rdefs goal info 
	in
	let (ilf,new_evars) = 
	  Util.array_fold_right2
            (fun ty fi (l,evars) -> 
	       let { me = me ; my_evars = new_evars } = 
		 fst (main_process_apply_case_metas {me=fi;my_evars=evars} ty
			                             env rdefs goal info) 
	       in
		 (me::l,new_evars)
	    )
	    lbrty lf ([] , evars)
	in
	({ me = Term.mkCase(k,ic,ip,Array.of_list ilf) ; 
	   my_evars = new_evars } ,
	   ty')
    | _ -> ot, 
        let sigma = Evd.evars_of !rdefs in
	Retyping.get_type_of env sigma (ot.me)(* arnaud: original: goal_type_of env sigma trm *)

and process_case_metas es p c env rdefs goal info =
  let oc = { me = c ; my_evars = es } in
  let { me = ic; my_evars = es } , ct = 
    process_head_metas oc env rdefs goal info 
  in 
  let op = { me = p ; my_evars = es } in
  let { me = ip; my_evars = es } , pt = 
    process_head_metas op env rdefs goal info 
  in
  let pj = {Environ.uj_val=p; Environ.uj_type=pt} in 
  let indspec =
    try Inductiveops.find_mrectype env (Evd.evars_of !rdefs) ct
    with Not_found -> 
      Util.anomaly "Goal.process_case_metas: the impossible happened" 
  in
  let (lbrty,conclty) =
    Inductiveops.type_case_branches_with_names env indspec pj c in
  (ip,ic,es,lbrty,conclty)


and process_arg_metas l acc funty env rdefs goal info =
  match l with
  | [] -> [],acc,funty
  | harg::tlargs as allargs ->
      let sigma = Evd.evars_of !rdefs in
      let t = Reductionops.whd_betadeltaiota env sigma funty in
      match kind_of_term t with
	| Prod (_,c1,b) ->
	    let (ot',hargty) = main_process_apply_case_metas 
	                                          { me = harg; my_evars = acc }
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

(* Primitives for the tactic [change] *)
let convert_hyp check (id,b,bt as d) envv rdefs gl info =
  let env = env envv rdefs gl info in
  let sigma = Evd.evars_of !rdefs in
  (* This function substitutes the new type and body definitions
     in the appropriate variable when used with {!Environ.apply_hyps}. *)
  let replace_function =
    (fun _ (_,c,ct) _ ->
       if check && not (Reductionops.is_conv env sigma bt ct) then
	 Util.error ("Incorrect change of the type of "^(Names.string_of_id id));
       if check && not (Option.Misc.compare (Reductionops.is_conv env sigma) b c) then
	 Util.error ("Incorrect change of the body of "^(Names.string_of_id id));
       d)
  in
  (* Modified named context. *)
  let new_hyps = 
    Environ.apply_to_hyp (hyps envv rdefs gl info) id replace_function
  in  
  let new_env = Environ.reset_with_named_context new_hyps envv in
  let new_constr = 
    Evarutil.e_new_evar rdefs new_env (concl envv rdefs gl info)
  in
  let (new_evar,_) = Term.destEvar new_constr in
  let new_goal = descendent gl new_evar in
  rdefs := Evd.evar_define gl.content new_constr !rdefs;
  { subgoals = [new_goal] ;
    new_defs = !rdefs
  }
  
let convert_concl check cl' envv rdefs gl info =
  let env = env envv rdefs gl info in
  let sigma = Evd.evars_of !rdefs in
  let cl = concl envv rdefs gl info in
  check_typability env sigma cl';
  if (not check) || Reductionops.is_conv_leq env sigma cl' cl then
    let new_constr = 
      Evarutil.e_new_evar rdefs env cl' 
    in
    let (new_evar,_) = Term.destEvar new_constr in
    let new_goal = descendent gl new_evar in
    rdefs := Evd.evar_define gl.content new_constr !rdefs;
    { subgoals = [new_goal] ;
      new_defs = !rdefs
    }
  else
    Util.error "convert-concl rule passed non-converting term"

(* Auxiliary functions for primitive MOVE tactic
 *
 * [move_after with_dep toleft (left,(hfrom,typfrom),right) hto] moves
 * hyp [hfrom] just after the hyp [hto] which belongs to the hyps on the 
 * left side [left] of the full signature if [toleft=true] or to the hyps 
 * on the right side [right] if [toleft=false].
 * If [with_dep] then dependent hypotheses are moved accordingly. *)

let split_sign hfrom hto l =
  let rec splitrec left toleft = function
    | [] -> Util.error ("No such hypothesis : " ^ (Names.string_of_id hfrom))
    | (hyp,c,typ) as d :: right ->
      	if hyp = hfrom then 
	  (left,right,d,toleft) 
      	else 
	  splitrec (d::left) (toleft or (hyp = hto)) right
  in 
    splitrec [] false l


let move_after with_dep toleft (left,(idfrom,_,_ as declfrom),right) hto =
  (* arnaud: Global.env ?? *)
  let env = Global.env() in
  let test_dep (hyp,c,typ as d) (hyp2,c,typ2 as d2) =
    if toleft
    then Termops.occur_var_in_decl env hyp2 d
    else Termops.occur_var_in_decl env hyp d2
  in
  let rec moverec first middle = function
    | [] -> Util.error ("No such hypothesis : " ^ (Names.string_of_id hto))
    | (hyp,_,_) as d :: right ->
	let (first',middle') =
      	  if List.exists (test_dep d) middle then 
	    if with_dep & (hyp <> hto) then 
	      (first, d::middle)
            else 
	      Util.error 
		("Cannot move "^(Names.string_of_id idfrom)^" after "
		 ^(Names.string_of_id hto)
		 ^(if toleft then ": it occurs in " else ": it depends on ")
		 ^(Names.string_of_id hyp))
          else 
	    (d::first, middle)
	in
      	if hyp = hto then 
	  (List.rev first')@(List.rev middle')@right
      	else 
	  moverec first' middle' right
  in
  if toleft then 
    let right = 
      List.fold_right Environ.push_named_context_val right Environ.empty_named_context_val in
    List.fold_left (fun sign d -> Environ.push_named_context_val d sign)
      right (moverec [] [declfrom] left) 
  else 
    let right = 
      List.fold_right Environ.push_named_context_val
	(moverec [] [declfrom] right) Environ.empty_named_context_val in
    List.fold_left (fun sign d -> Environ.push_named_context_val d sign)
      right left

(* arnaud: à commenter *)
let move_hyp withdep hfrom hto env rdefs gl info =
  let sign = info.Evd.evar_hyps in
  let (left,right,declfrom,toleft) = 
    split_sign hfrom hto (Environ.named_context_of_val sign) 
  in
  let hyps' = 
    move_after withdep toleft (left,declfrom,right) hto 
  in
  let env' = Environ.reset_with_named_context hyps' env in
  let cl = info.Evd.evar_concl in
  let new_constr = Evarutil.e_new_evar rdefs env' cl in
  let (new_evar,_) = Term.destEvar new_constr in
  let new_goal = descendent gl new_evar in
  rdefs := Evd.evar_define gl.content new_constr !rdefs;
  { subgoals = [new_goal] ;
    new_defs = !rdefs
  }


(*** Tag related things ***)

(* The [Goal.freeze] primitive is the main component of the tactic monad's
   (from the Proofview module) [Proofview.freeze].
   Precisely [Goal.freeze gl] returns a pair [ ( g' , i ) ], where [g'] is
   a goal identical to [gl] except that it has an additional hereditary
   internal tag [i].*)
let freeze gl = 
  let unique_tag = gl.content in
  { gl with itags = unique_tag::gl.itags }   ,  unique_tag

(* A [has_itag i] is a [bool Goal.sensitive] which is true inside
   the goals which have the internal tag [i]. *)
let has_itag i _ _ gl _ =
  List.mem i gl.itags

(*** Useful sensitive constant ***)

(* The following few constants, despite being definable, are very
   commonly used, sharing them from here, improves memory and 
   speed *)

(* [Goal.strue] is [Goal.return true] *)
let strue = return true

(* [Goal.sfalse] is [Goal.return false] *)
let sfalse = return false

(* [Goal.sNone] is [Goal.return None] *)
let sNone = return None

(* [Goal.sNil] is [Goal.return []] *)
let sNil = return []
