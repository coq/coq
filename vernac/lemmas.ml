(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to lemma proofs in
   file command.ml, Aug 2009 *)

open CErrors
open Util
open Flags
open Pp
open Names
open Term
open Declarations
open Declareops
open Entries
open Environ
open Nameops
open Globnames
open Decls
open Decl_kinds
open Declare
open Pretyping
open Termops
open Namegen
open Reductionops
open Constrexpr
open Constrintern
open Impargs
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

type 'a declaration_hook = Decl_kinds.locality -> Globnames.global_reference -> 'a
let mk_hook hook = hook
let call_hook fix_exn hook l c =
  try hook l c
  with e when CErrors.noncritical e ->
    let e = CErrors.push e in
    iraise (fix_exn e)

(* Support for mutually proved theorems *)

let retrieve_first_recthm = function
  | VarRef id ->
      (NamedDecl.get_value (Global.lookup_named id),variable_opacity id)
  | ConstRef cst ->
      let cb = Global.lookup_constant cst in
      (Global.body_of_constant_body cb, is_opaque cb)
  | _ -> assert false

let adjust_guardness_conditions const = function
  | [] -> const (* Not a recursive statement *)
  | possible_indexes ->
  (* Try all combinations... not optimal *)
     let env = Global.env() in
     { const with const_entry_body =
        Future.chain ~pure:true const.const_entry_body
        (fun ((body, ctx), eff) ->
          match kind_of_term body with
          | Fix ((nv,0),(_,_,fixdefs as fixdecls)) ->
(*      let possible_indexes =
	List.map2 (fun i c -> match i with Some i -> i | None ->
	  List.interval 0 (List.length ((lam_assum c))))
	  lemma_guard (Array.to_list fixdefs) in
*)
              let add c cb e =
                let exists c e =
                  try ignore(Environ.lookup_constant c e); true
                  with Not_found -> false in 
                if exists c e then e else Environ.add_constant c cb e in
              let env = List.fold_left (fun env { eff } ->
                match eff with
                | SEsubproof (c, cb,_) -> add c cb env
                | SEscheme (l,_) ->
                    List.fold_left (fun e (_,c,cb,_) -> add c cb e) env l)
                env (Safe_typing.side_effects_of_private_constants eff) in
              let indexes =
                search_guard Loc.ghost env
                  possible_indexes fixdecls in
		(mkFix ((indexes,0),fixdecls), ctx), eff
          | _ -> (body, ctx), eff) }

let find_mutually_recursive_statements thms =
    let n = List.length thms in
    let inds = List.map (fun (id,(t,impls,annot)) ->
      let (hyps,ccl) = decompose_prod_assum t in
      let x = (id,(t,impls)) in
      match annot with
      (* Explicit fixpoint decreasing argument is given *)
      | Some (Some (_,id),CStructRec) ->
          let i,b,typ = lookup_rel_id id hyps in
          (match kind_of_term t with
          | Ind ((kn,_ as ind), u) when
              let mind = Global.lookup_mind kn in
              mind.mind_finite == Decl_kinds.Finite && Option.is_empty b ->
              [ind,x,i],[]
          | _ ->
              error "Decreasing argument is not an inductive assumption.")
      (* Unsupported cases *)
      | Some (_,(CWfRec _|CMeasureRec _)) ->
          error "Only structural decreasing is supported for mutual statements."
      (* Cofixpoint or fixpoint w/o explicit decreasing argument *)
      | None | Some (None, CStructRec) ->
      let whnf_hyp_hds = map_rel_context_in_env
        (fun env c -> EConstr.Unsafe.to_constr (fst (whd_all_stack env Evd.empty (EConstr.of_constr c))))
        (Global.env()) hyps in
      let ind_hyps =
        List.flatten (List.map_i (fun i decl ->
          let t = RelDecl.get_type decl in
          match kind_of_term t with
          | Ind ((kn,_ as ind),u) when
                let mind = Global.lookup_mind kn in
                mind.mind_finite <> Decl_kinds.CoFinite && is_local_assum decl ->
              [ind,x,i]
          | _ ->
              []) 0 (List.rev whnf_hyp_hds)) in
      let ind_ccl =
        let cclenv = push_rel_context hyps (Global.env()) in
        let whnf_ccl,_ = whd_all_stack cclenv Evd.empty (EConstr.of_constr ccl) in
        match kind_of_term (EConstr.Unsafe.to_constr whnf_ccl) with
        | Ind ((kn,_ as ind),u) when
              let mind = Global.lookup_mind kn in
              Int.equal mind.mind_ntypes n && mind.mind_finite == Decl_kinds.CoFinite ->
            [ind,x,0]
        | _ ->
            [] in
      ind_hyps,ind_ccl) thms in
    let inds_hyps,ind_ccls = List.split inds in
    let of_same_mutind ((kn,_),_,_) = function ((kn',_),_,_) -> eq_mind kn kn' in
    (* Check if all conclusions are coinductive in the same type *)
    (* (degenerated cartesian product since there is at most one coind ccl) *)
    let same_indccl =
      List.cartesians_filter (fun hyp oks ->
	if List.for_all (of_same_mutind hyp) oks
	then Some (hyp::oks) else None) [] ind_ccls in
    let ordered_same_indccl =
      List.filter (List.for_all_i (fun i ((kn,j),_,_) -> Int.equal i j) 0) same_indccl in
    (* Check if some hypotheses are inductive in the same type *)
    let common_same_indhyp =
      List.cartesians_filter (fun hyp oks ->
	if List.for_all (of_same_mutind hyp) oks
	then Some (hyp::oks) else None) [] inds_hyps in
    let ordered_inds,finite,guard =
      match ordered_same_indccl, common_same_indhyp with
      | indccl::rest, _ ->
	  assert (List.is_empty rest);
          (* One occ. of common coind ccls and no common inductive hyps *)
	  if not (List.is_empty common_same_indhyp) then
	    if_verbose Feedback.msg_info (str "Assuming mutual coinductive statements.");
	  flush_all ();
          indccl, true, []
      | [], _::_ ->
          let () = match same_indccl with
          | ind :: _ ->
            if List.distinct_f ind_ord (List.map pi1 ind)
            then
              if_verbose Feedback.msg_info
                (strbrk
                   ("Coinductive statements do not follow the order of "^
                    "definition, assuming the proof to be by induction."));
            flush_all ()
          | _ -> ()
          in
          let possible_guards = List.map (List.map pi3) inds_hyps in
	  (* assume the largest indices as possible *)
	  List.last common_same_indhyp, false, possible_guards
      | _, [] ->
	  error
            ("Cannot find common (mutual) inductive premises or coinductive" ^
             " conclusions in the statements.")
    in
    (finite,guard,None), ordered_inds

let look_for_possibly_mutual_statements = function
  | [id,(t,impls,None)] ->
      (* One non recursively proved theorem *)
      None,[id,(t,impls)],None
  | _::_ as thms ->
    (* More than one statement and/or an explicit decreasing mark: *)
    (* we look for a common inductive hyp or a common coinductive conclusion *)
    let recguard,ordered_inds = find_mutually_recursive_statements thms in
    let thms = List.map pi2 ordered_inds in
    Some recguard,thms, Some (List.map (fun (_,_,i) -> succ i) ordered_inds)
  | [] -> anomaly (Pp.str "Empty list of theorems.")

(* Saving a goal *)

let save ?export_seff id const cstrs pl do_guard (locality,poly,kind) hook =
  let fix_exn = Future.fix_exn_of const.Entries.const_entry_body in
  try
    let const = adjust_guardness_conditions const do_guard in
    let k = Kindops.logical_kind_of_goal_kind kind in
    let l,r = match locality with
      | Discharge when Lib.sections_are_opened () ->
          let c = SectionLocalDef const in
          let _ = declare_variable id (Lib.cwd(), c, k) in
          (Local, VarRef id)
      | Local | Global | Discharge ->
          let local = match locality with
          | Local | Discharge -> true
          | Global -> false
          in
          let kn =
           declare_constant ?export_seff id ~local (DefinitionEntry const, k) in
          (locality, ConstRef kn) in
    definition_message id;
    Option.iter (Universes.register_universe_binders r) pl;
    call_hook (fun exn -> exn) hook l r
  with e when CErrors.noncritical e ->
    let e = CErrors.push e in
    iraise (fix_exn e)

let default_thm_id = Id.of_string "Unnamed_thm"

let compute_proof_name locality = function
  | Some ((loc,id),pl) ->
      (* We check existence here: it's a bit late at Qed time *)
      if Nametab.exists_cci (Lib.make_path id) || is_section_variable id ||
	 locality == Global && Nametab.exists_cci (Lib.make_path_except_section id)
      then
        user_err ~loc  (pr_id id ++ str " already exists.");
      id, pl
  | None ->
      next_global_ident_away default_thm_id (Pfedit.get_all_proof_names ()), None

let save_remaining_recthms (locality,p,kind) norm ctx body opaq i ((id,pl),(t_i,(_,imps))) =
  let t_i = norm t_i in
  match body with
  | None ->
      (match locality with
      | Discharge ->
          let impl = false in (* copy values from Vernacentries *)
          let k = IsAssumption Conjectural in
          let c = SectionLocalAssum ((t_i,ctx),p,impl) in
	  let _ = declare_variable id (Lib.cwd(),c,k) in
          (Discharge, VarRef id,imps)
      | Local | Global ->
          let k = IsAssumption Conjectural in
          let local = match locality with
          | Local -> true
          | Global -> false
          | Discharge -> assert false
          in
          let ctx = Univ.ContextSet.to_context ctx in
          let decl = (ParameterEntry (None,p,(t_i,ctx),None), k) in
          let kn = declare_constant id ~local decl in
          (locality,ConstRef kn,imps))
  | Some body ->
      let body = norm body in
      let k = Kindops.logical_kind_of_goal_kind kind in
      let rec body_i t = match kind_of_term t with
        | Fix ((nv,0),decls) -> mkFix ((nv,i),decls)
        | CoFix (0,decls) -> mkCoFix (i,decls)
        | LetIn(na,t1,ty,t2) -> mkLetIn (na,t1,ty, body_i t2)
        | Lambda(na,ty,t) -> mkLambda(na,ty,body_i t)
        | App (t, args) -> mkApp (body_i t, args)
        | _ -> anomaly Pp.(str "Not a proof by induction: " ++ Printer.pr_constr body) in
      let body_i = body_i body in
      match locality with
      | Discharge ->
          let const = definition_entry ~types:t_i ~opaque:opaq ~poly:p 
	    ~univs:(Univ.ContextSet.to_context ctx) body_i in
	  let c = SectionLocalDef const in
	  let _ = declare_variable id (Lib.cwd(), c, k) in
          (Discharge,VarRef id,imps)
      | Local | Global ->
        let ctx = Univ.ContextSet.to_context ctx in
        let local = match locality with
        | Local -> true
        | Global -> false
        | Discharge -> assert false
        in
        let const =
	  Declare.definition_entry ~types:t_i ~poly:p ~univs:ctx ~opaque:opaq body_i
	in
        let kn = declare_constant id ~local (DefinitionEntry const, k) in
        (locality,ConstRef kn,imps)

let save_hook = ref ignore
let set_save_hook f = save_hook := f

let save_named ?export_seff proof =
  let id,const,(cstrs,pl),do_guard,persistence,hook = proof in
  save ?export_seff id const cstrs pl do_guard persistence hook

let check_anonymity id save_ident =
  if not (String.equal (atompart_of_id id) (Id.to_string (default_thm_id))) then
    error "This command can only be used for unnamed theorem."

let save_anonymous ?export_seff proof save_ident =
  let id,const,(cstrs,pl),do_guard,persistence,hook = proof in
  check_anonymity id save_ident;
  save ?export_seff save_ident const cstrs pl do_guard persistence hook

let save_anonymous_with_strength ?export_seff proof kind save_ident =
  let id,const,(cstrs,pl),do_guard,_,hook = proof in
  check_anonymity id save_ident;
  (* we consider that non opaque behaves as local for discharge *)
  save ?export_seff save_ident const cstrs pl do_guard
      (Global, const.const_entry_polymorphic, Proof kind) hook

(* Admitted *)

let warn_let_as_axiom =
  CWarnings.create ~name:"let-as-axiom" ~category:"vernacular"
                   (fun id -> strbrk "Let definition" ++ spc () ++ pr_id id ++
                                spc () ++ strbrk "declared as an axiom.")

let admit (id,k,e) pl hook () =
  let kn = declare_constant id (ParameterEntry e, IsAssumption Conjectural) in
  let () = match k with
  | Global, _, _ -> ()
  | Local, _, _ | Discharge, _, _ -> warn_let_as_axiom id
  in
  let () = assumption_message id in
  Option.iter (Universes.register_universe_binders (ConstRef kn)) pl;
  call_hook (fun exn -> exn) hook Global (ConstRef kn)

(* Starting a goal *)

let start_hook = ref ignore
let set_start_hook = (:=) start_hook


let get_proof proof do_guard hook opacity =
  let (id,(const,univs,persistence)) =
    Pfedit.cook_this_proof proof
  in
  id,{const with const_entry_opaque = opacity},univs,do_guard,persistence,hook

let check_exist =
  List.iter (fun (loc,id) ->
    if not (Nametab.exists_cci (Lib.make_path id)) then
        user_err ~loc  (pr_id id ++ str " does not exist.")
  )

let universe_proof_terminator compute_guard hook =
  let open Proof_global in
  make_terminator begin function
  | Admitted (id,k,pe,(ctx,pl)) ->
      admit (id,k,pe) pl (hook (Some ctx)) ();
      Feedback.feedback Feedback.AddedAxiom
  | Proved (opaque,idopt,proof) ->
      let is_opaque, export_seff, exports = match opaque with
        | Vernacexpr.Transparent -> false, true, []
        | Vernacexpr.Opaque None -> true, false, []
        | Vernacexpr.Opaque (Some l) -> true, true, l in
      let proof = get_proof proof compute_guard
	(hook (Some (fst proof.Proof_global.universes))) is_opaque in
      begin match idopt with
      | None -> save_named ~export_seff proof
      | Some ((_,id),None) -> save_anonymous ~export_seff proof id
      | Some ((_,id),Some kind) -> 
          save_anonymous_with_strength ~export_seff proof kind id
      end;
      check_exist exports
  end

let standard_proof_terminator compute_guard hook =
  universe_proof_terminator compute_guard (fun _ -> hook)

(* Default proof mode, to be set at the beginning of proofs for
   programs that cannot be statically classified. *)
let default_proof_mode = ref "No"
let get_default_proof_mode () = !default_proof_mode
let set_default_proof_mode mn = default_proof_mode := mn

let _ =
  Goptions.declare_string_option {Goptions.
    optsync = true ;
    optdepr = false;
    optname = "default proof mode" ;
    optkey = ["Default";"Proof";"Mode"] ;
    optread = get_default_proof_mode;
    optwrite = set_default_proof_mode;
  }


let start_proof id ?pl kind sigma ?terminator ?sign c ?init_tac ?(compute_guard=[]) hook =
  let terminator = match terminator with
  | None -> standard_proof_terminator compute_guard hook
  | Some terminator -> terminator compute_guard hook
  in
  let sign =
    match sign with
    | Some sign -> sign
    | None -> initialize_named_context_for_proof ()
  in
  !start_hook c;
  Pfedit.start_proof id ?pl kind sigma sign c ?init_tac terminator

let start_proof_univs id ?pl kind sigma ?terminator ?sign c ?init_tac ?(compute_guard=[]) hook =
  let terminator = match terminator with
  | None -> universe_proof_terminator compute_guard hook
  | Some terminator -> terminator compute_guard hook
  in
  let sign = 
    match sign with
    | Some sign -> sign
    | None -> initialize_named_context_for_proof ()
  in
  !start_hook c;
  Pfedit.start_proof id ?pl kind sigma sign c ?init_tac terminator

let rec_tac_initializer finite guard thms snl =
  if finite then
    match List.map (fun ((id,_),(t,_)) -> (id,EConstr.of_constr t)) thms with
    | (id,_)::l -> Tactics.mutual_cofix id l 0
    | _ -> assert false
  else
    (* nl is dummy: it will be recomputed at Qed-time *)
    let nl = match snl with 
     | None -> List.map succ (List.map List.last guard)
     | Some nl -> nl
    in match List.map2 (fun ((id,_),(t,_)) n -> (id,n, EConstr.of_constr t)) thms nl with
       | (id,n,_)::l -> Tactics.mutual_fix id n l 0
       | _ -> assert false

let start_proof_with_initialization kind ctx recguard thms snl hook =
  let intro_tac (_, (_, (ids, _))) =
    Tacticals.New.tclMAP (function
    | Name id -> Tactics.intro_mustbe_force id
    | Anonymous -> Tactics.intro) (List.rev ids) in
  let init_tac,guard = match recguard with
  | Some (finite,guard,init_tac) ->
      let rec_tac = rec_tac_initializer finite guard thms snl in
      Some (match init_tac with
        | None -> 
            if Flags.is_auto_intros () then 
              Tacticals.New.tclTHENS rec_tac (List.map intro_tac thms)
            else
              rec_tac
        | Some tacl ->
            Tacticals.New.tclTHENS rec_tac
            (if Flags.is_auto_intros () then
              List.map2 (fun tac thm -> Tacticals.New.tclTHEN tac (intro_tac thm)) tacl thms
            else
              tacl)),guard
  | None ->
      let () = match thms with [_] -> () | _ -> assert false in
      (if Flags.is_auto_intros () then Some (intro_tac (List.hd thms)) else None), [] in
  match thms with
  | [] -> anomaly (Pp.str "No proof to start")
  | ((id,pl),(t,(_,imps)))::other_thms ->
      let hook ctx strength ref =
        let ctx = match ctx with
        | None -> Evd.empty_evar_universe_context
        | Some ctx -> ctx
        in
        let other_thms_data =
          if List.is_empty other_thms then [] else
            (* there are several theorems defined mutually *)
            let body,opaq = retrieve_first_recthm ref in
            let subst = Evd.evar_universe_context_subst ctx in
            let norm c = Universes.subst_opt_univs_constr subst c in
	    let ctx = UState.context_set (*FIXME*) ctx in
	    let body = Option.map norm body in
            List.map_i (save_remaining_recthms kind norm ctx body opaq) 1 other_thms in
        let thms_data = (strength,ref,imps)::other_thms_data in
        List.iter (fun (strength,ref,imps) ->
	  maybe_declare_manual_implicits false ref imps;
	  call_hook (fun exn -> exn) hook strength ref) thms_data in
      start_proof_univs id ?pl kind ctx (EConstr.of_constr t) ?init_tac (fun ctx -> mk_hook (hook ctx)) ~compute_guard:guard

let start_proof_com ?inference_hook kind thms hook =
  let env0 = Global.env () in
  let levels = Option.map snd (fst (List.hd thms)) in 
  let evdref = ref (match levels with
		    | None -> Evd.from_env env0
		    | Some l -> Evd.from_ctx (Evd.make_evar_universe_context env0 l))
  in
  let thms = List.map (fun (sopt,(bl,t,guard)) ->
    let impls, ((env, ctx), imps) = interp_context_evars env0 evdref bl in
    let t', imps' = interp_type_evars_impls ~impls env evdref t in
    let flags = all_and_fail_flags in
    let flags = { flags with use_hook = inference_hook } in
    evdref := solve_remaining_evars flags env !evdref Evd.empty;
    let ids = List.map RelDecl.get_name ctx in
      (compute_proof_name (pi1 kind) sopt,
      (EConstr.Unsafe.to_constr (nf_evar !evdref (EConstr.it_mkProd_or_LetIn t' ctx)),
       (ids, imps @ lift_implicits (List.length ids) imps'),
       guard)))
    thms in
  let recguard,thms,snl = look_for_possibly_mutual_statements thms in
  let evd, nf = Evarutil.nf_evars_and_universes !evdref in
  let thms = List.map (fun (n, (t, info)) -> (n, (nf t, info))) thms in
  let () =
    match levels with
    | None -> ()
    | Some l -> ignore (Evd.universe_context evd ?names:l)
  in
  let evd =
    if pi2 kind then evd
    else (* We fix the variables to ensure they won't be lowered to Set *)
      Evd.fix_undefined_variables evd
  in
    start_proof_with_initialization kind evd recguard thms snl hook


(* Saving a proof *)

let keep_admitted_vars = ref true

let _ =
  let open Goptions in
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "keep section variables in admitted proofs";
      optkey   = ["Keep"; "Admitted"; "Variables"];
      optread  = (fun () -> !keep_admitted_vars);
      optwrite = (fun b -> keep_admitted_vars := b) }

let save_proof ?proof = function
  | Vernacexpr.Admitted ->
      let pe =
        let open Proof_global in
        match proof with
        | Some ({ id; entries; persistence = k; universes }, _) ->
            if List.length entries <> 1 then
              error "Admitted does not support multiple statements";
            let { const_entry_secctx; const_entry_type } = List.hd entries in
            if const_entry_type = None then
              error "Admitted requires an explicit statement";
            let typ = Option.get const_entry_type in
            let ctx = Evd.evar_context_universe_context (fst universes) in
            let sec_vars = if !keep_admitted_vars then const_entry_secctx else None in
            Admitted(id, k, (sec_vars, pi2 k, (typ, ctx), None), universes)
        | None ->
            let pftree = Pfedit.get_pftreestate () in
            let id, k, typ = Pfedit.current_proof_statement () in
            let typ = EConstr.Unsafe.to_constr typ in
            let universes = Proof.initial_euctx pftree in
            (* This will warn if the proof is complete *)
            let pproofs, _univs =
              Proof_global.return_proof ~allow_partial:true () in
            let sec_vars =
              if not !keep_admitted_vars then None
              else match  Pfedit.get_used_variables(), pproofs with
              | Some _ as x, _ -> x
              | None, (pproof, _) :: _ -> 
                  let env = Global.env () in
                  let ids_typ = Environ.global_vars_set env typ in
                  let ids_def = Environ.global_vars_set env pproof in
                  Some (Environ.keep_hyps env (Idset.union ids_typ ids_def))
              | _ -> None in
	    let names = Pfedit.get_universe_binders () in
            let evd = Evd.from_ctx universes in
            let binders, ctx = Evd.universe_context ?names evd in
            Admitted(id,k,(sec_vars, pi2 k, (typ, ctx), None),
		     (universes, Some binders))
      in
      Proof_global.apply_terminator (Proof_global.get_terminator ()) pe
  | Vernacexpr.Proved (is_opaque,idopt) ->
      let (proof_obj,terminator) =
        match proof with
        | None ->
            Proof_global.close_proof ~keep_body_ucst_separate:false (fun x -> x)
        | Some proof -> proof
      in
      (* if the proof is given explicitly, nothing has to be deleted *)
      if Option.is_empty proof then Pfedit.delete_current_proof ();
      Proof_global.(apply_terminator terminator (Proved (is_opaque,idopt,proof_obj)))

(* Miscellaneous *)

let get_current_context () =
  Pfedit.get_current_context ()

