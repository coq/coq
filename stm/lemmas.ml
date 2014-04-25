(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to lemma proofs in
   file command.ml, Aug 2009 *)

open Errors
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

(* Support for mutually proved theorems *)

let retrieve_first_recthm = function
  | VarRef id ->
      (pi2 (Global.lookup_named id),variable_opacity id)
  | ConstRef cst ->
      let cb = Global.lookup_constant cst in
      (body_of_constant cb, is_opaque cb)
  | _ -> assert false

let adjust_guardness_conditions const = function
  | [] -> const (* Not a recursive statement *)
  | possible_indexes ->
  (* Try all combinations... not optimal *)
     let env = Global.env() in
     { const with const_entry_body =
        Future.chain ~greedy:true ~pure:true const.const_entry_body
        (fun (body, eff) ->
          match kind_of_term body with
          | Fix ((nv,0),(_,_,fixdefs as fixdecls)) ->
(*      let possible_indexes =
	List.map2 (fun i c -> match i with Some i -> i | None ->
	  List.interval 0 (List.length ((lam_assum c))))
	  lemma_guard (Array.to_list fixdefs) in
*)
              let indexes =
	        search_guard Loc.ghost env
                  possible_indexes fixdecls in
              mkFix ((indexes,0),fixdecls),  eff
          | _ -> body, eff) }

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
          | Ind (kn,_ as ind) when
              let mind = Global.lookup_mind kn in
              mind.mind_finite && Option.is_empty b ->
              [ind,x,i],[]
          | _ ->
              error "Decreasing argument is not an inductive assumption.")
      (* Unsupported cases *)
      | Some (_,(CWfRec _|CMeasureRec _)) ->
          error "Only structural decreasing is supported for mutual statements."
      (* Cofixpoint or fixpoint w/o explicit decreasing argument *)
      | None | Some (None, CStructRec) ->
      let whnf_hyp_hds = map_rel_context_in_env
        (fun env c -> fst (whd_betadeltaiota_stack env Evd.empty c))
        (Global.env()) hyps in
      let ind_hyps =
        List.flatten (List.map_i (fun i (_,b,t) ->
          match kind_of_term t with
          | Ind (kn,_ as ind) when
                let mind = Global.lookup_mind kn in
                mind.mind_finite && Option.is_empty b ->
              [ind,x,i]
          | _ ->
              []) 0 (List.rev whnf_hyp_hds)) in
      let ind_ccl =
        let cclenv = push_rel_context hyps (Global.env()) in
        let whnf_ccl,_ = whd_betadeltaiota_stack cclenv Evd.empty ccl in
        match kind_of_term whnf_ccl with
        | Ind (kn,_ as ind) when
              let mind = Global.lookup_mind kn in
              Int.equal mind.mind_ntypes n && not mind.mind_finite ->
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
	    if_verbose msg_info (str "Assuming mutual coinductive statements.");
	  flush_all ();
          indccl, true, []
      | [], _::_ ->
          let () = match same_indccl with
          | ind :: _ ->
            if List.distinct_f ind_ord (List.map pi1 ind)
            then
              if_verbose msg_info
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

let save id const do_guard (locality,kind) hook =
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
        let kn = declare_constant id ~local (DefinitionEntry const, k) in
	(locality, ConstRef kn) in
  definition_message id;
  hook l r

let default_thm_id = Id.of_string "Unnamed_thm"

let compute_proof_name locality = function
  | Some (loc,id) ->
      (* We check existence here: it's a bit late at Qed time *)
      if Nametab.exists_cci (Lib.make_path id) || is_section_variable id ||
	 locality == Global && Nametab.exists_cci (Lib.make_path_except_section id)
      then
        user_err_loc (loc,"",pr_id id ++ str " already exists.");
      id
  | None ->
      next_global_ident_away default_thm_id (Pfedit.get_all_proof_names ()) 

let save_remaining_recthms (locality,kind) body opaq i (id,(t_i,(_,imps))) =
  match body with
  | None ->
      (match locality with
      | Discharge ->
          let impl = false in (* copy values from Vernacentries *)
          let k = IsAssumption Conjectural in
          let c = SectionLocalAssum (t_i,impl) in
	  let _ = declare_variable id (Lib.cwd(),c,k) in
          (Discharge, VarRef id,imps)
      | Local | Global ->
          let k = IsAssumption Conjectural in
          let local = match locality with
          | Local -> true
          | Global -> false
          | Discharge -> assert false
          in
          let decl = (ParameterEntry (None,t_i,None), k) in
          let kn = declare_constant id ~local decl in
          (locality,ConstRef kn,imps))
  | Some body ->
      let k = Kindops.logical_kind_of_goal_kind kind in
      let body_i = match kind_of_term body with
        | Fix ((nv,0),decls) -> mkFix ((nv,i),decls)
        | CoFix (0,decls) -> mkCoFix (i,decls)
        | _ -> anomaly (Pp.str "Not a proof by induction") in
      match locality with
      | Discharge ->
          let const = { const_entry_body =
                Future.from_val (body_i,Declareops.no_seff);
              const_entry_secctx = None;
              const_entry_type = Some t_i;
              const_entry_opaque = opaq;
              const_entry_inline_code = false;
              const_entry_feedback = None;
          } in
	  let c = SectionLocalDef const in
	  let _ = declare_variable id (Lib.cwd(), c, k) in
          (Discharge,VarRef id,imps)
      | Local | Global ->
        let local = match locality with
        | Local -> true
        | Global -> false
        | Discharge -> assert false
        in
        let const = { const_entry_body =
              Future.from_val (body_i,Declareops.no_seff);
            const_entry_secctx = None;
            const_entry_type = Some t_i;
            const_entry_opaque = opaq;
            const_entry_inline_code = false;
            const_entry_feedback = None;
        } in
        let kn = declare_constant id ~local (DefinitionEntry const, k) in
        (locality,ConstRef kn,imps)

let save_hook = ref ignore
let set_save_hook f = save_hook := f

let save_named proof =
  let id,const,do_guard,persistence,hook = proof in
  save id const do_guard persistence hook

let check_anonymity id save_ident =
  if not (String.equal (atompart_of_id id) (Id.to_string (default_thm_id))) then
    error "This command can only be used for unnamed theorem."


let save_anonymous proof save_ident =
  let id,const,do_guard,persistence,hook = proof in
  check_anonymity id save_ident;
  save save_ident const do_guard persistence hook

let save_anonymous_with_strength proof kind save_ident =
  let id,const,do_guard,_,hook = proof in
  check_anonymity id save_ident;
  (* we consider that non opaque behaves as local for discharge *)
  save save_ident const do_guard (Global, Proof kind) hook

(* Admitted *)

let admit hook () =
  let (id,k,typ) = Pfedit.current_proof_statement () in
  let e = Pfedit.get_used_variables(), typ, None in
  let kn = declare_constant id (ParameterEntry e,IsAssumption Conjectural) in
  let () = match fst k with
  | Global -> ()
  | Local | Discharge ->
    msg_warning (str "Let definition" ++ spc () ++ pr_id id ++ spc () ++
      str "declared as an axiom.")
  in
  let () = assumption_message id in
  hook Global (ConstRef kn)

(* Starting a goal *)

let start_hook = ref ignore
let set_start_hook = (:=) start_hook


let get_proof proof do_guard hook opacity =
  let (id,(const,persistence)) =
    Pfedit.cook_this_proof proof
  in
  id,{const with const_entry_opaque = opacity},do_guard,persistence,hook

let standard_proof_terminator compute_guard hook =
  let open Proof_global in function
  | Admitted ->
      admit hook ();
      Pp.feedback Interface.AddedAxiom
  | Proved (is_opaque,idopt,proof) ->
      let proof = get_proof proof compute_guard hook is_opaque in
      begin match idopt with
      | None -> save_named proof
      | Some ((_,id),None) -> save_anonymous proof id
      | Some ((_,id),Some kind) -> 
          save_anonymous_with_strength proof kind id
      end

let start_proof id kind ?sign c ?init_tac ?(compute_guard=[]) hook =
  let terminator = standard_proof_terminator compute_guard hook in
  let sign = 
    match sign with
    | Some sign -> sign
    | None -> initialize_named_context_for_proof ()
  in
  !start_hook c;
  Pfedit.start_proof id kind sign c ?init_tac terminator


let rec_tac_initializer finite guard thms snl =
  if finite then
    match List.map (fun (id,(t,_)) -> (id,t)) thms with
    | (id,_)::l -> Tactics.mutual_cofix id l 0
    | _ -> assert false
  else
    (* nl is dummy: it will be recomputed at Qed-time *)
    let nl = match snl with 
     | None -> List.map succ (List.map List.last guard)
     | Some nl -> nl
    in match List.map2 (fun (id,(t,_)) n -> (id,n,t)) thms nl with
       | (id,n,_)::l -> Tactics.mutual_fix id n l 0
       | _ -> assert false

let start_proof_with_initialization kind recguard thms snl hook =
  let intro_tac (_, (_, (ids, _))) =
    Tacticals.New.tclMAP (function
    | Name id -> Tactics.intro_mustbe_force id
    | Anonymous -> Tactics.intro) (List.rev ids) in
  let init_tac,guard = match recguard with
  | Some (finite,guard,init_tac) ->
      let rec_tac = Proofview.V82.tactic (rec_tac_initializer finite guard thms snl) in
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
  | (id,(t,(_,imps)))::other_thms ->
      let hook strength ref =
        let other_thms_data =
          if List.is_empty other_thms then [] else
            (* there are several theorems defined mutually *)
            let body,opaq = retrieve_first_recthm ref in
            List.map_i (save_remaining_recthms kind body opaq) 1 other_thms in
        let thms_data = (strength,ref,imps)::other_thms_data in
        List.iter (fun (strength,ref,imps) ->
	  maybe_declare_manual_implicits false ref imps;
	  hook strength ref) thms_data in
      start_proof id kind t ?init_tac hook ~compute_guard:guard

let start_proof_com kind thms hook =
  let evdref = ref Evd.empty in
  let env0 = Global.env () in
  let thms = List.map (fun (sopt,(bl,t,guard)) ->
    let impls, ((env, ctx), imps) = interp_context_evars evdref env0 bl in
    let t', imps' = interp_type_evars_impls ~impls evdref env t in
    check_evars_are_solved env Evd.empty !evdref;
    let ids = List.map pi1 ctx in
      (compute_proof_name (fst kind) sopt,
      (nf_evar !evdref (it_mkProd_or_LetIn t' ctx),
       (ids, imps @ lift_implicits (List.length ids) imps'),
       guard)))
    thms in
  let recguard,thms,snl = look_for_possibly_mutual_statements thms in
  start_proof_with_initialization kind recguard thms snl hook


(* Saving a proof *)

let save_proof ?proof = function
  | Vernacexpr.Admitted ->
      Proof_global.get_terminator() Proof_global.Admitted
  | Vernacexpr.Proved (is_opaque,idopt) ->
      let (proof_obj,terminator) =
        match proof with
        | None -> Proof_global.close_proof (fun x -> x)
        | Some proof -> proof
      in
      (* if the proof is given explicitly, nothing has to be deleted *)
      if Option.is_empty proof then Pfedit.delete_current_proof ();
      terminator (Proof_global.Proved (is_opaque,idopt,proof_obj))

(* Miscellaneous *)

let get_current_context () =
  try Pfedit.get_current_goal_context ()
  with e when Logic.catchable_exception e ->
    (Evd.empty, Global.env())










