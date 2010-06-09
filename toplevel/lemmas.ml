(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Created by Hugo Herbelin from contents related to lemma proofs in
   file command.ml, Aug 2009 *)

open Util
open Flags
open Pp
open Names
open Term
open Declarations
open Entries
open Environ
open Nameops
open Libnames
open Decls
open Decl_kinds
open Declare
open Pretyping
open Termops
open Namegen
open Evd
open Evarutil
open Reductionops
open Topconstr
open Constrintern
open Impargs
open Tacticals

(* Support for mutually proved theorems *)

let retrieve_first_recthm = function
  | VarRef id ->
      (pi2 (Global.lookup_named id),variable_opacity id)
  | ConstRef cst ->
      let {const_body=body;const_opaque=opaq} =	Global.lookup_constant cst in
      (Option.map Declarations.force body,opaq)
  | _ -> assert false

let adjust_guardness_conditions const = function
  | [] -> const (* Not a recursive statement *)
  | possible_indexes ->
  (* Try all combinations... not optimal *)
  match kind_of_term const.const_entry_body with
  | Fix ((nv,0),(_,_,fixdefs as fixdecls)) ->
(*      let possible_indexes =
	List.map2 (fun i c -> match i with Some i -> i | None ->
	  interval 0 (List.length ((lam_assum c))))
	  lemma_guard (Array.to_list fixdefs) in
*)
      let indexes =
	search_guard dummy_loc (Global.env()) possible_indexes fixdecls in
      { const with const_entry_body = mkFix ((indexes,0),fixdecls) }
  | c -> const

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
              mind.mind_finite & b = None ->
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
        List.flatten (list_map_i (fun i (_,b,t) ->
          match kind_of_term t with
          | Ind (kn,_ as ind) when
                let mind = Global.lookup_mind kn in
                mind.mind_finite & b = None ->
              [ind,x,i]
          | _ ->
              []) 0 (List.rev whnf_hyp_hds)) in
      let ind_ccl =
        let cclenv = push_rel_context hyps (Global.env()) in
        let whnf_ccl,_ = whd_betadeltaiota_stack cclenv Evd.empty ccl in
        match kind_of_term whnf_ccl with
        | Ind (kn,_ as ind) when
              let mind = Global.lookup_mind kn in
              mind.mind_ntypes = n & not mind.mind_finite ->
            [ind,x,0]
        | _ ->
            [] in
      ind_hyps,ind_ccl) thms in
    let inds_hyps,ind_ccls = List.split inds in
    let of_same_mutind ((kn,_),_,_) = function ((kn',_),_,_) -> kn = kn' in
    (* Check if all conclusions are coinductive in the same type *)
    (* (degenerated cartesian product since there is at most one coind ccl) *)
    let same_indccl =
      list_cartesians_filter (fun hyp oks ->
	if List.for_all (of_same_mutind hyp) oks
	then Some (hyp::oks) else None) [] ind_ccls in
    let ordered_same_indccl =
      List.filter (list_for_all_i (fun i ((kn,j),_,_) -> i=j) 0) same_indccl in
    (* Check if some hypotheses are inductive in the same type *)
    let common_same_indhyp =
      list_cartesians_filter (fun hyp oks ->
	if List.for_all (of_same_mutind hyp) oks
	then Some (hyp::oks) else None) [] inds_hyps in
    let ordered_inds,finite,guard =
      match ordered_same_indccl, common_same_indhyp with
      | indccl::rest, _ ->
	  assert (rest=[]);
          (* One occ. of common coind ccls and no common inductive hyps *)
	  if common_same_indhyp <> [] then
	    if_verbose warning "Assuming mutual coinductive statements.";
	  flush_all ();
          indccl, true, []
      | [], _::_ ->
	  if same_indccl <> [] &&
	     list_distinct (List.map pi1 (List.hd same_indccl)) then
	    if_verbose warn (strbrk "Coinductive statements do not follow the order of definition, assume the proof to be by induction."); flush_all ();
          let possible_guards = List.map (List.map pi3) inds_hyps in
	  (* assume the largest indices as possible *)
	  list_last common_same_indhyp, false, possible_guards
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
  | [] -> anomaly "Empty list of theorems."

(* Saving a goal *)

let save id const do_guard (locality,kind) hook =
  let const = adjust_guardness_conditions const do_guard in
  let {const_entry_body = pft;
       const_entry_type = tpo;
       const_entry_opaque = opacity } = const in
  let k = logical_kind_of_goal_kind kind in
  let l,r = match locality with
    | Local when Lib.sections_are_opened () ->
	let c = SectionLocalDef (pft, tpo, opacity) in
	let _ = declare_variable id (Lib.cwd(), c, k) in
	(Local, VarRef id)
    | Local | Global ->
        let kn = declare_constant id (DefinitionEntry const, k) in
	Autoinstance.search_declaration (ConstRef kn);
	(Global, ConstRef kn) in
  Pfedit.delete_current_proof ();
  definition_message id;
  hook l r

let save_hook = ref ignore
let set_save_hook f = save_hook := f

let save_named opacity =
  let id,(const,do_guard,persistence,hook) = Pfedit.cook_proof !save_hook in
  let const = { const with const_entry_opaque = opacity } in
  save id const do_guard persistence hook

let default_thm_id = id_of_string "Unnamed_thm"

let compute_proof_name locality = function
  | Some (loc,id) ->
      (* We check existence here: it's a bit late at Qed time *)
      if Nametab.exists_cci (Lib.make_path id) || is_section_variable id ||
	 locality=Global && Nametab.exists_cci (Lib.make_path_except_section id)
      then
        user_err_loc (loc,"",pr_id id ++ str " already exists.");
      id
  | None ->
      next_global_ident_away default_thm_id (Pfedit.get_all_proof_names ()) 

let save_remaining_recthms (local,kind) body opaq i (id,(t_i,(_,imps))) =
  match body with
  | None ->
      (match local with
      | Local ->
          let impl=false in (* copy values from Vernacentries *)
          let k = IsAssumption Conjectural in
          let c = SectionLocalAssum (t_i,impl) in
	  let _ = declare_variable id (Lib.cwd(),c,k) in
          (Local,VarRef id,imps)
      | Global ->
          let k = IsAssumption Conjectural in
          let kn = declare_constant id (ParameterEntry (t_i,false), k) in
          (Global,ConstRef kn,imps))
  | Some body ->
      let k = logical_kind_of_goal_kind kind in
      let body_i = match kind_of_term body with
        | Fix ((nv,0),decls) -> mkFix ((nv,i),decls)
        | CoFix (0,decls) -> mkCoFix (i,decls)
        | _ -> anomaly "Not a proof by induction" in
      match local with
      | Local ->
	  let c = SectionLocalDef (body_i, Some t_i, opaq) in
	  let _ = declare_variable id (Lib.cwd(), c, k) in
          (Local,VarRef id,imps)
      | Global ->
          let const =
            { const_entry_body = body_i;
              const_entry_type = Some t_i;
              const_entry_opaque = opaq;
              const_entry_boxed = false (* copy of what cook_proof does *)} in
          let kn = declare_constant id (DefinitionEntry const, k) in
          (Global,ConstRef kn,imps)

(* 4.2| General support for goals *)

let check_anonymity id save_ident =
  if atompart_of_id id <> "Unnamed_thm" then
    error "This command can only be used for unnamed theorem."

let save_anonymous opacity save_ident =
  let id,(const,do_guard,persistence,hook) = Pfedit.cook_proof !save_hook in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  save save_ident const do_guard persistence hook

let save_anonymous_with_strength kind opacity save_ident =
  let id,(const,do_guard,_,hook) = Pfedit.cook_proof !save_hook in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  (* we consider that non opaque behaves as local for discharge *)
  save save_ident const do_guard (Global, Proof kind) hook

(* Starting a goal *)

let start_hook = ref ignore
let set_start_hook = (:=) start_hook

let start_proof id kind c ?init_tac ?(compute_guard=[]) hook =
  let sign = Global.named_context () in
  let sign = clear_proofs sign in
  !start_hook c;
  Pfedit.start_proof id kind sign c ?init_tac ~compute_guard hook

let rec_tac_initializer finite guard thms snl =
  if finite then
    match List.map (fun (id,(t,_)) -> (id,t)) thms with
    | (id,_)::l -> Hiddentac.h_mutual_cofix true id l
    | _ -> assert false
  else
    (* nl is dummy: it will be recomputed at Qed-time *)
    let nl = match snl with 
     | None -> List.map succ (List.map list_last guard)
     | Some nl -> nl
    in match List.map2 (fun (id,(t,_)) n -> (id,n,t)) thms nl with
       | (id,n,_)::l -> Hiddentac.h_mutual_fix true id n l
       | _ -> assert false

let start_proof_with_initialization kind recguard thms snl hook =
  let intro_tac (_, (_, (ids, _))) =
    Refiner.tclMAP (function
    | Name id -> Tactics.intro_mustbe_force id
    | Anonymous -> Tactics.intro) (List.rev ids) in
  let init_tac,guard = match recguard with
  | Some (finite,guard,init_tac) ->
      let rec_tac = rec_tac_initializer finite guard thms snl in
      Some (match init_tac with
        | None -> 
            if Flags.is_auto_intros () then 
              tclTHENS rec_tac (List.map intro_tac thms)
            else
              rec_tac
        | Some tacl ->
            tclTHENS rec_tac
            (if Flags.is_auto_intros () then
              List.map2 (fun tac thm -> tclTHEN tac (intro_tac thm)) tacl thms
            else
              tacl)),guard
  | None ->
      assert (List.length thms = 1);
      (if Flags.is_auto_intros () then Some (intro_tac (List.hd thms)) else None), [] in
  match thms with
  | [] -> anomaly "No proof to start"
  | (id,(t,(_,imps)))::other_thms ->
      let hook strength ref =
        let other_thms_data =
          if other_thms = [] then [] else
            (* there are several theorems defined mutually *)
            let body,opaq = retrieve_first_recthm ref in
            list_map_i (save_remaining_recthms kind body opaq) 1 other_thms in
        let thms_data = (strength,ref,imps)::other_thms_data in
        List.iter (fun (strength,ref,imps) ->
	  maybe_declare_manual_implicits false ref imps;
	  hook strength ref) thms_data in
      start_proof id kind t ?init_tac hook ~compute_guard:guard

let start_proof_com kind thms hook =
  let evdref = ref (create_evar_defs Evd.empty) in
  let env0 = Global.env () in
  let thms = List.map (fun (sopt,(bl,t,guard)) ->
    let (env, ctx), imps = interp_context_evars evdref env0 bl in
    let t', imps' = interp_type_evars_impls ~evdref env t in
    Sign.iter_rel_context (check_evars env Evd.empty !evdref) ctx;
    let ids = List.map pi1 ctx in
      (compute_proof_name (fst kind) sopt,
      (nf_isevar !evdref (it_mkProd_or_LetIn t' ctx),
       (ids, imps @ lift_implicits (List.length ids) imps'),
       guard)))
    thms in
  let recguard,thms,snl = look_for_possibly_mutual_statements thms in
  start_proof_with_initialization kind recguard thms snl hook

(* Admitted *)

let admit () =
  let (id,k,typ,hook) = Pfedit.current_proof_statement () in
  let kn =
    declare_constant id (ParameterEntry (typ,false),IsAssumption Conjectural) in
  Pfedit.delete_current_proof ();
  assumption_message id;
  hook Global (ConstRef kn)

(* Miscellaneous *)

let get_current_context () =
  try Pfedit.get_current_goal_context ()
  with e when Logic.catchable_exception e ->
    (Evd.empty, Global.env())
