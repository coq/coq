(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to lemma proofs in
   file command.ml, Aug 2009 *)

open CErrors
open Util
open Pp
open Names
open Constr
open Declareops
open Entries
open Nameops
open Pretyping
open Termops
open Reductionops
open Constrintern
open Impargs

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(* Support for terminators and proofs with an associated constant
   [that can be saved] *)

type lemma_possible_guards = int list list

module Proof_ending = struct

  type t =
    | Regular
    | End_obligation of DeclareObl.obligation_qed_info
    | End_derive of { f : Id.t; name : Id.t }
    | End_equations of { hook : Constant.t list -> Evd.evar_map -> unit
                       ; i : Id.t
                       ; types : (Environ.env * Evar.t * Evd.evar_info * EConstr.named_context * Evd.econstr) list
                       ; wits : EConstr.t list ref
                       (* wits are actually computed by the proof
                          engine by side-effect after creating the
                          proof! This is due to the start_dependent_proof API *)
                       ; sigma : Evd.evar_map
                       }

end

module Recthm = struct
  type t =
    { name : Id.t
    ; typ : EConstr.t
    ; args : Name.t list
    ; impargs : Impargs.manual_implicits
    }
end

module Info = struct

  type t =
    { hook : DeclareDef.Hook.t option
    ; compute_guard : lemma_possible_guards
    ; impargs : Impargs.manual_implicits
    ; proof_ending : Proof_ending.t CEphemeron.key
    (* This could be improved and the CEphemeron removed *)
    ; other_thms : Recthm.t list
    ; scope : DeclareDef.locality
    ; kind : Decls.logical_kind
    }

  let make ?hook ?(proof_ending=Proof_ending.Regular) ?(scope=DeclareDef.Global Declare.ImportDefaultBehavior)
      ?(kind=Decls.(IsProof Lemma)) () =
    { hook
    ; compute_guard = []
    ; impargs = []
    ; proof_ending = CEphemeron.create proof_ending
    ; other_thms = []
    ; scope
    ; kind
    }
end

(* Proofs with a save constant function *)
type t =
  { proof : Proof_global.t
  ; info : Info.t
  }

let pf_map f pf = { pf with proof = f pf.proof }
let pf_fold f pf = f pf.proof

let set_endline_tactic t = pf_map (Proof_global.set_endline_tactic t)

(* To be removed *)
module Internal = struct

  (** Gets the current terminator without checking that the proof has
      been completed. Useful for the likes of [Admitted]. *)
  let get_info ps = ps.info

end

let by tac pf =
  let proof, res = Pfedit.by tac pf.proof in
  { pf with proof }, res

(************************************************************************)
(* Creating a lemma-like constant                                       *)
(************************************************************************)

let check_name_freshness locality {CAst.loc;v=id} : unit =
  (* We check existence here: it's a bit late at Qed time *)
  if Nametab.exists_cci (Lib.make_path id) || is_section_variable id ||
     locality <> DeclareDef.Discharge && Nametab.exists_cci (Lib.make_path_except_section id)
  then
    user_err ?loc  (Id.print id ++ str " already exists.")

let initialize_named_context_for_proof () =
  let sign = Global.named_context () in
  List.fold_right
    (fun d signv ->
      let id = NamedDecl.get_id d in
      let d = if Decls.variable_opacity id then NamedDecl.drop_body d else d in
      Environ.push_named_context_val d signv) sign Environ.empty_named_context_val

(* Starting a goal *)
let start_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Info.make ())
    sigma c =
  (* We remove the bodies of variables in the named context marked
     "opaque", this is a hack tho, see #10446 *)
  let sign = initialize_named_context_for_proof () in
  let goals = [ Global.env_of_context sign , c ] in
  let proof = Proof_global.start_proof sigma ~name ~udecl ~poly goals in
  { proof ; info }

let start_dependent_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Info.make ()) telescope =
  let proof = Proof_global.start_dependent_proof ~name ~udecl ~poly telescope in
  { proof; info }

let rec_tac_initializer finite guard thms snl =
  if finite then
    match List.map (fun { Recthm.name; typ } -> name,typ) thms with
    | (id,_)::l -> Tactics.mutual_cofix id l 0
    | _ -> assert false
  else
    (* nl is dummy: it will be recomputed at Qed-time *)
    let nl = match snl with
     | None -> List.map succ (List.map List.last guard)
     | Some nl -> nl
    in match List.map2 (fun { Recthm.name; typ } n -> (name, n, typ)) thms nl with
       | (id,n,_)::l -> Tactics.mutual_fix id n l 0
       | _ -> assert false

let start_lemma_with_initialization ?hook ~poly ~scope ~kind ~udecl sigma recguard thms snl =
  let intro_tac { Recthm.args; _ } = Tactics.auto_intros_tac args in
  let init_tac, compute_guard = match recguard with
  | Some (finite,guard,init_tac) ->
    let rec_tac = rec_tac_initializer finite guard thms snl in
    Some (match init_tac with
        | None ->
          Tacticals.New.tclTHENS rec_tac (List.map intro_tac thms)
        | Some tacl ->
          Tacticals.New.tclTHENS rec_tac
            List.(map2 (fun tac thm -> Tacticals.New.tclTHEN tac (intro_tac thm)) tacl thms)
      ),guard
  | None ->
    let () = match thms with [_] -> () | _ -> assert false in
    Some (intro_tac (List.hd thms)), [] in
  match thms with
  | [] -> anomaly (Pp.str "No proof to start.")
  | { Recthm.name; typ; impargs; _}::other_thms ->
    let info =
      Info.{ hook
           ; impargs
           ; compute_guard
           ; other_thms
           ; proof_ending = CEphemeron.create Proof_ending.Regular
           ; scope
           ; kind
           } in
    let lemma = start_lemma ~name ~poly ~udecl ~info sigma typ in
    pf_map (Proof_global.map_proof (fun p ->
        match init_tac with
        | None -> p
        | Some tac -> pi1 @@ Proof.run_tactic Global.(env ()) tac p)) lemma

let start_lemma_com ~program_mode ~poly ~scope ~kind ?inference_hook ?hook thms =
  let env0 = Global.env () in
  let decl = fst (List.hd thms) in
  let evd, udecl = Constrexpr_ops.interp_univ_decl_opt env0 (snd decl) in
  let evd, thms = List.fold_left_map (fun evd ((id, _), (bl, t)) ->
    let evd, (impls, ((env, ctx), imps)) = interp_context_evars ~program_mode env0 evd bl in
    let evd, (t', imps') = interp_type_evars_impls ~program_mode ~impls env evd t in
    let flags = { all_and_fail_flags with program_mode } in
    let hook = inference_hook in
    let evd = solve_remaining_evars ?hook flags env evd in
    let ids = List.map RelDecl.get_name ctx in
    check_name_freshness scope id;
    (* XXX: The nf_evar is critical !! *)
    evd, (id.CAst.v,
          (Evarutil.nf_evar evd (EConstr.it_mkProd_or_LetIn t' ctx),
           (ids, imps @ imps'))))
      evd thms in
  let recguard,thms,snl = RecLemmas.look_for_possibly_mutual_statements evd thms in
  let evd = Evd.minimize_universes evd in
  (* XXX: This nf_evar is critical too!! We are normalizing twice if
     you look at the previous lines... *)
  let thms = List.map (fun (name, (typ, (args, impargs))) ->
      { Recthm.name; typ = nf_evar evd typ; args; impargs} ) thms in
  let () =
    let open UState in
    if not (udecl.univdecl_extensible_instance && udecl.univdecl_extensible_constraints) then
       ignore (Evd.check_univ_decl ~poly evd udecl)
  in
  let evd =
    if poly then evd
    else (* We fix the variables to ensure they won't be lowered to Set *)
      Evd.fix_undefined_variables evd
  in
  start_lemma_with_initialization ?hook ~poly ~scope ~kind evd ~udecl recguard thms snl

(************************************************************************)
(* Commom constant saving path, for both Qed and Admitted               *)
(************************************************************************)

(* Helper for process_recthms *)
let retrieve_first_recthm uctx = function
  | GlobRef.VarRef id ->
    NamedDecl.get_value (Global.lookup_named id),
    Decls.variable_opacity id
  | GlobRef.ConstRef cst ->
    let cb = Global.lookup_constant cst in
    (* we get the right order somehow but surely it could be enforced in a better way *)
    let uctx = UState.context uctx in
    let inst = Univ.UContext.instance uctx in
    let map (c, _, _) = Vars.subst_instance_constr inst c in
    (Option.map map (Global.body_of_constant_body Library.indirect_accessor cb), is_opaque cb)
  | _ -> assert false

(* Helper for process_recthms *)
let save_remaining_recthms env sigma ~poly ~scope ~udecl uctx body opaq i { Recthm.name; typ; impargs } =
  let norm c = EConstr.to_constr (Evd.from_ctx uctx) c in
  let body = Option.map EConstr.of_constr body in
  let univs = UState.check_univ_decl ~poly uctx udecl in
  let t_i = norm typ in
  let kind = Decls.(IsAssumption Conjectural) in
  match body with
  | None ->
    let open DeclareDef in
    (match scope with
     | Discharge ->
       let impl = Glob_term.Explicit in
       let univs = match univs with
         | Polymorphic_entry (_, univs) ->
           (* What is going on here? *)
           Univ.ContextSet.of_context univs
         | Monomorphic_entry univs -> univs
       in
       let () = Declare.declare_universe_context ~poly univs in
       let c = Declare.SectionLocalAssum {typ=t_i; impl} in
       let () = Declare.declare_variable ~name ~kind c in
       GlobRef.VarRef name, impargs
     | Global local ->
       let kind = Decls.(IsAssumption Conjectural) in
       let decl = Declare.ParameterEntry (None,(t_i,univs),None) in
       let kn = Declare.declare_constant ~name ~local ~kind decl in
       GlobRef.ConstRef kn, impargs)
  | Some body ->
    let body = norm body in
    let rec body_i t = match Constr.kind t with
      | Fix ((nv,0),decls) -> mkFix ((nv,i),decls)
      | CoFix (0,decls) -> mkCoFix (i,decls)
      | LetIn(na,t1,ty,t2) -> mkLetIn (na,t1,ty, body_i t2)
      | Lambda(na,ty,t) -> mkLambda(na,ty,body_i t)
      | App (t, args) -> mkApp (body_i t, args)
      | _ ->
        anomaly Pp.(str "Not a proof by induction: " ++ Printer.pr_constr_env env sigma body ++ str ".") in
    let body_i = body_i body in
    let open DeclareDef in
    match scope with
    | Discharge ->
      let const = Declare.definition_entry ~types:t_i ~opaque:opaq ~univs body_i in
      let c = Declare.SectionLocalDef const in
      let () = Declare.declare_variable ~name ~kind c in
      GlobRef.VarRef name, impargs
    | Global local ->
      let const = Declare.definition_entry ~types:t_i ~univs ~opaque:opaq body_i in
      let kn = Declare.declare_constant ~name ~local ~kind (Declare.DefinitionEntry const) in
      GlobRef.ConstRef kn, impargs

(* This declares implicits and calls the hooks for all the theorems,
   including the main one *)
let process_recthms ?fix_exn ?hook env sigma uctx ~udecl ~poly ~scope dref imps other_thms =
  let other_thms_data =
    if List.is_empty other_thms then [] else
      (* there are several theorems defined mutually *)
      let body,opaq = retrieve_first_recthm uctx dref in
      List.map_i (save_remaining_recthms env sigma ~poly ~scope ~udecl uctx body opaq) 1 other_thms in
  let thms_data = (dref,imps)::other_thms_data in
  List.iter (fun (dref,imps) ->
      maybe_declare_manual_implicits false dref imps;
      DeclareDef.Hook.(call ?fix_exn ?hook { S.uctx; obls = []; scope; dref})) thms_data

(************************************************************************)
(* Admitting a lemma-like constant                                      *)
(************************************************************************)

(* Admitted *)
let warn_let_as_axiom =
  CWarnings.create ~name:"let-as-axiom" ~category:"vernacular"
                   (fun id -> strbrk "Let definition" ++ spc () ++ Id.print id ++
                                spc () ++ strbrk "declared as an axiom.")

let get_keep_admitted_vars =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~name:"keep section variables in admitted proofs"
    ~key:["Keep"; "Admitted"; "Variables"]
    ~value:true

let finish_admitted env sigma ~name ~poly ~scope pe ctx hook ~udecl impargs other_thms =
  let open DeclareDef in
  let local = match scope with
  | Global local -> local
  | Discharge -> warn_let_as_axiom name; Declare.ImportNeedQualified
  in
  let kn = Declare.declare_constant ~name ~local ~kind:Decls.(IsAssumption Conjectural) (Declare.ParameterEntry pe) in
  let () = Declare.assumption_message name in
  DeclareUniv.declare_univ_binders (GlobRef.ConstRef kn) (UState.universe_binders ctx);
  (* This takes care of the implicits and hook for the current constant*)
  process_recthms ?fix_exn:None ?hook env sigma ctx ~udecl ~poly ~scope:(Global local) (GlobRef.ConstRef kn) impargs other_thms

let save_lemma_admitted ~(lemma : t) : unit =
  (* Used for printing in recthms *)
  let env = Global.env () in
  let { Info.hook; scope; impargs; other_thms } = lemma.info in
  let udecl = Proof_global.get_universe_decl lemma.proof in
  let Proof.{ sigma; name; poly; entry } = Proof.data (Proof_global.get_proof lemma.proof) in
  let typ = match Proofview.initial_goals entry with
    | [typ] -> snd typ
    | _ -> CErrors.anomaly ~label:"Lemmas.save_proof" (Pp.str "more than one statement.")
  in
  let typ = EConstr.Unsafe.to_constr typ in
  (* This will warn if the proof is complete *)
  let pproofs, _univs = Proof_global.return_proof ~allow_partial:true lemma.proof in
  let sec_vars =
    if not (get_keep_admitted_vars ()) then None
    else match Proof_global.get_used_variables lemma.proof, pproofs with
      | Some _ as x, _ -> x
      | None, (pproof, _) :: _ ->
        let env = Global.env () in
        let ids_typ = Environ.global_vars_set env typ in
        let ids_def = Environ.global_vars_set env pproof in
        Some (Environ.really_needed env (Id.Set.union ids_typ ids_def))
      | _ -> None in
  let universes = Proof_global.get_initial_euctx lemma.proof in
  let ctx = UState.check_univ_decl ~poly universes udecl in
  finish_admitted env sigma ~name ~poly ~scope (sec_vars, (typ, ctx), None) universes hook ~udecl impargs other_thms

(************************************************************************)
(* Saving a lemma-like constant                                         *)
(************************************************************************)

let default_thm_id = Id.of_string "Unnamed_thm"

let check_anonymity id save_ident =
  if not (String.equal (atompart_of_id id) (Id.to_string (default_thm_id))) then
    user_err Pp.(str "This command can only be used for unnamed theorem.")

(* Support for mutually proved theorems *)

(* Helper for finish_proved *)
let adjust_guardness_conditions const = function
  | [] -> const (* Not a recursive statement *)
  | possible_indexes ->
    (* Try all combinations... not optimal *)
    let env = Global.env() in
    Declare.Internal.map_entry_body const
      ~f:(fun ((body, ctx), eff) ->
          match Constr.kind body with
          | Fix ((nv,0),(_,_,fixdefs as fixdecls)) ->
            let env = Safe_typing.push_private_constants env eff.Evd.seff_private in
            let indexes = search_guard env possible_indexes fixdecls in
            (mkFix ((indexes,0),fixdecls), ctx), eff
          | _ -> (body, ctx), eff)

let finish_proved env sigma idopt po info =
  let open Proof_global in
  let { Info.hook; compute_guard; impargs; other_thms; scope; kind } = info in
  match po with
  | { name; entries=[const]; universes; udecl; poly } ->
    let name = match idopt with
      | None -> name
      | Some { CAst.v = save_id } -> check_anonymity name save_id; save_id in
    let fix_exn = Declare.Internal.get_fix_exn const in
    let () = try
      let const = adjust_guardness_conditions const compute_guard in
      let should_suggest = const.Declare.proof_entry_opaque &&
                           Option.is_empty const.Declare.proof_entry_secctx in
      let open DeclareDef in
      let r = match scope with
        | Discharge ->
          let c = Declare.SectionLocalDef const in
          let () = Declare.declare_variable ~name ~kind c in
          let () = if should_suggest
            then Proof_using.suggest_variable (Global.env ()) name
          in
          GlobRef.VarRef name
        | Global local ->
          let kn =
            Declare.declare_constant ~name ~local ~kind (Declare.DefinitionEntry const) in
          let () = if should_suggest
            then Proof_using.suggest_constant (Global.env ()) kn
          in
          let gr = GlobRef.ConstRef kn in
          DeclareUniv.declare_univ_binders gr (UState.universe_binders universes);
          gr
      in
      Declare.definition_message name;
      (* This takes care of the implicits and hook for the current constant*)
      process_recthms ~fix_exn ?hook env sigma universes ~udecl ~poly ~scope r impargs other_thms
    with e when CErrors.noncritical e ->
      let e = CErrors.push e in
      iraise (fix_exn e)
    in ()
  | _ ->
    CErrors.anomaly Pp.(str "[standard_proof_terminator] close_proof returned more than one proof term")

let finish_derived ~f ~name ~idopt ~entries =
  (* [f] and [name] correspond to the proof of [f] and of [suchthat], respectively. *)

  if Option.has_some idopt then
    CErrors.user_err Pp.(str "Cannot save a proof of Derive with an explicit name.");

  let f_def, lemma_def =
    match entries with
    | [_;f_def;lemma_def] ->
      f_def, lemma_def
    | _ -> assert false
  in
  (* The opacity of [f_def] is adjusted to be [false], as it
     must. Then [f] is declared in the global environment. *)
  let f_def = Declare.Internal.set_opacity ~opaque:false f_def in
  let f_kind = Decls.(IsDefinition Definition) in
  let f_def = Declare.DefinitionEntry f_def in
  let f_kn = Declare.declare_constant ~name:f ~kind:f_kind f_def in
  let f_kn_term = mkConst f_kn in
  (* In the type and body of the proof of [suchthat] there can be
     references to the variable [f]. It needs to be replaced by
     references to the constant [f] declared above. This substitution
     performs this precise action. *)
  let substf c = Vars.replace_vars [f,f_kn_term] c in
  (* Extracts the type of the proof of [suchthat]. *)
  let lemma_pretype typ =
    match typ with
    | Some t -> Some (substf t)
    | None -> assert false (* Proof_global always sets type here. *)
  in
  (* The references of [f] are subsituted appropriately. *)
  let lemma_def = Declare.Internal.map_entry_type lemma_def ~f:lemma_pretype in
  (* The same is done in the body of the proof. *)
  let lemma_def = Declare.Internal.map_entry_body lemma_def ~f:(fun ((b,ctx),fx) -> (substf b, ctx), fx) in
  let lemma_def = Declare.DefinitionEntry lemma_def in
  let _ : Names.Constant.t = Declare.declare_constant ~name ~kind:Decls.(IsProof Proposition) lemma_def in
  ()

let finish_proved_equations lid kind proof_obj hook i types wits sigma0 =

  let obls = ref 1 in
  let sigma, recobls =
    CList.fold_left2_map (fun sigma (wit, (evar_env, ev, evi, local_context, type_)) entry ->
        let id =
          match Evd.evar_ident ev sigma0 with
          | Some id -> id
          | None -> let n = !obls in incr obls; add_suffix i ("_obligation_" ^ string_of_int n)
        in
        let entry, args = Declare.Internal.shrink_entry local_context entry in
        let cst = Declare.declare_constant ~name:id ~kind (Declare.DefinitionEntry entry) in
        let sigma, app = Evarutil.new_global sigma (GlobRef.ConstRef cst) in
        let sigma = Evd.define ev (EConstr.applist (app, List.map EConstr.of_constr args)) sigma in
        sigma, cst) sigma0
      (CList.combine (List.rev !wits) types) proof_obj.Proof_global.entries
  in
  hook recobls sigma

let finalize_proof idopt env sigma proof_obj proof_info =
  let open Proof_global in
  let open Proof_ending in
  match CEphemeron.default proof_info.Info.proof_ending Regular with
  | Regular ->
    finish_proved env sigma idopt proof_obj proof_info
  | End_obligation oinfo ->
    DeclareObl.obligation_terminator proof_obj.entries proof_obj.universes oinfo
  | End_derive { f ; name } ->
    finish_derived ~f ~name ~idopt ~entries:proof_obj.entries
  | End_equations { hook; i; types; wits; sigma } ->
    finish_proved_equations idopt proof_info.Info.kind proof_obj hook i types wits sigma

let save_lemma_proved ~lemma ~opaque ~idopt =
  (* Env and sigma are just used for error printing in save_remaining_recthms *)
  let env = Global.env () in
  let { Proof.sigma } = Proof.data (Proof_global.get_proof lemma.proof) in
  let proof_obj = Proof_global.close_proof ~opaque ~keep_body_ucst_separate:false (fun x -> x) lemma.proof in
  finalize_proof idopt env sigma proof_obj lemma.info

(***********************************************************************)
(* Special case to close a lemma without forcing a proof               *)
(***********************************************************************)
let save_lemma_admitted_delayed ~proof ~info =
  let open Proof_global in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let { name; entries; universes; udecl; poly } = proof in
  let { Info.hook; scope; impargs; other_thms } = info in
  if List.length entries <> 1 then
    user_err Pp.(str "Admitted does not support multiple statements");
  let { Declare.proof_entry_secctx; proof_entry_type; proof_entry_universes } = List.hd entries in
  let poly = match proof_entry_universes with
    | Entries.Monomorphic_entry _ -> false
    | Entries.Polymorphic_entry (_, _) -> true in
  let typ = match proof_entry_type with
    | None -> user_err Pp.(str "Admitted requires an explicit statement");
    | Some typ -> typ in
  let ctx = UState.univ_entry ~poly universes in
  let sec_vars = if get_keep_admitted_vars () then proof_entry_secctx else None in
  finish_admitted env sigma ~name ~poly ~scope (sec_vars, (typ, ctx), None) universes hook ~udecl impargs other_thms

let save_lemma_proved_delayed ~proof ~info ~idopt =
  (* Env and sigma are just used for error printing in save_remaining_recthms *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  finalize_proof idopt env sigma proof info
