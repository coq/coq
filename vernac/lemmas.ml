(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to lemma proofs in
   file command.ml, Aug 2009 *)

open Util
open Names

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

module Info = struct

  type t =
    { hook : DeclareDef.Hook.t option
    ; proof_ending : Proof_ending.t CEphemeron.key
    (* This could be improved and the CEphemeron removed *)
    ; scope : DeclareDef.locality
    ; kind : Decls.logical_kind
    (* thms and compute guard are specific only to start_lemma_with_initialization + regular terminator *)
    ; thms : DeclareDef.Recthm.t list
    ; compute_guard : lemma_possible_guards
    }

  let make ?hook ?(proof_ending=Proof_ending.Regular) ?(scope=DeclareDef.Global Declare.ImportDefaultBehavior)
      ?(kind=Decls.(IsProof Lemma)) () =
    { hook
    ; compute_guard = []
    ; proof_ending = CEphemeron.create proof_ending
    ; thms = []
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

let initialize_named_context_for_proof () =
  let sign = Global.named_context () in
  List.fold_right
    (fun d signv ->
      let id = NamedDecl.get_id d in
      let d = if Decls.variable_opacity id then NamedDecl.drop_body d else d in
      Environ.push_named_context_val d signv) sign Environ.empty_named_context_val

let add_first_thm ~info ~name ~typ ~impargs =
  let thms =
    { DeclareDef.Recthm.name
    ; impargs
    ; typ = EConstr.Unsafe.to_constr typ
    ; args = [] } :: info.Info.thms
  in
  { info with Info.thms }

(* Starting a goal *)
let start_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Info.make ()) ?(impargs=[]) sigma c =
  (* We remove the bodies of variables in the named context marked
     "opaque", this is a hack tho, see #10446 *)
  let sign = initialize_named_context_for_proof () in
  let goals = [ Global.env_of_context sign , c ] in
  let proof = Proof_global.start_proof sigma ~name ~udecl ~poly goals in
  let info = add_first_thm ~info ~name ~typ:c ~impargs in
  { proof; info }

(* Note that proofs opened by start_dependent lemma cannot be closed
   by the regular terminators, thus we don't need to update the [thms]
   field. We will capture this invariant by typing in the future *)
let start_dependent_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Info.make ()) telescope =
  let proof = Proof_global.start_dependent_proof ~name ~udecl ~poly telescope in
  { proof; info }

let rec_tac_initializer finite guard thms snl =
  if finite then
    match List.map (fun { DeclareDef.Recthm.name; typ } -> name, (EConstr.of_constr typ)) thms with
    | (id,_)::l -> Tactics.mutual_cofix id l 0
    | _ -> assert false
  else
    (* nl is dummy: it will be recomputed at Qed-time *)
    let nl = match snl with
     | None -> List.map succ (List.map List.last guard)
     | Some nl -> nl
    in match List.map2 (fun { DeclareDef.Recthm.name; typ } n -> (name, n, (EConstr.of_constr typ))) thms nl with
       | (id,n,_)::l -> Tactics.mutual_fix id n l 0
       | _ -> assert false

let start_lemma_with_initialization ?hook ~poly ~scope ~kind ~udecl sigma recguard thms snl =
  let intro_tac { DeclareDef.Recthm.args; _ } = Tactics.auto_intros_tac args in
  let init_tac, compute_guard = match recguard with
  | Some (finite,guard,init_terms) ->
    let rec_tac = rec_tac_initializer finite guard thms snl in
    let term_tac =
      match init_terms with
      | None ->
        List.map intro_tac thms
      | Some init_terms ->
        (* This is the case for hybrid proof mode / definition
           fixpoint, where terms for some constants are given with := *)
        let tacl = List.map (Option.cata (EConstr.of_constr %> Tactics.exact_no_check) Tacticals.New.tclIDTAC) init_terms in
        List.map2 (fun tac thm -> Tacticals.New.tclTHEN tac (intro_tac thm)) tacl thms
    in
    Tacticals.New.tclTHENS rec_tac term_tac, guard
  | None ->
    let () = match thms with [_] -> () | _ -> assert false in
    intro_tac (List.hd thms), [] in
  match thms with
  | [] -> CErrors.anomaly (Pp.str "No proof to start.")
  | { DeclareDef.Recthm.name; typ; impargs; _} :: thms ->
    let info =
      Info.{ hook
           ; compute_guard
           ; proof_ending = CEphemeron.create Proof_ending.Regular
           ; thms
           ; scope
           ; kind
           } in
    (* start_lemma has the responsibility to add (name, impargs, typ)
       to thms, once Info.t is more refined this won't be necessary *)
    let lemma = start_lemma ~name ~impargs ~poly ~udecl ~info sigma (EConstr.of_constr typ) in
    pf_map (Proof_global.map_proof (fun p ->
        pi1 @@ Proof.run_tactic Global.(env ()) init_tac p)) lemma

(************************************************************************)
(* Commom constant saving path, for both Qed and Admitted               *)
(************************************************************************)

(* Support for mutually proved theorems *)

(* XXX: Most of this does belong to Declare, due to proof_entry manip *)
module MutualEntry : sig

  val declare_variable
    : info:Info.t
    -> uctx:UState.t
    -> Entries.parameter_entry
    -> Names.GlobRef.t list

  val declare_mutdef
    (* Common to all recthms *)
    : info:Info.t
    -> uctx:UState.t
    -> Evd.side_effects Declare.proof_entry
    -> Names.GlobRef.t list

end = struct

  (* Body with the fix *)
  type et =
    | NoBody of Entries.parameter_entry
    | Single of Evd.side_effects Declare.proof_entry
    | Mutual of Evd.side_effects Declare.proof_entry

  type t =
    { entry : et
    ; info : Info.t
    }

  (* XXX: Refactor this with the code in [DeclareDef.declare_mutdef] *)
  let guess_decreasing env possible_indexes ((body, ctx), eff) =
    let open Constr in
    match Constr.kind body with
    | Fix ((nv,0),(_,_,fixdefs as fixdecls)) ->
      let env = Safe_typing.push_private_constants env eff.Evd.seff_private in
      let indexes = Pretyping.search_guard env possible_indexes fixdecls in
      (mkFix ((indexes,0),fixdecls), ctx), eff
    | _ -> (body, ctx), eff

  let adjust_guardness_conditions ~info const =
    let entry = match info.Info.compute_guard with
    | [] ->
      (* Not a recursive statement *)
      Single const
    | possible_indexes ->
      (* Try all combinations... not optimal *)
      let env = Global.env() in
      let pe = Declare.Internal.map_entry_body const
          ~f:(guess_decreasing env possible_indexes)
      in
      Mutual pe
    in { entry; info }

  let rec select_body i t =
    let open Constr in
    match Constr.kind t with
    | Fix ((nv,0),decls) -> mkFix ((nv,i),decls)
    | CoFix (0,decls) -> mkCoFix (i,decls)
    | LetIn(na,t1,ty,t2) -> mkLetIn (na,t1,ty, select_body i t2)
    | Lambda(na,ty,t) -> mkLambda(na,ty, select_body i t)
    | App (t, args) -> mkApp (select_body i t, args)
    | _ ->
      CErrors.anomaly
        Pp.(str "Not a proof by induction: " ++
            Termops.Internal.debug_print_constr (EConstr.of_constr t) ++ str ".")

  let declare_mutdef ?fix_exn ~uctx ?hook_data ~name ?typ ~impargs ~info mutpe i =
    let { Info.hook; compute_guard; scope; kind; _ } = info in
    match mutpe with
    | NoBody pe ->
      DeclareDef.declare_assumption ?fix_exn ~name ~scope ~hook ~impargs ~uctx pe
    | Single pe ->
      (* We'd like to do [assert (i = 0)] here, however this codepath
         is used when declaring mutual cofixpoints *)
      let ubind = UState.universe_binders uctx in
      let hook_data = Option.map (fun hook -> hook, uctx, []) info.Info.hook in
      DeclareDef.declare_definition ~name ~scope ~kind ?hook_data ~ubind ~impargs pe
    | Mutual pe ->
      (* if i = 0 , we don't touch the type; this is for compat
         but not clear it is the right thing to do *)
      (* See start_dependent_proof ~typ:mkProp to understand why
         we don't we use the type stored here. This is obviously a
         fixme [was like this for long time]
      *)
      let pe =
        match typ with
        | None -> pe
        | Some typ ->
          if i > 0
          then Declare.Internal.map_entry_type pe ~f:(fun _ -> Some typ)
          else pe
      in
      let hook_data = Option.map (fun hook -> hook, uctx, []) info.Info.hook in
      let ubind = if i = 0 then UState.universe_binders uctx else UnivNames.empty_binders in
      let pe = Declare.Internal.map_entry_body pe
          ~f:(fun ((body, ctx), eff) -> (select_body i body, ctx), eff) in
      DeclareDef.declare_definition ~name ~scope ~kind ?hook_data ~ubind ~impargs pe

  let declare_mutdef ?fix_exn ~uctx { entry; info } =
    let rs =
      List.map_i (
        fun i { DeclareDef.Recthm.name; typ; impargs } ->
          declare_mutdef ?fix_exn ~name ~info ~uctx ~typ ~impargs entry i)
        0 info.Info.thms
    in rs

  let declare_variable ~info ~uctx pe =
    declare_mutdef ~uctx { entry = NoBody pe; info }

  let declare_mutdef ~info ~uctx const =
    let mutpe = adjust_guardness_conditions ~info const in
    declare_mutdef ~uctx mutpe

end

(************************************************************************)
(* Admitting a lemma-like constant                                      *)
(************************************************************************)

(* Admitted *)
let get_keep_admitted_vars =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Keep"; "Admitted"; "Variables"]
    ~value:true

let compute_proof_using_for_admitted proof typ pproofs =
  if not (get_keep_admitted_vars ()) then None
  else match Proof_global.get_used_variables proof, pproofs with
    | Some _ as x, _ -> x
    | None, pproof :: _ ->
      let env = Global.env () in
      let ids_typ = Environ.global_vars_set env typ in
      (* [pproof] is evar-normalized by [partial_proof]. We don't
         count variables appearing only in the type of evars. *)
      let ids_def = Environ.global_vars_set env (EConstr.Unsafe.to_constr pproof) in
      Some (Environ.really_needed env (Id.Set.union ids_typ ids_def))
    | _ -> None

let finish_admitted ~info ~uctx pe =
  let _r : Names.GlobRef.t list = MutualEntry.declare_variable ~info ~uctx pe in
  ()

let save_lemma_admitted ~(lemma : t) : unit =
  let udecl = Proof_global.get_universe_decl lemma.proof in
  let Proof.{ poly; entry } = Proof.data (Proof_global.get_proof lemma.proof) in
  let typ = match Proofview.initial_goals entry with
    | [typ] -> snd typ
    | _ -> CErrors.anomaly ~label:"Lemmas.save_lemma_admitted" (Pp.str "more than one statement.")
  in
  let typ = EConstr.Unsafe.to_constr typ in
  let proof = Proof_global.get_proof lemma.proof in
  let pproofs = Proof.partial_proof proof in
  let sec_vars = compute_proof_using_for_admitted lemma.proof typ pproofs in
  let universes = Proof_global.get_initial_euctx lemma.proof in
  let ctx = UState.check_univ_decl ~poly universes udecl in
  finish_admitted ~info:lemma.info ~uctx:universes (sec_vars, (typ, ctx), None)

(************************************************************************)
(* Saving a lemma-like constant                                         *)
(************************************************************************)

let finish_proved po info =
  let open Proof_global in
  match po with
  | { entries=[const]; uctx } ->
    let _r : Names.GlobRef.t list = MutualEntry.declare_mutdef ~info ~uctx const in
    ()
  | _ ->
    CErrors.anomaly ~label:"finish_proved" Pp.(str "close_proof returned more than one proof term")

let finish_derived ~f ~name ~entries =
  (* [f] and [name] correspond to the proof of [f] and of [suchthat], respectively. *)

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
  let f_kn_term = Constr.mkConst f_kn in
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

let finish_proved_equations kind proof_obj hook i types wits sigma0 =

  let obls = ref 1 in
  let sigma, recobls =
    CList.fold_left2_map (fun sigma (wit, (evar_env, ev, evi, local_context, type_)) entry ->
        let id =
          match Evd.evar_ident ev sigma0 with
          | Some id -> id
          | None -> let n = !obls in incr obls; Nameops.add_suffix i ("_obligation_" ^ string_of_int n)
        in
        let entry, args = Declare.Internal.shrink_entry local_context entry in
        let cst = Declare.declare_constant ~name:id ~kind (Declare.DefinitionEntry entry) in
        let sigma, app = Evarutil.new_global sigma (GlobRef.ConstRef cst) in
        let sigma = Evd.define ev (EConstr.applist (app, List.map EConstr.of_constr args)) sigma in
        sigma, cst) sigma0
      (CList.combine (List.rev !wits) types) proof_obj.Proof_global.entries
  in
  hook recobls sigma

let finalize_proof proof_obj proof_info =
  let open Proof_global in
  let open Proof_ending in
  match CEphemeron.default proof_info.Info.proof_ending Regular with
  | Regular ->
    finish_proved proof_obj proof_info
  | End_obligation oinfo ->
    DeclareObl.obligation_terminator proof_obj.entries proof_obj.uctx oinfo
  | End_derive { f ; name } ->
    finish_derived ~f ~name ~entries:proof_obj.entries
  | End_equations { hook; i; types; wits; sigma } ->
    finish_proved_equations proof_info.Info.kind proof_obj hook i types wits sigma

let err_save_forbidden_in_place_of_qed () =
  CErrors.user_err (Pp.str "Cannot use Save with more than one constant or in this proof mode")

let process_idopt_for_save ~idopt info =
  match idopt with
  | None -> info
  | Some { CAst.v = save_name } ->
    (* Save foo was used; we override the info in the first theorem *)
    let thms =
      match info.Info.thms, CEphemeron.default info.Info.proof_ending Proof_ending.Regular with
      | [ { DeclareDef.Recthm.name; _} as decl ], Proof_ending.Regular ->
        [ { decl with DeclareDef.Recthm.name = save_name } ]
      | _ ->
        err_save_forbidden_in_place_of_qed ()
    in { info with Info.thms }

let save_lemma_proved ~lemma ~opaque ~idopt =
  (* Env and sigma are just used for error printing in save_remaining_recthms *)
  let proof_obj = Proof_global.close_proof ~opaque ~keep_body_ucst_separate:false (fun x -> x) lemma.proof in
  let proof_info = process_idopt_for_save ~idopt lemma.info in
  finalize_proof proof_obj proof_info

(***********************************************************************)
(* Special case to close a lemma without forcing a proof               *)
(***********************************************************************)
let save_lemma_admitted_delayed ~proof ~info =
  let open Proof_global in
  let { entries; uctx } = proof in
  if List.length entries <> 1 then
    CErrors.user_err Pp.(str "Admitted does not support multiple statements");
  let { Declare.proof_entry_secctx; proof_entry_type; proof_entry_universes } = List.hd entries in
  let poly = match proof_entry_universes with
    | Entries.Monomorphic_entry _ -> false
    | Entries.Polymorphic_entry (_, _) -> true in
  let typ = match proof_entry_type with
    | None -> CErrors.user_err Pp.(str "Admitted requires an explicit statement");
    | Some typ -> typ in
  let ctx = UState.univ_entry ~poly uctx in
  let sec_vars = if get_keep_admitted_vars () then proof_entry_secctx else None in
  finish_admitted ~uctx ~info (sec_vars, (typ, ctx), None)

let save_lemma_proved_delayed ~proof ~info ~idopt =
  (* vio2vo calls this but with invalid info, we have to workaround
     that to add the name to the info structure *)
  if CList.is_empty info.Info.thms then
    let info = add_first_thm ~info ~name:proof.Proof_global.name ~typ:EConstr.mkSet ~impargs:[] in
    finalize_proof proof info
  else
    let info = process_idopt_for_save ~idopt info in
    finalize_proof proof info
