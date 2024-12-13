(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module is about the low-level declaration of logical objects *)

open Pp
open Util
open Names
open Safe_typing
module NamedDecl = Context.Named.Declaration

(* Hooks naturally belong here as they apply to both definitions and lemmas *)
module Hook = struct
  module S = struct
    type t =
      { uctx : UState.t
      (** [ustate]: universe constraints obtained when the term was closed *)
      ; obls : (Names.Id.t * Constr.t) list
      (** [(n1,t1),...(nm,tm)]: association list between obligation
          name and the corresponding defined term (might be a constant,
          but also an arbitrary term in the Expand case of obligations) *)
      ; scope : Locality.definition_scope
      (**  [locality]: Locality of the original declaration *)
      ; dref : Names.GlobRef.t
      (** [ref]: identifier of the original declaration *)
      }
  end

  type 'a g = (S.t -> 'a -> 'a) CEphemeron.key
  type t = unit g

  let make_g hook = CEphemeron.create hook
  let make (hook : S.t -> unit) : t = CEphemeron.create (fun x () -> hook x)

  let hcall hook x s = CEphemeron.default hook (fun _ x -> x) x s

  let call_g ?hook x s = Option.cata (fun hook -> hcall hook x s) s hook
  let call ?hook x = Option.iter (fun hook -> hcall hook x ()) hook

end

module CInfo = struct

  type 'constr t =
    { name : Id.t
    (** Name of theorem *)
    ; typ : 'constr
    (** Type of theorem  *)
    ; args : Name.t list
    (** Names to pre-introduce  *)
    ; impargs : Impargs.manual_implicits
    (** Explicitily declared implicit arguments  *)
    }


  let make ~name ~typ ?(args=[]) ?(impargs=[]) () =
    { name; typ; args; impargs }

  let to_constr sigma thm = { thm with typ = EConstr.to_constr sigma thm.typ }

  let get_typ { typ; _ } = typ
  let get_name { name; _ } = name

end

(** Information for a declaration, interactive or not, includes
   parameters shared by mutual constants *)
module Info = struct

  type t =
    { poly : bool
    ; inline : bool
    ; kind : Decls.logical_kind
    ; udecl : UState.universe_decl
    ; scope : Locality.definition_scope
    ; clearbody : bool (* always false for non Discharge scope *)
    ; hook : Hook.t option
    ; typing_flags : Declarations.typing_flags option
    ; user_warns : Globnames.extended_global_reference UserWarn.with_qf option
    ; ntns : Metasyntax.notation_interpretation_decl list
    ; loc : Loc.t option
    }

  (** Note that [opaque] doesn't appear here as it is not known at the
     start of the proof in the interactive case. *)
  let make ?loc ?(poly=false) ?(inline=false) ?(kind=Decls.(IsDefinition Definition))
      ?(udecl=UState.default_univ_decl) ?(scope=Locality.default_scope)
      ?(clearbody=false) ?hook ?typing_flags ?user_warns ?(ntns=[]) () =
    let loc = match loc with
      | None -> Loc.get_current_command_loc()
      | Some _ -> loc
    in
    { poly; inline; kind; udecl; scope; hook; typing_flags; clearbody; user_warns; ntns; loc }
end

(** Declaration of constants and parameters *)

(* Deferred proofs: monomorphic, opaque, and udecl is for body+type *)
type 'eff deferred_opaque_proof_body = {
  body : ((Constr.t * Univ.ContextSet.t) * 'eff) Future.computation;
  feedback_id : Stateid.t option
  (* State id on which the completion of type checking is reported *)
}

(* Opacity of default proofs, possibly with private universes *)
type default_body_opacity =
  | Transparent
    (* udecl is for body+type; all universes are in proof_entry_universes  *)
  | Opaque of Univ.ContextSet.t
    (* if poly, the private uctx, udecl excludes the private uctx *)
    (* if mono, the body uctx *)

(* Default (non-deferred) proofs/definitions, possibly with effects *)
type 'eff default_proof_body = {
  body : Constr.t * 'eff;
  opaque : default_body_opacity
}

(* A proof body is either immediate or deferred *)
type 'eff proof_body =
  | DeferredOpaque of 'eff deferred_opaque_proof_body
  | Default of 'eff default_proof_body

(* A proof entry, parameterized with its kind of proof body *)
type 'body pproof_entry = {
  proof_entry_body   : 'body;
  proof_entry_secctx : Id.Set.t option;
  (* List of section variables *)
  proof_entry_type        : Constr.types option;
  (* the initial type if deferred *)
  proof_entry_universes   : UState.named_universes_entry;
  (* refers to:
     - the initial uctx if opaque deferred;
     - the uctx of type only if opaque private;
     - the full uctx otherwise *)
  proof_entry_inline_code : bool;
}

(* The most general form of proof entry *)
type proof_entry = Evd.side_effects proof_body pproof_entry

type parameter_entry = {
  parameter_entry_secctx : Id.Set.t option;
  parameter_entry_type : Constr.types;
  parameter_entry_universes : UState.named_universes_entry;
  parameter_entry_inline_code : Entries.inline;
}

type primitive_entry = {
  prim_entry_type : (Constr.types * UState.named_universes_entry) option;
  prim_entry_content : CPrimitives.op_or_type;
}

type symbol_entry = {
  symb_entry_type : Constr.types;
  symb_entry_unfold_fix: bool;
  symb_entry_universes : UState.named_universes_entry;
}

let default_univ_entry = UState.Monomorphic_entry Univ.ContextSet.empty
let default_named_univ_entry = default_univ_entry, UnivNames.empty_binders

let extract_monomorphic = function
  | UState.Monomorphic_entry ctx -> Entries.Monomorphic_entry, ctx
  | UState.Polymorphic_entry uctx -> Entries.Polymorphic_entry uctx, Univ.ContextSet.empty

let instance_of_univs = function
  | UState.Monomorphic_entry _, _ -> UVars.Instance.empty
  | UState.Polymorphic_entry uctx, _ -> UVars.UContext.instance uctx

let add_mono_uctx uctx = function
  | UState.Monomorphic_entry ctx, ubinders -> UState.Monomorphic_entry (Univ.ContextSet.union (UState.context_set uctx) ctx), ubinders
  | UState.Polymorphic_entry _, _ as x -> assert (Univ.ContextSet.is_empty (UState.context_set uctx)); x

let make_ubinders uctx (univs, ubinders as u) = match univs with
  | UState.Monomorphic_entry _ -> (UState.Monomorphic_entry uctx, ubinders)
  | UState.Polymorphic_entry _ -> u

let { Goptions.get = private_poly_univs } =
  Goptions.declare_bool_option_and_ref
    ~key:["Private";"Polymorphic";"Universes"]
    ~value:true
    ()

let universes_of_body_type ~used_univs body typ =
  let used_univs_typ = Option.cata (Vars.universes_of_constr ~init:used_univs) used_univs typ in
  let used_univs = Vars.universes_of_constr body ~init:used_univs_typ in
  used_univs_typ, used_univs

let make_univs_deferred_private_mono ~initial_euctx ?feedback_id ~uctx ~udecl body typ =
  let _, used_univs = universes_of_body_type ~used_univs:Univ.Level.Set.empty body typ in
  let uctx = UState.constrain_variables (fst (UState.context_set initial_euctx)) uctx in
  (* For vi2vo compilation proofs are computed now but we need to
     complement the univ constraints of the typ with the ones of
     the body.  So we keep the two sets distinct. *)
  let uctx_body = UState.restrict uctx used_univs in
  UState.check_mono_univ_decl uctx_body udecl

let make_univs_immediate_private_mono ~initial_euctx ~uctx ~udecl ~eff ~used_univs body typ =
  let utyp = UState.univ_entry ~poly:false initial_euctx in
  let _, used_univs = universes_of_body_type ~used_univs body typ in
  let ubody =
    let uctx = UState.constrain_variables (fst (UState.context_set initial_euctx)) uctx in
    (* For vi2vo compilation proofs are computed now but we need to
       complement the univ constraints of the typ with the ones of
       the body.  So we keep the two sets distinct. *)
    let uctx_body = UState.restrict uctx used_univs in
    UState.check_mono_univ_decl uctx_body udecl in
  initial_euctx, utyp, used_univs, Default { body = (body, eff); opaque = Opaque ubody }

let make_univs_immediate_private_poly ~uctx ~udecl ~eff ~used_univs body typ =
  let used_univs_typ, used_univs = universes_of_body_type ~used_univs body typ in
  let uctx' = UState.restrict uctx used_univs_typ in
  let utyp = UState.check_univ_decl ~poly:true uctx' udecl in
  let ubody =
    let uctx = UState.restrict uctx used_univs in
    Univ.ContextSet.diff
      (UState.context_set uctx)
      (UState.context_set uctx')
  in
  uctx', utyp, used_univs, Default { body = (body, eff); opaque = Opaque ubody }

let make_univs_immediate_default ~poly ~opaque ~uctx ~udecl ~eff ~used_univs body typ =
  let _, used_univs = universes_of_body_type ~used_univs body typ in
  (* Since the proof is computed now, we can simply have 1 set of
     constraints in which we merge the ones for the body and the ones
     for the typ. We recheck the declaration after restricting with
     the actually used universes.
     TODO: check if restrict is really necessary now. *)
  let uctx = UState.restrict uctx used_univs in
  let utyp = UState.check_univ_decl ~poly uctx udecl in
  let utyp = match fst utyp with
    | Polymorphic_entry _ -> utyp
    | Monomorphic_entry uctx ->
      (* the constraints from the body may depend on universes from
         the side effects, so merge it all together.
         Example failure if we don't is "l1" in test-suite/success/rewrite.v.

         Not sure if it makes more sense to merge them in the ustate
         before restrict/check_univ_decl or here. Since we only do it
         when monomorphic it shouldn't really matter. *)
      Monomorphic_entry (Univ.ContextSet.union uctx (Safe_typing.universes_of_private eff.Evd.seff_private)), snd utyp
  in
  uctx, utyp, used_univs, Default { body = (body, eff); opaque = if opaque then Opaque Univ.ContextSet.empty else Transparent }

let make_univs_immediate ~poly ?keep_body_ucst_separate ~opaque ~uctx ~udecl ~eff ~used_univs body typ =
  (* allow_deferred case *)
  match keep_body_ucst_separate with
  | Some initial_euctx when not poly -> make_univs_immediate_private_mono ~initial_euctx ~uctx ~udecl ~eff ~used_univs body typ
  | _ ->
  (* private_poly_univs case *)
  if poly && opaque && private_poly_univs ()
  then make_univs_immediate_private_poly ~uctx ~udecl ~eff ~used_univs body typ
  else make_univs_immediate_default ~poly ~opaque ~uctx ~udecl ~eff ~used_univs body typ

(** [univsbody] are universe-constraints attached to the body-only,
   used in vio-delayed opaque constants and private poly universes *)
let definition_entry_core ?using ?(inline=false) ?types
    ?(univs=default_named_univ_entry) body =
  { proof_entry_body = body;
    proof_entry_secctx = using;
    proof_entry_type = types;
    proof_entry_universes = univs;
    proof_entry_inline_code = inline}

let pure_definition_entry ?(opaque=Transparent) ?using ?inline ?types ?univs body =
  definition_entry_core ?using ?inline ?types ?univs body

let definition_entry ?(opaque=false) ?using ?inline ?types ?univs body =
  let opaque = if opaque then Opaque Univ.ContextSet.empty else Transparent in
  definition_entry_core ?using ?inline ?types ?univs (Default { body = (body, Evd.empty_side_effects); opaque })

let delayed_definition_entry ?feedback_id ?using ~univs ?types body =
  definition_entry_core ?using ?types ~univs (DeferredOpaque { body; feedback_id })

let parameter_entry ?inline ?(univs=default_named_univ_entry) typ = {
  parameter_entry_secctx = None;
  parameter_entry_type = typ;
  parameter_entry_universes = univs;
  parameter_entry_inline_code = inline;
}

let primitive_entry ?types c = {
  prim_entry_type = types;
  prim_entry_content = c;
}

let symbol_entry ?(univs=default_named_univ_entry) ~unfold_fix symb_entry_type = {
  symb_entry_universes = univs;
  symb_entry_unfold_fix = unfold_fix;
  symb_entry_type;
}

type constant_entry =
  | DefinitionEntry of proof_entry
  | ParameterEntry of parameter_entry
  | PrimitiveEntry of primitive_entry
  | SymbolEntry of symbol_entry

module ProofEntry = struct

  let map_entry_body ~f = function
    | Default { body = body; opaque } -> Default { body = f body; opaque }
    | DeferredOpaque { body; feedback_id } ->
      let body = Future.chain body (fun ((b,c),eff) -> let b, eff = f (b,eff) in ((b,c),eff)) in
      DeferredOpaque { body; feedback_id }

  let map_entry ~f entry =
    { entry with
      proof_entry_body = map_entry_body ~f:(on_fst f) entry.proof_entry_body;
      proof_entry_type = Option.map f entry.proof_entry_type }

  let get_opacity entry =
    match entry.proof_entry_body with
    | Default { body; opaque = Transparent } -> false
    | Default { body; opaque = Opaque _ } -> true
    | DeferredOpaque _ -> true

  let force_entry_body entry =
    match entry.proof_entry_body with
    | Default { body; opaque } -> body, opaque
    | DeferredOpaque { body; feedback_id = Some _ } -> CErrors.anomaly (str "Forcing a proof with feedback")
    | DeferredOpaque { body; feedback_id = None } ->
      let (body, uctx), eff = Future.force body in
      (body, eff), Opaque uctx

  let force_extract_body entry =
    match entry.proof_entry_body with
    | Default { body = (body, eff); opaque = Transparent } -> ((body, Univ.ContextSet.empty), eff), false, None
    | Default { body = (body, eff); opaque = Opaque uctx } -> ((body, uctx), eff), true, None
    | DeferredOpaque { body; feedback_id } -> Future.force body, true, feedback_id

  let get_entry_body entry =
    let (body, eff), opaque = force_entry_body entry in
    let uctx = match opaque with
      | Opaque uctx -> uctx
      | Transparent -> Univ.ContextSet.empty
    in
    (body, uctx), eff

  let rec shrink ctx sign c t accu =
    let open Constr in
    let open Vars in
    match ctx, sign with
    | [], [] -> (c, t, accu)
    | p :: ctx, decl :: sign ->
      if noccurn 1 c && noccurn 1 t then
        let c = subst1 mkProp c in
        let t = subst1 mkProp t in
        shrink ctx sign c t accu
      else
        let c = Term.mkLambda_or_LetIn p c in
        let t = Term.mkProd_or_LetIn p t in
        let accu = if Context.Rel.Declaration.is_local_assum p
          then EConstr.mkVar (NamedDecl.get_id decl) :: accu
          else accu
        in
        shrink ctx sign c t accu
    | _ -> assert false

  (* If [sign] is [x1:T1..xn:Tn], [c] is [fun x1:T1..xn:Tn => c']
     and [t] is [forall x1:T1..xn:Tn, t'], returns a new [c'] and [t'],
     where all non-dependent [xi] are removed, as well as a
     restriction [args] of [x1..xn] such that [c' args] = [c x1..xn] *)
  let shrink_entry sign body typ =
    let typ = match typ with
      | None -> assert false
      | Some t -> t
    in
    let (ctx, body, typ) = Term.decompose_lambda_prod_n_decls (List.length sign) body typ in
    let (body, typ, args) = shrink ctx sign body typ [] in
    body, Some typ, args

end

let local_csts = Summary.ref ~name:"local-csts" Cset_env.empty

let is_local_constant c = Cset_env.mem c !local_csts

type constant_obj = {
  cst_kind : Decls.logical_kind;
  cst_locl : Locality.import_status;
  cst_warn : Globnames.extended_global_reference UserWarn.with_qf option;
  cst_loc : Loc.t option;
}

let load_constant i ((sp,kn), obj) =
  if Nametab.exists_cci sp then
    raise (DeclareUniv.AlreadyDeclared (None, Libnames.basename sp));
  let con = Global.constant_of_delta_kn kn in
  let gr = GlobRef.ConstRef con in
  Nametab.push ?user_warns:obj.cst_warn (Nametab.Until i) sp gr;
  Dumpglob.add_constant_kind con obj.cst_kind;
  obj.cst_loc |> Option.iter (fun loc -> Nametab.set_cci_src_loc (TrueGlobal gr) loc);
  begin match obj.cst_locl with
    | Locality.ImportNeedQualified -> local_csts := Cset_env.add con !local_csts
    | Locality.ImportDefaultBehavior -> ()
  end

(* Opening means making the name without its module qualification available *)
let open_constant i ((sp,kn), obj) =
  (* Never open a local definition *)
  match obj.cst_locl with
  | Locality.ImportNeedQualified -> ()
  | Locality.ImportDefaultBehavior ->
    let con = Global.constant_of_delta_kn kn in
    Nametab.push (Nametab.Exactly i) sp (GlobRef.ConstRef con)

let exists_name id =
  Decls.variable_exists id || Global.exists_objlabel (Label.of_id id)

let check_exists id =
  if exists_name id then
    raise (DeclareUniv.AlreadyDeclared (None, id))

let cache_constant ((sp,kn), obj) =
  let kn = Global.constant_of_delta_kn kn in
  let gr = GlobRef.ConstRef kn in
  Nametab.push ?user_warns:obj.cst_warn (Nametab.Until 1) sp gr;
  Dumpglob.add_constant_kind kn obj.cst_kind;
  obj.cst_loc |> Option.iter (fun loc -> Nametab.set_cci_src_loc (TrueGlobal gr) loc)

let discharge_constant obj = Some obj

let classify_constant cst = Libobject.Substitute

let (objConstant : (Id.t * constant_obj) Libobject.Dyn.tag) =
  let open Libobject in
  declare_named_object_full { (default_object "CONSTANT") with
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = simple_open open_constant;
    classify_function = classify_constant;
    subst_function = ident_subst_function;
    discharge_function = discharge_constant }

let inConstant v = Libobject.Dyn.Easy.inj v objConstant

(* Register the libobjects attached to the constants *)
let register_constant loc cst kind ?user_warns local =
  (* Register the declaration *)
  let id = Label.to_id (Constant.label cst) in
  let o = inConstant (id, { cst_kind = kind; cst_locl = local; cst_warn = user_warns; cst_loc = loc; }) in
  let () = Lib.add_leaf o in
  (* Register associated data *)
  Impargs.declare_constant_implicits cst;
  Notation.declare_ref_arguments_scope (GlobRef.ConstRef cst)

let register_side_effect (c, body, role) =
  (* Register the body in the opaque table *)
  let () = match body with
  | None -> ()
  | Some opaque -> Opaques.declare_private_opaque opaque
  in
  let () = register_constant (Loc.get_current_command_loc()) c Decls.(IsProof Theorem) Locality.ImportDefaultBehavior in
  match role with
  | None -> ()
  | Some (Evd.Schema (ind, kind)) -> DeclareScheme.declare_scheme SuperGlobal kind (ind,c)

let get_roles export eff =
  let map (c, body) =
    let role = try Some (Cmap.find c eff.Evd.seff_roles) with Not_found -> None in
    (c, body, role)
  in
  List.map map export

let export_side_effects eff =
  let export = Global.export_private_constants eff.Evd.seff_private in
  let export = get_roles export eff in
  List.iter register_side_effect export

let record_aux env s_ty s_bo =
  let open Environ in
  let in_ty = keep_hyps env s_ty in
  let v =
    String.concat " "
      (CList.map_filter (fun decl ->
          let id = NamedDecl.get_id decl in
          if List.exists (NamedDecl.get_id %> Id.equal id) in_ty then None
          else Some (Id.to_string id))
        (keep_hyps env s_bo)) in
  Aux_file.record_in_aux "context_used" v

let cast_pure_proof_entry (e : Constr.constr pproof_entry) =
  let univ_entry, ctx = extract_monomorphic (fst (e.proof_entry_universes)) in
  { Entries.definition_entry_body = e.proof_entry_body;
    definition_entry_secctx = e.proof_entry_secctx;
    definition_entry_type = e.proof_entry_type;
    definition_entry_universes = univ_entry;
    definition_entry_inline_code = e.proof_entry_inline_code;
  },
  ctx

type ('a, 'b) effect_entry =
| ImmediateEffectEntry : (private_constants Entries.proof_output, unit) effect_entry
| DeferredEffectEntry : (private_constants Entries.proof_output Future.computation, unit) effect_entry
| PureEntry : (Constr.constr, Constr.constr) effect_entry

let section_context_of_opaque_proof_entry (type a b) (entry : (a, b) effect_entry) (body : a) typ =
  let open Environ in
  let env = Global.env () in
  let hyp_typ, hyp_def =
    if List.is_empty (Environ.named_context env) then
      Id.Set.empty, Id.Set.empty
    else
      let ids_typ = global_vars_set env typ in
      let (pf : Constr.constr), env = match entry with
        | PureEntry -> body, env
        | ImmediateEffectEntry ->
          let (pf, _), eff = body in
          let env = Safe_typing.push_private_constants env eff in
          pf, env
        | DeferredEffectEntry ->
          let (pf, _), eff = Future.force body in
          let env = Safe_typing.push_private_constants env eff in
          pf, env
      in
      let vars = global_vars_set env pf in
      ids_typ, vars
  in
  let () = if Aux_file.recording () then record_aux env hyp_typ hyp_def in
  Environ.really_needed env (Id.Set.union hyp_typ hyp_def)

let cast_opaque_proof_entry (type a b) (entry : (a, b) effect_entry) (e : a pproof_entry) : b Entries.opaque_entry * _ =
  let typ = match e.proof_entry_type with
  | None -> assert false
  | Some typ -> typ
  in
  let secctx = match e.proof_entry_secctx with
  | None -> section_context_of_opaque_proof_entry entry e.proof_entry_body typ
  | Some hyps -> hyps
  in
  let body : b = match entry with
  | PureEntry -> e.proof_entry_body
  | ImmediateEffectEntry -> ()
  | DeferredEffectEntry -> ()
  in
  let univ_entry, ctx = extract_monomorphic (fst (e.proof_entry_universes)) in
  { Entries.opaque_entry_body = body;
    opaque_entry_secctx = secctx;
    opaque_entry_type = typ;
    opaque_entry_universes = univ_entry;
  },
  ctx

let feedback_axiom () = Feedback.(feedback AddedAxiom)

let is_unsafe_typing_flags flags =
  let flags = Option.default (Global.typing_flags ()) flags in
  let open Declarations in
  not (flags.check_universes && flags.check_guarded && flags.check_positive)

let declare_constant ~loc ?(local = Locality.ImportDefaultBehavior) ~name ~kind ~typing_flags ?user_warns cd =
  let before_univs = Global.universes () in
  let make_constant = function
  (* Logically define the constant and its subproofs, no libobject tampering *)
    | DefinitionEntry de ->
      (* We deal with side effects *)
      (match de.proof_entry_body with
      | Default { body = (body, eff); opaque = Transparent } ->
        (* This globally defines the side-effects in the environment
           and registers their libobjects. *)
        let () = export_side_effects eff in
        let de = { de with proof_entry_body = body } in
        let e, ctx = cast_pure_proof_entry de in
        let ubinders = make_ubinders ctx de.proof_entry_universes in
        (* We register the global universes after exporting side-effects, since
           the latter depend on the former. *)
        let () = Global.push_context_set ctx in
        Entries.DefinitionEntry e, false, ubinders, None, ctx
      | Default { body = (body, eff); opaque = Opaque body_uctx } ->
        let body = ((body, body_uctx), eff.Evd.seff_private) in
        let de = { de with proof_entry_body = body } in
        let cd, ctx = cast_opaque_proof_entry ImmediateEffectEntry de in
        let ubinders = make_ubinders ctx de.proof_entry_universes in
        let () = Global.push_context_set ctx in
        Entries.OpaqueEntry cd, false, ubinders, Some (Future.from_val body, None), ctx
      | DeferredOpaque { body; feedback_id } ->
        let map (body, eff) = body, eff.Evd.seff_private in
        let body = Future.chain body map in
        let de = { de with proof_entry_body = body } in
        let cd, ctx = cast_opaque_proof_entry DeferredEffectEntry de in
        let ubinders = make_ubinders ctx de.proof_entry_universes in
        let () = Global.push_context_set ctx in
        Entries.OpaqueEntry cd, false, ubinders, Some (body, feedback_id), ctx)
    | ParameterEntry e ->
      let univ_entry, ctx = extract_monomorphic (fst e.parameter_entry_universes) in
      let ubinders = make_ubinders ctx e.parameter_entry_universes in
      let () = Global.push_context_set ctx in
      let e = {
        Entries.parameter_entry_secctx = e.parameter_entry_secctx;
        Entries.parameter_entry_type = e.parameter_entry_type;
        Entries.parameter_entry_universes = univ_entry;
        Entries.parameter_entry_inline_code = e.parameter_entry_inline_code;
      } in
      Entries.ParameterEntry e, not (Lib.is_modtype_strict()), ubinders, None, ctx
    | PrimitiveEntry e ->
      let typ, univ_entry, ctx = match e.prim_entry_type with
      | None ->
        None, (UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders), Univ.ContextSet.empty
      | Some (typ, entry_univs) ->
        let univ_entry, ctx = extract_monomorphic (fst entry_univs) in
        Some (typ, univ_entry), entry_univs, ctx
      in
      let () = Global.push_context_set ctx in
      let e = {
        Entries.prim_entry_type = typ;
        Entries.prim_entry_content = e.prim_entry_content;
      } in
      let ubinders = make_ubinders ctx univ_entry in
      Entries.PrimitiveEntry e, false, ubinders, None, ctx
    | SymbolEntry { symb_entry_type=typ; symb_entry_unfold_fix=un_fix; symb_entry_universes=entry_univs } ->
      let univ_entry, ctx = extract_monomorphic (fst entry_univs) in
      let () = Global.push_context_set ctx in
      let e = {
        Entries.symb_entry_type = typ;
        Entries.symb_entry_unfold_fix = un_fix;
        Entries.symb_entry_universes = univ_entry;
      } in
      let ubinders = make_ubinders ctx entry_univs in
      Entries.SymbolEntry e, false, ubinders, None, ctx
  in
  let declare_opaque kn = function
    | None -> ()
    | Some (body, feedback_id) ->
      let open Declarations in
      match (Global.lookup_constant kn).const_body with
      | OpaqueDef o ->
        let (_, _, _, i) = Opaqueproof.repr o in
        Opaques.declare_defined_opaque ?feedback_id i body
      | Def _ | Undef _ | Primitive _ | Symbol _ -> assert false
  in
  let () = check_exists name in
  let decl, unsafe, ubinders, delayed, ctx = make_constant cd in
  let kn = Global.add_constant ?typing_flags name decl in
  let () =
    let is_new_constraint (u,_,v as c) =
      match UGraph.check_declared_universes before_univs Univ.Level.Set.(add u (add v empty)) with
      | Ok () -> not (UGraph.check_constraint before_univs c)
      | Error _ -> true
    in
    let ctx = on_snd (Univ.Constraints.filter is_new_constraint) ctx in
    DeclareUniv.add_constraint_source (ConstRef kn) ctx
  in
  let () = DeclareUniv.declare_univ_binders (GlobRef.ConstRef kn) ubinders in
  let () = declare_opaque kn delayed in
  let () = register_constant loc kn kind local ?user_warns in
  if unsafe || is_unsafe_typing_flags typing_flags then feedback_axiom();
  kn

let declare_private_constant ?role ?(local = Locality.ImportDefaultBehavior) ~name ~kind ~opaque de =
  let de, ctx =
    if not opaque then
      let de, ctx = cast_pure_proof_entry de in
      DefinitionEff de, ctx
    else
      let de, ctx = cast_opaque_proof_entry PureEntry de in
      OpaqueEff de, ctx
  in
  let kn, eff = Global.add_private_constant name ctx de in
  let () = if Univ.Level.Set.is_empty (fst ctx) then ()
    else DeclareUniv.declare_univ_binders (ConstRef kn)
        (Monomorphic_entry ctx, UnivNames.empty_binders)
  in
  let () = register_constant (Loc.get_current_command_loc()) kn kind local in
  let seff_roles = match role with None -> Cmap.empty | Some r -> Cmap.singleton kn r in
  let eff = { Evd.seff_private = eff; Evd.seff_roles; } in
  kn, eff

let inline_private_constants ~uctx env (body, eff) =
  let body, ctx = Safe_typing.inline_private_constants env (body, eff.Evd.seff_private) in
  let uctx = UState.merge ~sideff:true Evd.univ_rigid uctx ctx in
  body, uctx

(** Declaration of section variables and local definitions *)
type variable_declaration =
  | SectionLocalDef of {
      clearbody : bool;
      entry : proof_entry;
    }
  | SectionLocalAssum of {
      typ : Constr.types;
      impl : Glob_term.binding_kind;
      univs : UState.named_universes_entry;
    }

(* This object is only for things which iterate over objects to find
   variables (only Prettyp.print_context AFAICT) *)
let objVariable : Id.t Libobject.Dyn.tag =
  let open Libobject in
  declare_object_full { (default_object "VARIABLE") with
    classify_function = (fun _ -> Dispose)}

let inVariable v = Libobject.Dyn.Easy.inj v objVariable

let declare_variable ~name ~kind ~typing_flags d =
  (* Variables are distinguished by only short names *)
  if Decls.variable_exists name then
    raise (DeclareUniv.AlreadyDeclared (None, name));

  let impl,opaque = match d with (* Fails if not well-typed *)
    | SectionLocalAssum {typ;impl;univs} ->
      let () = match fst univs with
        | UState.Monomorphic_entry uctx ->
          (* XXX [snd univs] is ignored, should we use it? *)
          DeclareUniv.name_mono_section_univs (fst uctx);
          Global.push_context_set uctx
        | UState.Polymorphic_entry uctx -> Global.push_section_context uctx
      in
      let () = Global.push_named_assum (name,typ) in
      impl, true
    | SectionLocalDef { clearbody; entry = de } ->
      (* The body should already have been forced upstream because it is a
         section-local definition, but it's not enforced by typing *)
      let ((body, body_uctx), eff), opaque, feedback_id = ProofEntry.force_extract_body de in
      let () = export_side_effects eff in
      (* We must declare the universe constraints before type-checking the
         term. *)
      let univs = match fst de.proof_entry_universes with
        | UState.Monomorphic_entry uctx ->
          DeclareUniv.name_mono_section_univs (fst uctx);
          Global.push_context_set (Univ.ContextSet.union uctx body_uctx);
          UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders
        | UState.Polymorphic_entry uctx ->
          Global.push_section_context uctx;
          let mk_anon_names u =
            let qs, us = UVars.Instance.to_array u in
            Array.make (Array.length qs) Anonymous, Array.make (Array.length us) Anonymous
          in
          Global.push_section_context
            (UVars.UContext.of_context_set mk_anon_names Sorts.QVar.Set.empty body_uctx);
          UState.Polymorphic_entry UVars.UContext.empty, UnivNames.empty_binders
      in
      let se = if opaque then
          let cname = Id.of_string (Id.to_string name ^ "_subproof") in
          let cname = Namegen.next_global_ident_away cname Id.Set.empty in
          let de = {
            proof_entry_body = DeferredOpaque { body = Future.from_val ((body, Univ.ContextSet.empty), Evd.empty_side_effects); feedback_id };
            proof_entry_secctx = None; (* de.proof_entry_secctx is NOT respected *)
            proof_entry_type = de.proof_entry_type;
            proof_entry_universes = univs;
            proof_entry_inline_code = de.proof_entry_inline_code;
          }
          in
          let kn = declare_constant ~name:cname ~loc:None
              ~local:ImportNeedQualified ~kind:(IsProof Lemma) ~typing_flags
              (DefinitionEntry de)
          in
          {
            Entries.secdef_body = Constr.mkConstU (kn, UVars.Instance.empty);
            secdef_type = None;
          }
        else {
        Entries.secdef_body = body;
        secdef_type = de.proof_entry_type;
      } in
      let () = Global.push_named_def (name, se) in
      (* opaque implies clearbody, so we don't see useless "foo := foo_subproof" in the context *)
      Glob_term.Explicit, opaque || clearbody
  in
  Nametab.push (Nametab.Until 1) (Libnames.make_path DirPath.empty name) (GlobRef.VarRef name);
  Decls.(add_variable_data name {opaque;kind});
  Lib.add_leaf (inVariable name);
  Impargs.declare_var_implicits ~impl name;
  Notation.declare_ref_arguments_scope (GlobRef.VarRef name)

(* Declaration messages *)

let pr_rank i = pr_nth (i+1)

let fixpoint_message indexes l =
  Flags.if_verbose Feedback.msg_info (match l with
  | [] -> CErrors.anomaly (Pp.str "no recursive definition.")
  | [id] -> Id.print id ++ str " is recursively defined" ++
      (match indexes with
         | Some [|i|] -> str " (guarded on "++pr_rank i++str " argument)"
         | _ -> mt ())
  | l -> hov 0 (prlist_with_sep pr_comma Id.print l ++
                  spc () ++ str "are recursively defined" ++
                  match indexes with
                    | Some a -> spc () ++ str "(guarded respectively on " ++
                        prvect_with_sep pr_comma pr_rank a ++
                        str " arguments)"
                    | None -> mt ()))

let cofixpoint_message l =
  Flags.if_verbose Feedback.msg_info (match l with
  | [] -> CErrors.anomaly (Pp.str "No corecursive definition.")
  | [id] -> Id.print id ++ str " is corecursively defined"
  | l -> hov 0 (prlist_with_sep pr_comma Id.print l ++
                    spc () ++ str "are corecursively defined"))

let recursive_message indexes l =
  match indexes with
  | None -> cofixpoint_message l
  | Some indexes -> fixpoint_message (Some indexes) l

let definition_message id =
  Flags.if_verbose Feedback.msg_info (Id.print id ++ str " is defined")

let assumption_message id =
  (* Changing "assumed" to "declared", "assuming" referring more to
  the type of the object than to the name of the object (see
  discussion on coqdev: "Chapter 4 of the Reference Manual", 8/10/2015) *)
  Flags.if_verbose Feedback.msg_info (Id.print id ++ str " is declared")

module Internal = struct

  module Constant = struct
    type t = constant_obj
    let tag = objConstant
    let kind obj = obj.cst_kind
  end

  let objVariable = objVariable

  let export_side_effects = export_side_effects

end

(* The word [proof] is to be understood as [justification] *)
(* A possible alternatve would be [evidence]?? *)
type closed_proof_output = ((Constr.t * Evd.side_effects) * Constr.t option) list * UState.t

type proof_object =
  | DefaultProof of
      { proof : closed_proof_output
      ; opaque : bool
      ; using : Names.Id.Set.t option
      ; keep_body_ucst_separate : UState.t option
      }
  | DeferredOpaqueProof of
      { deferred_proof : closed_proof_output Future.computation
      ; using : Names.Id.Set.t option
      ; initial_proof_data : Proof.data
      ; feedback_id : Stateid.t
      ; initial_euctx : UState.t
      }

let future_map2_pair_list_distribute p l f =
  List.map_i (fun i c -> f (Future.chain p (fun (a, b) -> (List.nth a i, b))) c) 0 l

let process_proof ~info:Info.({ udecl; poly }) ?(is_telescope=false) = function
  | DefaultProof { proof = (entries, uctx); opaque; using; keep_body_ucst_separate } ->
    (* Force transparency for Derive-like dependent statements *)
    let opaques =
      let n = List.length entries in
      List.init n (fun i ->
          if i < n-1 && is_telescope then (* waiting for addition of cinfo-based opacity in #19029 *) false
          else opaque) in
    (* Multiple entries mean either a recursive block of definitions
       (as in Co/Fixpoint) or a sequence of dependent definitions (as
       in "Derive"). In the second case, the dependency in the
       previous entries requires to accumulate the universes from the
       previous definitions *)
    snd (List.fold_left2_map (fun used_univs ((body, eff), typ) opaque ->
        let uctx, univs, used_univs, body =
          make_univs_immediate ~poly ?keep_body_ucst_separate ~opaque ~uctx ~udecl ~eff ~used_univs body typ in
        (used_univs, (definition_entry_core ?using ~univs ?types:typ body, uctx))) Univ.Level.Set.empty entries opaques)
  | DeferredOpaqueProof { deferred_proof = bodies; using; initial_proof_data; feedback_id; initial_euctx } ->
    let { Proof.poly; entry; sigma } = initial_proof_data in
    (* Deferred multiple entries currently assume either a mutual
       Co/Fixpoint or no dependency (thus no "Derive"); to support
       "Derive"-like statements, we would need a combinator on futures
       that fold used universes *)
    future_map2_pair_list_distribute bodies (Proofview.initial_goals entry)
        (fun body_typ_uctx (_, _, initial_typ) ->
           (* Testing if evar-closed? *)
           let initial_typ = Evarutil.nf_evars_universes sigma (EConstr.Unsafe.to_constr initial_typ) in
           (* The flags keep_body_ucst_separate, opaque, etc. should be consistent with evar-closedness? *)
           let univs = UState.univ_entry ~poly:false initial_euctx in
           let body = Future.chain body_typ_uctx (fun (((body, eff), _typ), uctx) ->
               let uctx = make_univs_deferred_private_mono ~initial_euctx ~uctx ~udecl body (Some initial_typ) in
               ((body, uctx), eff)) in
           (delayed_definition_entry ?using ~univs ~types:initial_typ ~feedback_id body, initial_euctx))

let ustate_of_proof = function
  | DefaultProof { proof = (_entries, uctx) } -> uctx
  | DeferredOpaqueProof { initial_euctx } -> initial_euctx

let declare_definition_scheme ~internal ~univs ~role ~name ?loc c =
  let kind = Decls.(IsDefinition Scheme) in
  let entry = pure_definition_entry ~univs c in
  let kn, eff = declare_private_constant ~role ~kind ~name ~opaque:false entry in
  Dumpglob.dump_definition
    (CAst.make ?loc (Constant.label kn |> Label.to_id)) false "scheme";
  let () = if internal then () else definition_message name in
  kn, eff

(* Locality stuff *)
let declare_entry ~loc ~name ?(scope=Locality.default_scope) ?(clearbody=false) ~kind ~typing_flags ~user_warns ?hook ?(obls=[]) ~impargs ~uctx entry =
  let should_suggest =
    ProofEntry.get_opacity entry
    && not (List.is_empty (Global.named_context()))
    && Option.is_empty entry.proof_entry_secctx
  in
  let dref = match scope with
  | Locality.Discharge ->
    let () = declare_variable ~typing_flags ~name ~kind (SectionLocalDef {clearbody; entry}) in
    if should_suggest then Proof_using.suggest_variable (Global.env ()) name;
    Names.GlobRef.VarRef name
  | Locality.Global local ->
    assert (not clearbody);
    let kn = declare_constant ~loc ~name ~local ~kind ~typing_flags ?user_warns (DefinitionEntry entry) in
    let gr = Names.GlobRef.ConstRef kn in
    if should_suggest then Proof_using.suggest_constant (Global.env ()) kn;
    gr
  in
  let () = Impargs.maybe_declare_manual_implicits false dref impargs in
  let () = definition_message name in
  Hook.call ?hook { Hook.S.uctx; obls; scope; dref };
  dref

let warn_let_as_axiom =
  CWarnings.create ~name:"let-as-axiom" ~category:CWarnings.CoreCategories.vernacular
    Pp.(fun id -> strbrk "Let definition" ++ spc () ++ Names.Id.print id ++
                  spc () ++ strbrk "declared as an axiom.")

(* Declare an assumption when not in a section: Parameter/Axiom but also
   Variable/Hypothesis seen as Local Parameter/Axiom *)
let declare_parameter ~name ~scope ~hook ~impargs ~uctx pe =
  let local = match scope with
    | Locality.Discharge -> warn_let_as_axiom name; Locality.ImportNeedQualified
    | Locality.Global local -> local
  in
  let kind = Decls.(IsAssumption Conjectural) in
  let decl = ParameterEntry pe in
  let cst = declare_constant ~loc:None ~name ~local ~kind ~typing_flags:None decl in
  let dref = Names.GlobRef.ConstRef cst in
  let () = Impargs.maybe_declare_manual_implicits false dref impargs in
  let () = assumption_message name in
  let () = Hook.(call ?hook { S.uctx; obls = []; scope; dref}) in
  cst

(* Using processing *)
let interp_proof_using_gen f env evd cinfo using =
  let cextract v (fixnames, terms) =
    let name, new_terms = f v in
    name :: fixnames, new_terms @ terms
  in
  let fixnames, terms = CList.fold_right cextract cinfo ([],[]) in
  Proof_using.definition_using env evd ~fixnames ~terms ~using

let interp_proof_using_cinfo env evd cinfo using =
  let f { CInfo.name; typ; _ } = name, [EConstr.of_constr typ] in
  interp_proof_using_gen f env evd cinfo using

let gather_mutual_using_data cinfo =
  List.fold_left2 (fun acc CInfo.{name} (body, typ) ->
      let l = Option.List.flatten EConstr.[Option.map of_constr typ; Some (of_constr body)] in
      (name, l) :: acc) [] cinfo

let interp_mutual_using env cinfo bodies_types using =
  let evd = Evd.from_env env in
  Option.map (fun using ->
      let cinfos = gather_mutual_using_data cinfo bodies_types in
      let f x = x in
      interp_proof_using_gen f env evd cinfos using)
    using

let declare_possibly_mutual_definitions ~info ~cinfo ~obls ?(is_telescope=false) obj =
  let entries = process_proof ~info ~is_telescope obj in
  let { Info.hook; scope; clearbody; kind; typing_flags; user_warns; ntns; _ } = info in
  let _, refs = List.fold_left2_map (fun subst CInfo.{name; impargs} (entry, uctx) ->
      (* replacing matters for Derive-like statement but it does not hurt otherwise *)
      let entry = ProofEntry.map_entry entry ~f:(Vars.replace_vars subst) in
      let gref = declare_entry ~loc:info.loc ~name ~scope ~clearbody ~kind ?hook ~impargs ~typing_flags ~user_warns ~obls ~uctx entry in
      let inst = instance_of_univs entry.proof_entry_universes in
      let const = Constr.mkRef (gref, inst) in
      ((name, const) :: subst, gref)) [] cinfo entries in
  let () =
    (* For the recursive case, we override the temporary notations used while proving, now using the global names *)
    let local = info.scope=Locality.Discharge in
    if ntns <> [] then
      CWarnings.with_warn ("-"^Notation.warning_overridden_name)
        (List.iter (Metasyntax.add_notation_interpretation ~local (Global.env()))) ntns
  in
  refs

let declare_possibly_mutual_parameters ~info ~cinfo ?(mono_uctx_extra=UState.empty) ~sec_vars typs =
  (* Note, if an initial uctx, minimize and restrict have not been done *)
  (* if the uctx of an abandonned proof, minimize is redundant (see close_proof) *)
  let { Info.scope; poly; hook; udecl } = info in
  pi3 (List.fold_left2 (
    fun (i, subst, csts) { CInfo.name; impargs } (typ, uctx) ->
      let uctx' = UState.restrict uctx (Vars.universes_of_constr typ) in
      let univs = UState.check_univ_decl ~poly uctx' udecl in
      let univs = if i = 0 then add_mono_uctx mono_uctx_extra univs else univs in
      let typ = Vars.replace_vars subst typ in
      let pe = {
          parameter_entry_secctx = sec_vars;
          parameter_entry_type = Evarutil.nf_evars_universes (Evd.from_ctx uctx) typ;
          parameter_entry_universes = univs;
          parameter_entry_inline_code = None;
        } in
      let cst = declare_parameter ~name ~scope ~hook ~impargs ~uctx pe in
      let inst = instance_of_univs univs in
      (i+1, (name, Constr.mkConstU (cst,inst))::subst, (cst, univs)::csts)
  ) (0, [], []) cinfo typs)

let make_recursive_bodies env ~typing_flags ~possible_guard ~rec_declaration =
  let env = Environ.update_typing_flags ?typing_flags env in
  let indexes = Pretyping.search_guard env possible_guard rec_declaration in
  let mkbody i = match indexes with
  | Some indexes -> Constr.mkFix ((indexes,i), rec_declaration)
  | None -> Constr.mkCoFix (i, rec_declaration) in
  List.map_i (fun i typ -> (mkbody i, typ)) 0 (Array.to_list (pi2 rec_declaration)), indexes

let prepare_recursive_declaration cinfo fixtypes fixrs fixdefs =
  let fixnames = List.map (fun CInfo.{name} -> name) cinfo in
  let names = List.map2 (fun name r -> Context.make_annot (Name name) r) fixnames fixrs in
  let defs = List.map (Vars.subst_vars (List.rev fixnames)) fixdefs in
  (Array.of_list names, Array.of_list fixtypes, Array.of_list defs)

let prepare_recursive_edeclaration sigma cinfo fixtypes fixrs fixdefs =
  let fixnames = List.map (fun CInfo.{name} -> name) cinfo in
  let names = List.map2 (fun name r -> Context.make_annot (Name name) (EConstr.ERelevance.make r)) fixnames fixrs in
  let defs = List.map (EConstr.Vars.subst_vars sigma (List.rev fixnames)) fixdefs in
  (Array.of_list names, Array.of_list fixtypes, Array.of_list defs)

let declare_mutual_definitions ~info ~cinfo ~opaque ~uctx ~bodies ~possible_guard ?using () =
  (* Note: uctx is supposed to be already minimized *)
  let { Info.typing_flags; _ } = info in
  let env = Global.env() in
  let possible_guard, fixrelevances = possible_guard in
  let fixtypes = List.map (fun CInfo.{typ} -> typ) cinfo in
  let rec_declaration = prepare_recursive_declaration cinfo fixtypes fixrelevances bodies in
  let bodies_types, indexes = make_recursive_bodies env ~typing_flags ~rec_declaration ~possible_guard in
  let entries = List.map (fun (body, typ) -> ((body, Evd.empty_side_effects), Some typ)) bodies_types in
  let entries_for_using = List.map (fun (body, typ) -> (body, Some typ)) bodies_types in
  let using = interp_mutual_using env cinfo entries_for_using using in
  let obj = DefaultProof { proof = (entries, uctx); opaque; using; keep_body_ucst_separate = None } in
  let refs = declare_possibly_mutual_definitions ~info ~cinfo ~obls:[] obj in
  let fixnames = List.map (fun { CInfo.name } -> name) cinfo in
  recursive_message indexes fixnames;
  refs

(* Preparing proof entries *)
let error_unresolved_evars env sigma t evars =
  let pr_unresolved_evar e =
    hov 2 (str"- " ++ Printer.pr_existential_key env sigma e ++  str ": " ++
      Himsg.explain_pretype_error env sigma
        (Pretype_errors.UnsolvableImplicit (e,None)))
  in
  CErrors.user_err (hov 0 begin
    str "The following term contains unresolved implicit arguments:"++ fnl () ++
    str "  " ++ Printer.pr_econstr_env env sigma t ++ fnl () ++
    str "More precisely: " ++ fnl () ++
    v 0 (prlist_with_sep cut pr_unresolved_evar (Evar.Set.elements evars))
  end)

let check_evars_are_solved env sigma t =
  let evars = Evarutil.undefined_evars_of_term sigma t in
  if not (Evar.Set.is_empty evars) then error_unresolved_evars env sigma t evars

let declare_definition ~info ~cinfo ~opaque ~obls ~body ?using sigma =
  let { CInfo.name; typ; _ } = cinfo in
  let env = Global.env () in
  Option.iter (check_evars_are_solved env sigma) typ;
  check_evars_are_solved env sigma body;
  let sigma = Evd.minimize_universes sigma in
  let body = EConstr.to_constr sigma body in
  let typ = Option.map (EConstr.to_constr sigma) typ in
  let uctx = Evd.ustate sigma in
  let using = interp_mutual_using env [cinfo] [body,typ] using in
  let obj = DefaultProof { proof = ([((body,Evd.empty_side_effects),typ)], uctx); opaque; using; keep_body_ucst_separate = None } in
  let gref = List.hd (declare_possibly_mutual_definitions ~info ~cinfo:[cinfo] ~obls obj) in
  gref, uctx

let prepare_obligations ~name ?types ~body env sigma =
  let env = Global.env () in
  let types = match types with
    | Some t -> t
    | None -> Retyping.get_type_of env sigma body
  in
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:false
      sigma (fun nf -> nf body, nf types)
  in
  RetrieveObl.check_evars env sigma;
  let body, types = EConstr.(of_constr body, of_constr types) in
  let obls, (_, evmap), body, cty = RetrieveObl.retrieve_obligations env name sigma 0 body types in
  let uctx = Evd.ustate sigma in
  body, cty, uctx, evmap, obls

let prepare_parameter ~poly ~udecl ~types sigma =
  let env = Global.env () in
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;
  let sigma, typ = Evarutil.finalize ~abort_on_undefined_evars:true
      sigma (fun nf -> nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let pe = {
      parameter_entry_secctx = None;
      parameter_entry_type = typ;
      parameter_entry_universes = univs;
      parameter_entry_inline_code = None;
    } in
  sigma, pe

type progress = Remain of int | Dependent | Defined of GlobRef.t

module Obls_ = struct

open Constr

type 'a obligation_body = DefinedObl of 'a | TermObl of constr

module Obligation = struct
  type t =
    { obl_name : Id.t
    ; obl_type : types
    ; obl_location : Evar_kinds.t Loc.located
    ; obl_body : pconstant obligation_body option
    ; obl_status : bool * Evar_kinds.obligation_definition_status
    ; obl_deps : Int.Set.t
    ; obl_tac : unit Proofview.tactic option }

  let set_type ~typ obl = {obl with obl_type = typ}
end

type obligations = {obls : Obligation.t array; remaining : int}
type fixpoint_kind = IsFixpoint of lident option list | IsCoFixpoint

module ProgramDecl = struct

  type 'a t =
    { prg_cinfo : constr CInfo.t
    ; prg_info : Info.t
    ; prg_using : Vernacexpr.section_subset_expr option
    ; prg_opaque : bool
    ; prg_hook : 'a option
    ; prg_body : constr
    ; prg_uctx : UState.t
    ; prg_obligations : obligations
    ; prg_deps : Id.t list
    ; prg_possible_guard : (Pretyping.possible_guard * Sorts.relevance list) option (* None = not recursive *)
    ; prg_reduce : constr -> constr
    }

  open Obligation

  let make ~info ~cinfo ~opaque ~reduce ~deps ~uctx ~body ~possible_guard ?obl_hook ?using obls =
    let obls', body =
      match body with
      | None ->
        assert (Int.equal (Array.length obls) 0);
        let n = Nameops.add_suffix cinfo.CInfo.name "_obligation" in
        ( [| { obl_name = n
             ; obl_body = None
             ; obl_location = Loc.tag Evar_kinds.InternalHole
             ; obl_type = cinfo.CInfo.typ
             ; obl_status = (false, Evar_kinds.Expand)
             ; obl_deps = Int.Set.empty
             ; obl_tac = None } |]
        , mkVar n )
      | Some b ->
        ( Array.mapi
            (fun i (n, t, l, o, d, tac) ->
              { obl_name = n
              ; obl_body = None
              ; obl_location = l
              ; obl_type = t
              ; obl_status = o
              ; obl_deps = d
              ; obl_tac = tac })
            obls
        , b )
    in
    let prg_uctx = UState.make_flexible_nonalgebraic uctx in
    { prg_cinfo = { cinfo with CInfo.typ = reduce cinfo.CInfo.typ }
    ; prg_info = info
    ; prg_using = using
    ; prg_hook = obl_hook
    ; prg_opaque = opaque
    ; prg_body = body
    ; prg_uctx
    ; prg_obligations = {obls = obls'; remaining = Array.length obls'}
    ; prg_deps = deps
    ; prg_possible_guard = possible_guard
    ; prg_reduce = reduce }

  let show prg =
    let { CInfo.name; typ; _ } = prg.prg_cinfo in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    Id.print name ++ spc () ++ str ":" ++ spc ()
    ++ Printer.pr_constr_env env sigma typ
    ++ spc () ++ str ":=" ++ fnl ()
    ++ Printer.pr_constr_env env sigma prg.prg_body

  module Internal = struct
    let get_name prg = prg.prg_cinfo.CInfo.name
    let get_uctx prg = prg.prg_uctx
    let set_uctx ~uctx prg = {prg with prg_uctx = uctx}
    let get_poly prg = prg.prg_info.Info.poly
    let get_obligations prg = prg.prg_obligations
    let get_using prg = prg.prg_using
  end
end

open Obligation
open ProgramDecl

(* Saving an obligation *)

(* XXX: Is this the right place for this? *)
let it_mkLambda_or_LetIn_or_clean t ctx =
  let open Context.Rel.Declaration in
  let fold t decl =
    if is_local_assum decl then Term.mkLambda_or_LetIn decl t
    else if Vars.noccurn 1 t then Vars.subst1 mkProp t
    else Term.mkLambda_or_LetIn decl t
  in
  Context.Rel.fold_inside fold ctx ~init:t

(* XXX: Is this the right place for this? *)
let decompose_lam_prod c ty =
  let open Context.Rel.Declaration in
  let rec aux ctx c ty =
    match (Constr.kind c, Constr.kind ty) with
    | LetIn (x, b, t, c), LetIn (x', b', t', ty)
      when Constr.equal b b' && Constr.equal t t' ->
      let ctx' = Context.Rel.add (LocalDef (x, b', t')) ctx in
      aux ctx' c ty
    | _, LetIn (x', b', t', ty) ->
      let ctx' = Context.Rel.add (LocalDef (x', b', t')) ctx in
      aux ctx' (lift 1 c) ty
    | LetIn (x, b, t, c), _ ->
      let ctx' = Context.Rel.add (LocalDef (x, b, t)) ctx in
      aux ctx' c (lift 1 ty)
    | Lambda (x, b, t), Prod (x', b', t')
    (* By invariant, must be convertible *) ->
      let ctx' = Context.Rel.add (LocalAssum (x, b')) ctx in
      aux ctx' t t'
    | Cast (c, _, _), _ -> aux ctx c ty
    | _, _ -> (ctx, c, ty)
  in
  aux Context.Rel.empty c ty

(* XXX: What's the relation of this with Abstract.shrink ? *)
let shrink_body c ty =
  let ctx, b, ty =
    match ty with
    | None ->
      let ctx, b = Term.decompose_lambda_decls c in
      (ctx, b, None)
    | Some ty ->
      let ctx, b, ty = decompose_lam_prod c ty in
      (ctx, b, Some ty)
  in
  let b', ty', n, args =
    List.fold_left
      (fun (b, ty, i, args) decl ->
        if Vars.noccurn 1 b && Option.cata (Vars.noccurn 1) true ty then
          (Vars.subst1 mkProp b, Option.map (Vars.subst1 mkProp) ty, succ i, args)
        else
          let open Context.Rel.Declaration in
          let args = if is_local_assum decl then mkRel i :: args else args in
          ( Term.mkLambda_or_LetIn decl b
          , Option.map (Term.mkProd_or_LetIn decl) ty
          , succ i
          , args ))
      (b, ty, 1, []) ctx
  in
  (ctx, b', ty', Array.of_list args)

(***********************************************************************)
(* Saving an obligation                                                *)
(***********************************************************************)

let universes_of_decl body typ =
  let univs_typ = match typ with None -> Univ.Level.Set.empty | Some ty -> Vars.universes_of_constr ty in
  let univs_body = Vars.universes_of_constr body in
  Univ.Level.Set.union univs_body univs_typ

let current_obligation_uctx prg uctx vars =
  let uctx = UState.restrict uctx vars in
  if prg.prg_info.Info.poly then
    uctx
  else
    (* We let the first obligation declare the monomorphic universe
      context of the main constant (goes together with
      update_global_obligation_uctx) *)
    UState.union prg.prg_uctx uctx

let update_global_obligation_uctx prg uctx =
  let uctx =
    if prg.prg_info.Info.poly then
      (* Accumulate the polymorphic constraints *)
      UState.union prg.prg_uctx uctx
    else
      (* The monomorphic universe context of the main constant has
         been declared by the first obligation; it is now in the
         global env and we now remove it for the further
         declarations *)
      UState.Internal.reboot (Global.env ()) uctx in
  ProgramDecl.Internal.set_uctx ~uctx prg

let declare_obligation prg obl ~uctx ~types ~body =
  let body = prg.prg_reduce body in
  let types = Option.map prg.prg_reduce types in
  match obl.obl_status with
  | _, Evar_kinds.Expand ->
    let prg_uctx = UState.union prg.prg_uctx uctx in
    let prg = ProgramDecl.Internal.set_uctx ~uctx:prg_uctx prg in
    (prg, {obl with obl_body = Some (TermObl body)}, [])
  | force, Evar_kinds.Define opaque ->
    let opaque = (not force) && opaque in
    let poly = prg.prg_info.Info.poly in
    let ctx, body, ty, args =
      if not poly then shrink_body body types
      else ([], body, types, [||])
    in
    let uctx' = current_obligation_uctx prg uctx (universes_of_decl body types) in
    let univs = UState.univ_entry ~poly uctx' in
    let inst = instance_of_univs univs in
    let ce = definition_entry ?types:ty ~opaque ~univs body in
    (* ppedrot: seems legit to have obligations as local *)
    let constant =
      declare_constant ~loc:None ~name:obl.obl_name
        ~typing_flags:prg.prg_info.Info.typing_flags
        ~local:Locality.ImportNeedQualified
        ~kind:Decls.(IsProof Property)
        (DefinitionEntry ce)
    in
    definition_message obl.obl_name;
    let prg = update_global_obligation_uctx prg uctx in
    let body =
      if poly then DefinedObl (constant, inst)
      else
        let const = mkConstU (constant, inst) in
        TermObl (it_mkLambda_or_LetIn_or_clean (mkApp (const, args)) ctx)
    in
    (prg, {obl with obl_body = Some body}, [GlobRef.ConstRef constant])

(* Updating the obligation meta-info on close *)

let not_transp_msg =
  Pp.(
    str "Obligation should be transparent but was declared opaque."
    ++ spc ()
    ++ str "Use 'Defined' instead.")

let err_not_transp () =
  CErrors.user_err not_transp_msg

module ProgMap = Id.Map

module State = struct

  type t = prg_hook ProgramDecl.t CEphemeron.key ProgMap.t
  and prg_hook = PrgHook of t Hook.g

  let call_prg_hook { prg_hook=hook } x pm =
    let hook = Option.map (fun (PrgHook h) -> h) hook in
    Hook.call_g ?hook x pm


  let empty = ProgMap.empty

  let pending pm =
    ProgMap.filter
      (fun _ v -> (CEphemeron.get v).prg_obligations.remaining > 0)
      pm

  let num_pending pm = pending pm |> ProgMap.cardinal

  let first_pending pm =
    pending pm |> ProgMap.choose_opt
    |> Option.map (fun (_, v) -> CEphemeron.get v)

  let get_unique_open_prog pm name : (_, Id.t list) result =
    match name with
    | Some n ->
      Option.cata
        (fun p -> Ok (CEphemeron.get p))
        (Error []) (ProgMap.find_opt n pm)
    | None -> (
      let n = num_pending pm in
      match n with
      | 0 -> Error []
      | 1 -> Option.cata (fun p -> Ok p) (Error []) (first_pending pm)
      | _ ->
        let progs = Id.Set.elements (ProgMap.domain pm) in
        Error progs )

  let add t key prg = ProgMap.add key (CEphemeron.create prg) t

  let fold t ~f ~init =
    let f k v acc = f k (CEphemeron.get v) acc in
    ProgMap.fold f t init

  let all pm = ProgMap.bindings pm |> List.map (fun (_,v) -> CEphemeron.get v)
  let find m t = ProgMap.find_opt t m |> Option.map CEphemeron.get

  module View = struct
    module Obl = struct
      type t =
        { name : Id.t
        ; loc : Loc.t option
        ; status : bool * Evar_kinds.obligation_definition_status
        ; solved : bool
        }

      let make (o : Obligation.t) =
        let { obl_name; obl_location; obl_status; obl_body; _ } = o in
        { name = obl_name
        ; loc = fst obl_location
        ; status = obl_status
        ; solved = Option.has_some obl_body
        }
    end

    type t =
      { opaque : bool
      ; remaining : int
      ; obligations : Obl.t array
      }

    let make { prg_opaque; prg_obligations; _ } =
      { opaque = prg_opaque
      ; remaining = prg_obligations.remaining
      ; obligations = Array.map Obl.make prg_obligations.obls
      }

    let make eph = CEphemeron.get eph |> make
  end

  let view s = Id.Map.map View.make s

end

(* In all cases, the use of the map is read-only so we don't expose the ref *)
let map_non_empty_keys is_empty m =
  ProgMap.fold (fun k prg l -> if is_empty prg then l else k :: l) m []

let check_solved_obligations is_empty ~pm ~what_for : unit =
  if not (ProgMap.is_empty pm) then
    let keys = map_non_empty_keys is_empty pm in
    let have_string = if Int.equal (List.length keys) 1 then " has " else " have " in
    CErrors.user_err
      Pp.(
        str "Unsolved obligations when closing "
        ++ what_for ++ str ":" ++ spc ()
        ++ prlist_with_sep spc (fun x -> Id.print x) keys
        ++ str have_string
        ++ str "unsolved obligations." )

let map_replace k v m = ProgMap.add k (CEphemeron.create v) (ProgMap.remove k m)
let progmap_remove pm prg = ProgMap.remove prg.prg_cinfo.CInfo.name pm
let progmap_replace prg' pm = map_replace prg'.prg_cinfo.CInfo.name prg' pm
let obligations_solved prg = Int.equal prg.prg_obligations.remaining 0

let obligations_message rem =
  Format.asprintf "%s %s remaining"
    (if rem > 0 then string_of_int rem else "No more")
    (CString.plural rem "obligation")
  |> Pp.str |> Flags.if_verbose Feedback.msg_info

let get_obligation_body expand obl =
  match obl.obl_body with
  | None -> None
  | Some c -> (
    if expand && snd obl.obl_status == Evar_kinds.Expand then
      match c with
      | DefinedObl pc -> Some (Environ.constant_value_in (Global.env ()) pc)
      | TermObl c -> Some c
    else
      match c with DefinedObl pc -> Some (mkConstU pc) | TermObl c -> Some c )

let obl_substitution expand obls deps =
  Int.Set.fold
    (fun x acc ->
      let xobl = obls.(x) in
      match get_obligation_body expand xobl with
      | None -> acc
      | Some oblb -> (xobl.obl_name, (xobl.obl_type, oblb)) :: acc)
    deps []

let rec intset_to = function
  | -1 -> Int.Set.empty
  | n -> Int.Set.add n (intset_to (pred n))

let obligation_substitution expand prg =
  let obls = prg.prg_obligations.obls in
  let ints = intset_to (pred (Array.length obls)) in
  obl_substitution expand obls ints

let subst_prog subst prg =
  let subst' = List.map (fun (n, (_, b)) -> (n, b)) subst in
  ( Vars.replace_vars subst' prg.prg_body
  , Vars.replace_vars subst' (* Termops.refresh_universes *) prg.prg_cinfo.CInfo.typ )

let declare_definition ~pm prg =
  let varsubst = obligation_substitution true prg in
  let sigma = Evd.from_ctx prg.prg_uctx in
  let body, types = subst_prog varsubst prg in
  let body, types = EConstr.(of_constr body, of_constr types) in
  let cinfo = { prg.prg_cinfo with CInfo.typ = Some types } in
  let name, info, opaque, using = prg.prg_cinfo.CInfo.name, prg.prg_info, prg.prg_opaque, prg.prg_using in
  let obls = List.map (fun (id, (_, c)) -> (id, c)) varsubst in
  (* XXX: This is doing normalization twice *)
  let kn, uctx = declare_definition ~cinfo ~info ~obls ~body ~opaque ?using sigma in
  (* XXX: We call the obligation hook here, by consistency with the
     previous imperative behaviour, however I'm not sure this is right *)
  let pm = State.call_prg_hook prg
      { Hook.S.uctx; obls; scope = prg.prg_info.Info.scope; dref = kn} pm in
  let pm = progmap_remove pm prg in
  pm, kn

let declare_mutual_definitions ~pm l =
  let first = List.hd l in
  let defobl x =
    let oblsubst = obligation_substitution true x in
    let subs, typ = subst_prog oblsubst x in
    let sigma = Evd.from_ctx x.prg_uctx in
    let term = EConstr.of_constr subs in
    let typ = EConstr.of_constr typ in
    let term = EConstr.to_constr sigma term in
    let typ = EConstr.to_constr sigma typ in
    let def = (x.prg_reduce term, x.prg_reduce typ, x.prg_cinfo.CInfo.impargs) in
    let oblsubst = List.map (fun (id, (_, c)) -> (id, c)) oblsubst in
    (def, oblsubst)
  in
  let defs, obls = List.split (List.map defobl l) in
  let obls = List.flatten obls in
  let fixitems = List.map2 (fun (d, typ, impargs) name -> CInfo.make ~name ~typ ~impargs ()) defs first.prg_deps in
  let fixdefs, fixtypes, _ = List.split3 defs in
  let possible_guard = Option.get first.prg_possible_guard in
  (* Declare the recursive definitions *)
  let kns =
    declare_mutual_definitions ~info:first.prg_info
      ~uctx:first.prg_uctx ~bodies:fixdefs ~possible_guard ~opaque:first.prg_opaque
      ~cinfo:fixitems ?using:first.prg_using ()
  in
  (* Only for the first constant *)
  let dref = List.hd kns in
  let scope = first.prg_info.Info.scope in
  let s_hook = {Hook.S.uctx = first.prg_uctx; obls; scope; dref} in
  Hook.call ?hook:first.prg_info.Info.hook s_hook;
  (* XXX: We call the obligation hook here, by consistency with the
     previous imperative behaviour, however I'm not sure this is right *)
  let pm = State.call_prg_hook first s_hook pm in
  let pm = List.fold_left progmap_remove pm l in
  pm, dref

let update_obls ~pm prg obls rem =
  let prg_obligations = {obls; remaining = rem} in
  let prg' = {prg with prg_obligations} in
  let pm = progmap_replace prg' pm in
  obligations_message rem;
  if rem > 0 then pm, Remain rem
  else
    match prg'.prg_deps with
    | [] ->
      let pm, kn = declare_definition ~pm prg' in
      pm, Defined kn
    | l ->
      let progs =
        List.map (fun x -> CEphemeron.get (ProgMap.find x pm)) prg'.prg_deps
      in
      if List.for_all (fun x -> obligations_solved x) progs then
        let pm, kn = declare_mutual_definitions ~pm progs in
        pm, Defined kn
      else pm, Dependent

let dependencies obls n =
  let res = ref Int.Set.empty in
  Array.iteri
    (fun i obl ->
      if (not (Int.equal i n)) && Int.Set.mem n obl.obl_deps then
        res := Int.Set.add i !res)
    obls;
  !res

let update_program_decl_on_defined ~pm prg obls num obl rem ~auto =
  let obls = Array.copy obls in
  let () = obls.(num) <- obl in
  let pm, _progress = update_obls ~pm prg obls (pred rem) in
  let pm =
    if pred rem > 0 then
      let deps = dependencies obls num in
      if not (Int.Set.is_empty deps) then
        let pm, _progress = auto ~pm (Some prg.prg_cinfo.CInfo.name) deps None in
        pm
      else pm
    else pm
  in
  pm

type obligation_resolver =
     pm:State.t
  -> Id.t option
  -> Int.Set.t
  -> unit Proofview.tactic option
  -> State.t * progress

type obl_check_final = AllFinal | SpecificFinal of Id.t

type obligation_qed_info = {
  name : Id.t;
  num : int;
  auto : obligation_resolver;
  check_final : obl_check_final option;
}

let not_final_obligation n =
  let msg = match n with
    | AllFinal -> str "This obligation is not final."
    | SpecificFinal n -> str "This obligation is not final for program " ++ Id.print n ++ str "."
  in
  CErrors.user_err msg

let do_check_final ~pm = function
  | None -> ()
  | Some check_final ->
    let final = match check_final with
      | AllFinal -> begin match State.first_pending pm with
          | Some _ -> false
          | None -> true
        end
      | SpecificFinal n -> begin match State.get_unique_open_prog pm (Some n) with
          | Error _ -> true
          | Ok _ -> false
        end
    in
    if not final then not_final_obligation check_final

let obligation_terminator ~pm ~entry ~uctx ~oinfo:{name; num; auto; check_final} =
  let env = Global.env () in
  let ty = entry.proof_entry_type in
  let body, uctx = inline_private_constants ~uctx env (ProofEntry.get_entry_body entry) in
  let sigma = Evd.from_ctx uctx in
  Inductiveops.control_only_guard (Global.env ()) sigma
    (EConstr.of_constr body);
  (* Declare the obligation ourselves and drop the hook *)
  let prg = Option.get (State.find pm name) in
  let {obls; remaining = rem} = prg.prg_obligations in
  let obl = obls.(num) in
  let status =
    match (obl.obl_status, ProofEntry.get_opacity entry) with
    | (_, Evar_kinds.Expand), true -> err_not_transp ()
    | (true, _), true -> err_not_transp ()
    | (false, _), true -> Evar_kinds.Define true
    | (_, Evar_kinds.Define true), false -> Evar_kinds.Define false
    | (_, status), false -> status
  in
  let obl = {obl with obl_status = (false, status)} in
  let prg, obl, cst = declare_obligation prg obl ~body ~types:ty ~uctx in
  let pm = update_program_decl_on_defined ~pm prg obls num obl rem ~auto in
  let () = do_check_final ~pm check_final in
  pm, cst

(* Similar to the terminator but for the admitted path; this assumes
   the admitted constant was already declared.

   FIXME: There is duplication of this code with obligation_terminator
   and Obligations.admit_obligations *)
let obligation_admitted_terminator ~pm typ {name; num; auto; check_final} declare_fun sec_vars uctx =
  let prg = Option.get (State.find pm name) in
  let {obls; remaining = rem} = prg.prg_obligations in
  let obl = obls.(num) in
  let () =
    match obl.obl_status with
    | true, Evar_kinds.Expand | true, Evar_kinds.Define true -> err_not_transp ()
    | _ -> ()
  in
  let mono_uctx_extra = if prg.prg_info.Info.poly then UState.empty else prg.prg_uctx in
  let cst, univs = declare_fun ~uctx ~mono_uctx_extra typ in
  let inst = instance_of_univs univs in
  let obl = {obl with obl_body = Some (DefinedObl (cst, inst))} in
  let prg = update_global_obligation_uctx prg uctx in
  let pm = update_program_decl_on_defined ~pm prg obls num obl rem ~auto in
  let () = do_check_final ~pm check_final in
  pm

end

(************************************************************************)
(* Handling of interactive proofs                                       *)
(************************************************************************)

module Proof_ending = struct

  type t =
    | Regular
    | End_obligation of Obls_.obligation_qed_info
    | End_equations of
        { hook : pm:Obls_.State.t -> Constant.t list -> Evd.evar_map -> Obls_.State.t
        ; i : Id.t
        ; types : (Environ.env * Evar.t * Evd.undefined Evd.evar_info * EConstr.named_context * Evd.econstr) list
        ; sigma : Evd.evar_map
        }

end

module Proof_info = struct

  type t =
    { cinfo : unit CInfo.t list
    (** cinfo contains each individual constant info in a mutual decl *)
    ; info : Info.t
    ; proof_ending : Proof_ending.t CEphemeron.key
    (* This could be improved and the CEphemeron removed *)
    ; possible_guard : (Pretyping.possible_guard * Sorts.relevance list) option (* None = not recursive *)
    (** thms and compute guard are specific only to
       start_definition + regular terminator, so we
       could make this per-proof kind *)
    }

  let make ~cinfo ~info ?possible_guard ?(proof_ending=Proof_ending.Regular) () =
    { cinfo
    ; info
    ; possible_guard
    ; proof_ending = CEphemeron.create proof_ending
    }

end

module Proof_object = struct

  type t =
    { proof_object : proof_object
    ; pinfo : Proof_info.t
    }

end

(* Alias *)
module Proof_ = Proof
module Proof = struct

type nonrec closed_proof_output = closed_proof_output
type proof_object = Proof_object.t

type t =
  { endline_tactic : Genarg.glob_generic_argument option
  ; using : Id.Set.t option
  ; proof : Proof.t
  ; initial_euctx : UState.t
  (** The initial universe context (for the statement) *)
  ; pinfo : Proof_info.t
  }

(*** Proof Global manipulation ***)

let get ps = ps.proof
let get_name ps = (Proof.data ps.proof).Proof.name

let fold ~f p = f p.proof
let map ~f p = { p with proof = f p.proof }
let map_fold ~f p = let proof, res = f p.proof in { p with proof }, res

let map_fold_endline ~f ps =
  let et =
    match ps.endline_tactic with
    | None -> Proofview.tclUNIT ()
    | Some tac ->
      let open Geninterp in
      let {Proof.poly} = Proof.data ps.proof in
      let ist = { lfun = Id.Map.empty; poly; extra = TacStore.empty } in
      let tac = Geninterp.generic_interp ist tac in
      Ftactic.run tac (fun _ -> Proofview.tclUNIT ())
  in
  let (newpr,ret) = f et ps.proof in
  let ps = { ps with proof = newpr } in
  ps, ret

let compact pf = map ~f:Proof.compact pf

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac ps =
  { ps with endline_tactic = Some tac }

let initialize_named_context_for_proof () =
  let sign = Global.named_context () in
  List.fold_right
    (fun d signv ->
      let id = NamedDecl.get_id d in
      let d = if Decls.variable_opacity id then NamedDecl.drop_body d else d in
      Environ.push_named_context_val d signv) sign Environ.empty_named_context_val

let start_proof_core ~name ~pinfo ?using sigma goals =
  (* In ?sign, we remove the bodies of variables in the named context
     marked "opaque", this is a hack tho, see #10446, and
     build_constant_by_tactic uses a different method that would break
     program_inference_hook *)
  let { Proof_info.info = { Info.poly; typing_flags; _ }; _ } = pinfo in
  let goals = List.map (fun (sign, typ) ->
      let sign = match sign with None -> initialize_named_context_for_proof () | Some sign -> sign in
      (Global.env_of_context sign, typ)) goals in
  let proof = Proof.start ~name ~poly ?typing_flags sigma goals in
  let initial_euctx = Evd.ustate Proof.((data proof).sigma) in
  { proof
  ; endline_tactic = None
  ; using
  ; initial_euctx
  ; pinfo
  }

(** [start_proof ~info ~cinfo sigma] starts a proof of [cinfo].
   The proof is started in the evar map [sigma] (which
   can typically contain universe constraints) *)
let start_core ~info ~cinfo ?proof_ending ?using sigma =
  let { CInfo.name; typ; _ } = cinfo in
  check_exists name;
  let cinfo = [{ cinfo with CInfo.typ = () }] in
  let pinfo = Proof_info.make ~cinfo ~info ?proof_ending () in
  start_proof_core ~name ~pinfo ?using sigma [None,typ]

let start = start_core ?proof_ending:None

let start_dependent ~info ~cinfo ~name ~proof_ending goals =
  let { Info.poly; typing_flags; _ } = info in
  let proof = Proof.dependent_start ~name ~poly ?typing_flags goals in
  let initial_euctx = Evd.ustate Proof.((data proof).sigma) in
  let pinfo = Proof_info.make ~info ~cinfo ~proof_ending () in
  { proof
  ; endline_tactic = None
  ; using = None
  ; initial_euctx
  ; pinfo
  }

let start_derive ~name ~info ~cinfo goals =
  let proof_ending = Proof_ending.Regular in
  start_dependent ~info ~cinfo ~name ~proof_ending goals

let start_equations ~name ~info ~hook ~types sigma goals =
  let proof_ending = Proof_ending.End_equations {hook; i=name; types; sigma} in
  start_dependent ~name ~cinfo:[] ~info ~proof_ending goals

let start_definition ~info ~cinfo ?using sigma =
  let { CInfo.name; typ; args } = cinfo in
  let init_tac = Tactics.auto_intros_tac args in
  let pinfo = Proof_info.make ~cinfo:[{cinfo with typ = ()}] ~info () in
  let env = Global.env () in
  let using = Option.map (interp_proof_using_cinfo env sigma [cinfo]) using in
  let lemma = start_proof_core ~name ~pinfo ?using sigma [None, EConstr.of_constr typ] in
  map lemma ~f:(fun p ->
      pi1 @@ Proof.run_tactic Global.(env ()) init_tac p)

let start_mutual_definitions ~info ~cinfo ~bodies ~possible_guard ?using sigma =
  let intro_tac { CInfo.args; _ } = Tactics.auto_intros_tac args in
  let fixrs = snd possible_guard in
  let init_tac =
    (* This is the case for hybrid proof mode / definition
       fixpoint, where terms for some constants are given with := *)
    let tacl = List.map (Option.cata (EConstr.of_constr %> Tactics.exact_no_check) Tacticals.tclIDTAC) bodies in
    List.map2 (fun tac thm -> Tacticals.tclTHEN tac (intro_tac thm)) tacl cinfo
  in
  match cinfo with
  | [] -> CErrors.anomaly (Pp.str "No proof to start.")
  | { CInfo.name; _} :: _ as thms ->
    let pinfo = Proof_info.make ~cinfo:(List.map (fun cinfo -> {cinfo with CInfo.typ = ()}) cinfo) ~info ~possible_guard () in
    (* start_lemma has the responsibility to add (name, impargs, typ)
       to thms, once Info.t is more refined this won't be necessary *)
    let env = Global.env () in
    let sign =
      List.fold_left2 (fun sign CInfo.{name;typ} r ->
          let typ = EConstr.of_constr typ in
          let r = EConstr.ERelevance.make r in
          let decl = Context.Named.Declaration.LocalAssum (Context.make_annot name r, typ) in
          EConstr.push_named_context_val decl sign) (initialize_named_context_for_proof ()) cinfo fixrs in
    let using = Option.map (interp_proof_using_cinfo env sigma cinfo) using in
    let goals = List.map (function CInfo.{typ} -> (Some sign, EConstr.of_constr typ)) thms in
    let lemma = start_proof_core ~name ~pinfo ?using sigma goals in
    let lemma = map lemma ~f:(fun p ->
        pi1 @@ Proof.run_tactic Global.(env ()) (Proofview.tclFOCUS 1 (List.length thms) (Proofview.tclDISPATCH init_tac)) p) in
    let () =
      (* Temporary declaration of notations for the time of the proofs *)
      let ntn_env =
        (* We simulate the goal context in which the fixpoint bodies have to be proved (exact relevance does not matter) *)
        let make_decl CInfo.{name; typ} = Context.Named.Declaration.LocalAssum (Context.annotR name, typ) in
        Environ.push_named_context (List.map make_decl cinfo) (Global.env()) in
      List.iter (Metasyntax.add_notation_interpretation ~local:(info.scope=Locality.Discharge) ntn_env) info.ntns in
    lemma

let get_used_variables pf = pf.using

let definition_scope ps = ps.pinfo.info.scope

let set_used_variables ps ~using =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let ctx = Environ.keep_hyps env using in
  let ctx_set =
    List.fold_right Id.Set.add (List.map NamedDecl.get_id ctx) Id.Set.empty in
  let vars_of = Environ.global_vars_set in
  let aux env entry (ctx, all_safe as orig) =
    match entry with
    | LocalAssum ({Context.binder_name=x},_) ->
       if Id.Set.mem x all_safe then orig
       else (ctx, all_safe)
    | LocalDef ({Context.binder_name=x},bo, ty) as decl ->
       if Id.Set.mem x all_safe then orig else
       let vars = Id.Set.union (vars_of env bo) (vars_of env ty) in
       if Id.Set.subset vars all_safe
       then (decl :: ctx, Id.Set.add x all_safe)
       else (ctx, all_safe) in
  let ctx, _ =
    Environ.fold_named_context aux env ~init:(ctx,ctx_set) in
  if not (Option.is_empty ps.using) then
    CErrors.user_err Pp.(str "Used section variables can be declared only once");
  ctx, { ps with using = Some (Context.Named.to_vars ctx) }

(* Interprets the expression in the current proof context, from vernacentries *)
let get_recnames pf =
  if Option.has_some pf.pinfo.Proof_info.possible_guard then
    List.map (fun c -> c.CInfo.name) pf.pinfo.Proof_info.cinfo
  else
    []

let interpret_proof_using pstate using =
  let env = Global.env () in
  let pf = get pstate in
  let sigma, _ = Proof.get_proof_context pf in
  let fixnames = get_recnames pstate in
  let initial_goals pf = Proofview.initial_goals Proof.((data pf).entry) in
  let terms = List.map pi3 (initial_goals (get pstate)) in
  Proof_using.definition_using env sigma ~fixnames ~using ~terms

let set_proof_using pstate using =
  let using = interpret_proof_using pstate using in
  set_used_variables pstate ~using

let get_open_goals ps =
  let Proof.{ goals; stack; sigma } = Proof.data ps.proof in
  List.length goals +
  List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) stack) +
  List.length (Evd.shelf sigma)

let warn_remaining_shelved_goals =
  CWarnings.create ~name:"remaining-shelved-goals" ~category:CWarnings.CoreCategories.tactics
    (fun () -> Pp.str"The proof has remaining shelved goals.")

let warn_given_up =
  CWarnings.create ~name:"remaining-given-up" ~category:CWarnings.CoreCategories.tactics
    (fun () -> Pp.str"The proof has given up (admitted) goals." )

let warn_remaining_unresolved_evars =
  CWarnings.create ~name:"remaining-unresolved-evars" ~category:CWarnings.CoreCategories.tactics
    (fun () -> Pp.str"The proof has unresolved variables.")

type open_proof_kind =
  | OpenGoals
  | NonGroundResult of bool (* true = at least some of the evars in the proof term are given up *)

exception OpenProof of Names.Id.t * open_proof_kind

let () = CErrors.register_handler begin function
  | OpenProof (pid, reason) ->
    let open Pp in
    let ppreason = match reason with
      | OpenGoals -> str "(there are remaining open goals)"
      | NonGroundResult has_given_up ->
        str "(the proof term is not complete" ++
        (if has_given_up then str " because of given up (admitted) goals" else mt()) ++
        str ")"
    in
    let how_to_admit = match reason with
      | OpenGoals | NonGroundResult false -> mt()
      | NonGroundResult true ->
        fnl() ++ str "If this is really what you want to do, use Admitted in place of Qed."
    in
    Some (str " (in proof " ++ Names.Id.print pid ++ str "): " ++
          str "Attempt to save an incomplete proof" ++ spc() ++ ppreason ++ str "." ++
          how_to_admit)
  | _ -> None
  end

let raise_non_ground_proof evd pid c =
  let has_given_up =
    let exception Found in
    let rec aux c =
      let () = match EConstr.kind evd c with
        | Evar (e,_) -> if Evar.Set.mem e (Evd.given_up evd) then raise Found
        | _ -> ()
      in
      EConstr.iter evd aux c
    in
    try aux c; false with Found -> true
  in
  raise (OpenProof (pid, NonGroundResult has_given_up))

let check_incomplete_proof evd =
  if Evd.has_shelved evd then warn_remaining_shelved_goals ()
  else if Evd.has_given_up evd then warn_given_up ()
  else if Evd.has_undefined evd then warn_remaining_unresolved_evars ()

(* XXX: This is still separate from close_proof below due to drop_pt in the STM *)
let prepare_proof ?(warn_incomplete=true) { proof; pinfo } =
  let Proof.{name=pid;entry;poly;sigma=evd} = Proof.data proof in
  let initial_goals = Proofview.initial_goals entry in
  let () = if not @@ Proof.is_done proof then raise (OpenProof (pid, OpenGoals)) in
  let _ : Proof.t =
    (* checks that we closed all brackets ("}") *)
    Proof.unfocus_all proof
  in
  let eff = Evd.eval_side_effects evd in
  let evd = Evd.minimize_universes evd in
  let to_constr c =
    match EConstr.to_constr_opt evd c with
    | Some p -> p
    | None -> raise_non_ground_proof evd pid c
  in
  (* ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
     side-effects... This may explain why one need to uniquize side-effects
     thereafter... *)
  (* EJGA: actually side-effects de-duplication and this codepath is
     unrelated. Duplicated side-effects arise from incorrect scheme
     generation code, the main bulk of it was mostly fixed by #9836
     but duplication can still happen because of rewriting schemes I
     think; however the code below is mostly untested, the only
     code-paths that generate several proof entries are derive and
     equations and so far there is no code in the CI that will
     actually call those and do a side-effect, TTBOMK *)
  (* EJGA: likely the right solution is to attach side effects to the first constant only? *)
  let proofs = List.map (fun (_, body, typ) -> (to_constr body, to_constr typ)) initial_goals in
  let proofs = match pinfo.possible_guard with
    | None -> proofs
    | Some (possible_guard, fixrelevances) ->
      let env = Safe_typing.push_private_constants (Global.env()) eff.Evd.seff_private in
      let fixbodies, fixtypes = List.split proofs in
      let rec_declaration = prepare_recursive_declaration pinfo.cinfo fixtypes fixrelevances fixbodies in
      let typing_flags = pinfo.info.typing_flags in
      fst (make_recursive_bodies env ~typing_flags ~possible_guard ~rec_declaration) in
  let proofs = List.map (fun (body, typ) -> ((body, eff), Some typ)) proofs in
  let () = if warn_incomplete then check_incomplete_proof evd in
  proofs, Evd.ustate evd

exception NotGuarded of
    Environ.env * Evd.evar_map *
    (Environ.env * int * EConstr.t Type_errors.pcofix_guard_error) option *
    (Environ.env * int * int list * EConstr.t Type_errors.pfix_guard_error) list *
    EConstr.rec_declaration

let () = CErrors.register_handler (function
    | NotGuarded (env, sigma, cofix_err, fix_errs, rec_declaration) ->
      Some (Himsg.explain_not_guarded env sigma cofix_err fix_errs rec_declaration)
    | _ -> None)

let control_only_guard { proof; pinfo } =
  let { Proof.entry; Proof.sigma; } = Proof.data proof in
  let initial_goals = Proofview.initial_goals entry in
  let proofs = List.map (fun (_, body, typ) -> Evarutil.(nf_evar sigma body, nf_evar sigma typ)) initial_goals in
  let eff = Evd.eval_side_effects sigma in
  let env = Safe_typing.push_private_constants (Global.env()) eff.Evd.seff_private in
  let open Proof_info in
  match pinfo.possible_guard with
  | None ->
    List.iter (fun (body, _) -> Inductiveops.control_only_guard env sigma body) proofs
  | Some (possible_guard, fixrelevances) ->
    let fixbodies, fixtypes = List.split proofs in
    let rec_declaration = prepare_recursive_edeclaration sigma pinfo.cinfo fixtypes fixrelevances fixbodies in
    try
      let cofix_error =
        if possible_guard.possibly_cofix then
          try
            Inductiveops.control_only_guard env sigma (EConstr.mkCoFix (0,rec_declaration));
            raise Exit
          with Pretype_errors.PretypeError (env, sigma, TypingError (IllFormedRecBody (CoFixGuardError why,lna,i,fixenv,vdefj))) ->
            Some (env,i,why)
        else None
      in
      let combinations = List.combinations possible_guard.possible_fix_indices in
      let fix_errors =
        List.map (fun lv ->
            try
              Inductiveops.control_only_guard env sigma (EConstr.mkFix ((Array.of_list lv,0),rec_declaration));
              raise Exit
            with Pretype_errors.PretypeError (env, sigma, TypingError (IllFormedRecBody (FixGuardError why,lna,i,fixenv,vdefj))) ->
              (env,i,lv,why))
          combinations
      in
      raise (NotGuarded (env, sigma, cofix_error, fix_errors, rec_declaration))
    with Exit -> ()

let return_proof p = (prepare_proof p : closed_proof_output)

let close_proof ?warn_incomplete ~opaque ~keep_body_ucst_separate (proof : t) : Proof_object.t =
  NewProfile.profile "close_proof" (fun () ->
  let opaque = match opaque with
  | Vernacexpr.Opaque -> true
  | Vernacexpr.Transparent -> false in
  let keep_body_ucst_separate = if keep_body_ucst_separate then Some proof.initial_euctx else None in
  { Proof_object.proof_object =
      DefaultProof { proof = prepare_proof ?warn_incomplete proof; opaque; using = proof.using; keep_body_ucst_separate }
  ; pinfo = proof.pinfo
  }) ()

let close_proof_delayed ~feedback_id proof (fpl : closed_proof_output Future.computation) : Proof_object.t =
  NewProfile.profile "close_proof_delayed" (fun () ->
  { Proof_object.proof_object =
      DeferredOpaqueProof { deferred_proof = fpl; using = proof.using; initial_proof_data = Proof.data proof.proof;
                          feedback_id; initial_euctx = proof.initial_euctx }
  ; pinfo = proof.pinfo
  }) ()

let close_future_proof = close_proof_delayed

let update_sigma_univs ugraph p =
  map ~f:(Proof.update_sigma_univs ugraph) p

let next = let n = ref 0 in fun () -> incr n; !n

let by tac = map_fold ~f:(Proof.solve (Goal_select.SelectNth 1) None tac)

let build_constant_by_tactic ~name ?warn_incomplete ~sigma ~sign ~poly (typ : EConstr.t) tac =
  let cinfo = [CInfo.make ~name ~typ:() ()] in
  let info = Info.make ~poly () in
  let pinfo = Proof_info.make ~cinfo ~info () in
  let pf = start_proof_core ~name ~pinfo sigma [Some sign, typ] in
  let pf, status = by tac pf in
  let proof = close_proof ?warn_incomplete ~keep_body_ucst_separate:false ~opaque:Vernacexpr.Transparent pf in
  let entries = process_proof ~info proof.proof_object in
  let { Proof.sigma } = Proof.data pf.proof in
  let sigma = Evd.set_universe_context sigma (ustate_of_proof proof.proof_object) in
  match entries with
  | [ { proof_entry_body = Default { body; opaque = Transparent } } as entry, _] ->
    { entry with proof_entry_body = body }, status, sigma
  | _ ->
    CErrors.anomaly Pp.(str "[build_constant_by_tactic] close_proof returned more than one proof term, or a non transparent one.")

let build_by_tactic env ~uctx ~poly ~typ tac =
  let name = Id.of_string ("temporary_proof"^string_of_int (next())) in
  let sign = Environ.(val_of_named_context (named_context env)) in
  let sigma = Evd.from_ctx uctx in
  let ce, status, sigma = build_constant_by_tactic ~name ~sigma ~sign ~poly typ tac in
  let uctx = Evd.ustate sigma in
  (* ignore side effect universes:
     we don't reset the global env in this code path so the side effects are still present
     cf #13271 and discussion in #18874
     (but due to #13324 we still want to inline them) *)
  let body, effs = ce.proof_entry_body in
  let body, _uctx = inline_private_constants ~uctx env ((body, Univ.ContextSet.empty), effs) in
  body, ce.proof_entry_type, ce.proof_entry_universes, status, uctx

let declare_abstract ~name ~poly ~sign ~secsign ~opaque ~solve_tac sigma concl =
  let kind = if opaque
    then Decls.(IsProof Lemma)
    else Decls.(IsDefinition Definition)
  in
  let (const, safe, sigma') =
    try build_constant_by_tactic ~warn_incomplete:false ~name ~poly ~sigma ~sign:secsign concl solve_tac
    with Logic_monad.TacticFailure e as src ->
    (* if the tactic [tac] fails, it reports a [TacticFailure e],
       which is an error irrelevant to the proof system (in fact it
       means that [e] comes from [tac] failing to yield enough
       success). Hence it reraises [e]. *)
    let (_, info) = Exninfo.capture src in
    Exninfo.iraise (e, info)
  in
  let sigma = Evd.drop_new_defined ~original:sigma sigma' in
  let body, effs = const.proof_entry_body in
  (* EJGA: Hack related to the above call to
     `build_constant_by_tactic` with `~opaque:Transparent`. Even if
     the abstracted term is destined to be opaque, if we trigger the
     `if poly && opaque && private_poly_univs ()` in `close_proof`
     kernel will boom. This deserves more investigation. *)
  let body, typ, args = ProofEntry.shrink_entry sign body const.proof_entry_type in
  let cst () =
    (* do not compute the implicit arguments, it may be costly *)
    let () = Impargs.make_implicit_args false in
    (* No side-effects in the entry, they already exist in the ambient environment *)
    let const = { const with proof_entry_body = body; proof_entry_type = typ } in
    (* ppedrot: seems legit to have abstracted subproofs as local*)
    declare_private_constant ~local:Locality.ImportNeedQualified ~name ~kind ~opaque const
  in
  let cst, eff = Impargs.with_implicit_protection cst () in
  let inst = instance_of_univs const.proof_entry_universes in
  let lem = EConstr.of_constr (Constr.mkConstU (cst, inst)) in
  let effs = Evd.concat_side_effects eff effs in
  effs, sigma, lem, args, safe

let get_goal_context pf i =
  let p = get pf in
  Proof.get_goal_context_gen p i

let get_current_goal_context pf =
  let p = get pf in
  try Proof.get_goal_context_gen p 1
  with
  | Proof.NoSuchGoal _ ->
    (* spiwack: returning empty evar_map, since if there is no goal,
       under focus, there is no accessible evar either. EJGA: this
       seems strange, as we have pf *)
    let env = Global.env () in
    Evd.from_env env, env

let get_current_context pf =
  let p = get pf in
  Proof.get_proof_context p

(************************************************************************)
(* Admitting a lemma-like constant                                      *)
(************************************************************************)

(* Admitted *)
let { Goptions.get = get_keep_admitted_vars } =
  Goptions.declare_bool_option_and_ref
    ~key:["Keep"; "Admitted"; "Variables"]
    ~value:true
    ()

let compute_proof_using_for_admitted pinfo proof typs iproof =
  if not (get_keep_admitted_vars ()) || not (Lib.sections_are_opened()) then None
  else match get_used_variables proof with
    | Some _ as x -> x
    | None ->
        let pproofs = Proof.partial_proof iproof in
        let env = Global.env () in
        let sigma = (Proof.data iproof).Proof.sigma in
        let ids_def = Id.Set.List.union (List.map (Termops.global_vars_set env sigma) pproofs) in
        let ids_typ = Id.Set.List.union (List.map (Termops.global_vars_set env sigma) typs) in
        (* [pproof] is evar-normalized by [partial_proof]. We don't
           count variables appearing only in the type of evars. *)
        let vars = Id.Set.union ids_def ids_typ in
        let vars = match pinfo.Proof_info.possible_guard with
          | Some _ ->
            let recvars = Id.Set.of_list (List.map (fun CInfo.{name} -> name) pinfo.cinfo) in
            Id.Set.diff vars recvars
          | None -> vars
        in
        Some (Environ.really_needed env vars)

let check_type_evars_solved env sigma typ =
  let evars = Evar.Set.elements (Evarutil.undefined_evars_of_term sigma typ) in
  match evars with
  | [] -> ()
  | evk::_ -> CErrors.user_err (str "Cannot admit: the statement has unresolved existential variables.")

let finish_admitted ~pm ~pinfo ~sec_vars typs =
  (* If the constant was an obligation we need to update the program map *)
  let { Proof_info.info; cinfo } = pinfo in
  match CEphemeron.default pinfo.Proof_info.proof_ending Proof_ending.Regular with
  | Proof_ending.End_obligation oinfo ->
    let declare_fun ~uctx ~mono_uctx_extra typ =
      List.hd (declare_possibly_mutual_parameters ~info ~cinfo ~sec_vars ~mono_uctx_extra [typ, uctx]) in
    let typ, uctx = match typs with [typ, uctx] -> typ, uctx | _ -> assert false in
    Obls_.obligation_admitted_terminator ~pm typ oinfo declare_fun sec_vars uctx
  | _ ->
    let (_ : 'a list) = declare_possibly_mutual_parameters ~info ~cinfo ~sec_vars typs in
    pm

let save_admitted ~pm ~proof =
  let iproof = get proof in
  let Proof.{ entry } = Proof.data iproof in
  let typs = List.map pi3 (Proofview.initial_goals entry) in
  let sigma = Evd.from_ctx proof.initial_euctx in
  List.iter (check_type_evars_solved (Global.env()) sigma) typs;
  let sec_vars = compute_proof_using_for_admitted proof.pinfo proof typs iproof in
  let sigma = Evd.minimize_universes sigma in
  let uctx = Evd.ustate sigma in
  let typs = List.map (fun typ -> (EConstr.to_constr sigma typ, uctx)) typs in
  finish_admitted ~pm ~pinfo:proof.pinfo ~sec_vars typs

(************************************************************************)
(* Saving a lemma-like constant                                         *)
(************************************************************************)

let finish_proved_equations ~pm ~kind ~hook i entries types sigma0 =

  let obls = ref 1 in
  let sigma, recobls =
    CList.fold_left2_map (fun sigma (_evar_env, ev, _evi, local_context, _type) entry ->
        let id =
          match Evd.evar_ident ev sigma0 with
          | Some id -> id
          | None -> let n = !obls in incr obls; Nameops.add_suffix i ("_obligation_" ^ string_of_int n)
        in
        let (body, eff), opaque = match entry.proof_entry_body with Default { body; opaque } -> body, opaque | _ -> assert false in
        let body, typ, args = ProofEntry.shrink_entry local_context body entry.proof_entry_type in
        let entry = { entry with proof_entry_body = Default { body = (body, eff); opaque }; proof_entry_type = typ } in
        let cst = declare_constant ~loc:None ~name:id ~kind ~typing_flags:None (DefinitionEntry entry) in
        let sigma, app = Evd.fresh_global (Global.env ()) sigma (GlobRef.ConstRef cst) in
        let sigma = Evd.define ev (EConstr.applist (app, args)) sigma in
        sigma, cst) sigma0
      types entries
  in
  let pm = hook ~pm recobls sigma in
  pm, List.map (fun cst -> GlobRef.ConstRef cst) recobls

let check_single_entry entries label =
  match entries with
  | [entry, uctx] -> entry, uctx
  | _ ->
    CErrors.anomaly ~label Pp.(str "close_proof returned more than one proof term")

let finish_proof ~pm proof_obj proof_info =
  let open Proof_ending in
  let { Proof_info.info; cinfo; possible_guard } = proof_info in
  match CEphemeron.default proof_info.Proof_info.proof_ending Regular with
  | Regular ->
    (* Unless this is a block of mutual fixpoint, we assume the
       statements, if more than one, to form a telescope, as in Derive *)
    let is_telescope = Option.is_empty proof_info.possible_guard in
    pm, declare_possibly_mutual_definitions ~info ~cinfo ~obls:[] ~is_telescope proof_obj
  | End_obligation oinfo ->
    let entries = process_proof ~info proof_obj in
    let entry, uctx = check_single_entry entries "Obligation.save" in
    Obls_.obligation_terminator ~pm ~entry ~uctx ~oinfo
  | End_equations { hook; i; types; sigma } ->
    let kind = info.Info.kind in
    let entries = process_proof ~info proof_obj in
    let entries = List.map fst entries in
    finish_proved_equations ~pm ~kind ~hook i entries types sigma

let err_save_forbidden_in_place_of_qed () =
  CErrors.user_err (Pp.str "Cannot use Save with more than one constant or in this proof mode")

let process_idopt_for_save ~idopt info =
  match idopt with
  | None -> info
  | Some { CAst.v = save_name } ->
    (* Save foo was used; we override the info in the first theorem *)
    let cinfo =
      match info.Proof_info.cinfo, CEphemeron.default info.Proof_info.proof_ending Proof_ending.Regular with
      | [ { CInfo.name; _} as decl ], Proof_ending.Regular ->
        [ { decl with CInfo.name = save_name } ]
      | _ ->
        err_save_forbidden_in_place_of_qed ()
    in { info with Proof_info.cinfo }

let save ~pm ~proof ~opaque ~idopt =
  (* Env and sigma are just used for error printing in save_remaining_recthms *)
  let proof_obj = close_proof ~opaque ~keep_body_ucst_separate:false proof in
  let proof_info = process_idopt_for_save ~idopt proof.pinfo in
  finish_proof ~pm proof_obj.proof_object proof_info

let save_regular ~(proof : t) ~opaque ~idopt =
  let open Proof_ending in
  match CEphemeron.default proof.pinfo.Proof_info.proof_ending Regular with
  | Regular ->
    let (_, grs) : Obls_.State.t * _ = save ~pm:Obls_.State.empty ~proof ~opaque ~idopt in
    grs
  | _ -> CErrors.anomaly Pp.(str "save_regular: unexpected proof ending")

(***********************************************************************)
(* Special case to close a lemma without forcing a proof               *)
(***********************************************************************)
let save_lemma_admitted_delayed ~pm ~proof =
  let { Proof_object.proof_object; pinfo } = proof in
  let entries = process_proof ~info:pinfo.info proof_object in
  let typs = List.map (function { proof_entry_type }, uctx -> Option.get proof_entry_type, uctx) entries in
  (* Note: an alternative would be to compute sec_vars of the partial
     proof as a Future computation, as in compute_proof_using_for_admitted *)
  let sec_vars = if get_keep_admitted_vars () then (fst (List.hd entries)).proof_entry_secctx else None in
  (* If the proof is partial, do we want to take the (restriction on
     visible uvars of) uctx so far or (as done below) the initial ones
     that refers to only the types *)
  finish_admitted ~pm ~pinfo:proof.pinfo ~sec_vars typs

let save_lemma_proved_delayed ~pm ~proof ~idopt =
  (* vio2vo used to call this with invalid [pinfo], now it should work fine. *)
  let pinfo = process_idopt_for_save ~idopt proof.Proof_object.pinfo in
  let pm, _ = finish_proof ~pm proof.proof_object pinfo in
  pm

end (* Proof module *)

let _ = Ind_tables.declare_definition_scheme := declare_definition_scheme
let _ = Abstract.declare_abstract := Proof.declare_abstract

let build_by_tactic = Proof.build_by_tactic

(* This module could be merged with Obl, and placed before [Proof],
   however there is a single dependency on [Proof.start] for the interactive case *)
module Obls = struct
(* For the records fields, opens should go away one these types are private *)
open Obls_
open Obls_.Obligation
open Obls_.ProgramDecl

let reduce c =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  EConstr.Unsafe.to_constr (Reductionops.clos_norm_flags RedFlags.betaiota env sigma (EConstr.of_constr c))

let explain_no_obligations = function
    Some ident -> str "No obligations for program " ++ Id.print ident
  | None -> str "No obligations remaining"

module Error = struct

  let no_obligations n =
    CErrors.user_err (explain_no_obligations n)

  let ambiguous_program id ids =
    CErrors.user_err
      Pp.(str "More than one program with unsolved obligations: " ++ prlist Id.print ids
          ++ str "; use the \"of\" clause to specify, as in \"Obligation 1 of " ++ Id.print id ++ str "\"")

  let unknown_obligation num =
    CErrors.user_err (Pp.str (Printf.sprintf "Unknown obligation number %i" (succ num)))

  let already_solved num =
    CErrors.user_err Pp.(str "Obligation " ++ int num ++ str " already solved." )

  let depends num rem =
    CErrors.user_err
      ( str "Obligation " ++ int num
        ++ str " depends on obligation(s) "
        ++ pr_sequence (fun x -> int (succ x)) rem)

end

let default_tactic = ref (Proofview.tclUNIT ())

let subst_deps expand obls deps t =
  let osubst = Obls_.obl_substitution expand obls deps in
    (Vars.replace_vars (List.map (fun (n, (_, b)) -> n, b) osubst) t)

let subst_deps_obl obls obl =
  let t' = subst_deps true obls obl.obl_deps obl.obl_type in
  Obligation.set_type ~typ:t' obl

let is_defined obls x = not (Option.is_empty obls.(x).obl_body)

let deps_remaining obls deps =
  Int.Set.fold
    (fun x acc ->
      if is_defined obls x then acc
      else x :: acc)
    deps []

let goal_kind = Decls.(IsDefinition Definition)
let goal_proof_kind = Decls.(IsProof Lemma)

let kind_of_obligation o =
  match o with
  | Evar_kinds.Define false
  | Evar_kinds.Expand -> goal_kind
  | _ -> goal_proof_kind

(* Solve an obligation using tactics, return the corresponding proof term *)
let warn_solve_errored =
  CWarnings.create ~name:"solve_obligation_error" ~category:CWarnings.CoreCategories.tactics
    (fun err ->
      Pp.seq
        [ str "Solve Obligations tactic returned error: "
        ; err
        ; fnl ()
        ; str "This will become an error in the future" ])

let solve_by_tac prg obls i tac =
  let obl = obls.(i) in
  let obl = subst_deps_obl obls obl in
  let tac = Option.(default !default_tactic (append tac obl.obl_tac)) in
  let uctx = Internal.get_uctx prg in
  let uctx = UState.update_sigma_univs uctx (Global.universes ()) in
  let poly = Internal.get_poly prg in
  (* the status of [build_by_tactic] is dropped. *)
  try
    let env = Global.env () in
    let body, types, _univs, _, uctx =
      build_by_tactic env ~uctx ~poly ~typ:(EConstr.of_constr obl.obl_type) tac in
    Inductiveops.control_only_guard env (Evd.from_ctx uctx) (EConstr.of_constr body);
    Some (body, types, uctx)
  with
  | Tacticals.FailError (_, s) as exn ->
    let _ = Exninfo.capture exn in
    let loc = fst obl.obl_location in
    CErrors.user_err ?loc (Lazy.force s)
  (* If the proof is open we absorb the error and leave the obligation open *)
  | Proof.OpenProof _ ->
    None
  | e when CErrors.noncritical e ->
    let err = CErrors.print e in
    let loc = fst obl.obl_location in
    warn_solve_errored ?loc err;
    None

let solve_and_declare_by_tac prg obls i tac =
  match solve_by_tac prg obls i tac with
  | None -> None
  | Some (t, ty, uctx) ->
    let obl = obls.(i) in
    let prg, obl', _cst = declare_obligation prg obl ~body:t ~types:ty ~uctx in
    obls.(i) <- obl';
    Some prg

let solve_obligation_by_tac prg obls i tac =
  let obl = obls.(i) in
  match obl.obl_body with
  | Some _ -> None
  | None ->
    if List.is_empty (deps_remaining obls obl.obl_deps)
    then solve_and_declare_by_tac prg obls i tac
    else None

let get_unique_prog ~pm prg =
  match State.get_unique_open_prog pm prg with
  | Ok prg -> prg
  | Error [] ->
    Error.no_obligations None
  | Error ((id :: _) as ids) ->
    Error.ambiguous_program id ids

let solve_prg_obligations ~pm prg ?oblset tac =
  let { obls; remaining } = Internal.get_obligations prg in
  let rem = ref remaining in
  let obls' = Array.copy obls in
  let set = ref Int.Set.empty in
  let p = match oblset with
    | None -> (fun _ -> true)
    | Some s -> set := s;
      (fun i -> Int.Set.mem i !set)
  in
  let prg =
    Array.fold_left_i
      (fun i prg x ->
        if p i then (
          match solve_obligation_by_tac prg obls' i tac with
          | None -> prg
          | Some prg ->
            let deps = dependencies obls i in
            set := Int.Set.union !set deps;
            decr rem;
            prg)
        else prg)
      prg obls'
  in
  update_obls ~pm prg obls' !rem

let auto_solve_obligations ~pm n ?oblset tac : State.t * progress =
  Flags.if_verbose Feedback.msg_info
    (str "Solving obligations automatically...");
  let prg = get_unique_prog ~pm n in
  solve_prg_obligations ~pm prg ?oblset tac

let solve_obligation ?check_final prg num tac =
  let user_num = succ num in
  let { obls; remaining=rem } = Internal.get_obligations prg in
  let obl = obls.(num) in
  let remaining = deps_remaining obls obl.obl_deps in
  let () =
    if not (Option.is_empty obl.obl_body)
    then Error.already_solved user_num;
    if not (List.is_empty remaining)
    then Error.depends user_num remaining
  in
  let obl = subst_deps_obl obls obl in
  let kind = kind_of_obligation (snd obl.obl_status) in
  let evd = Evd.from_ctx (Internal.get_uctx prg) in
  let evd = Evd.update_sigma_univs (Global.universes ()) evd in
  let auto ~pm n oblset tac = auto_solve_obligations ~pm n ~oblset tac in
  let proof_ending =
    let name = Internal.get_name prg in
    Proof_ending.End_obligation {name; num; auto; check_final}
  in
  let cinfo = CInfo.make ~name:obl.obl_name ~typ:(EConstr.of_constr obl.obl_type) () in
  let using =
    let using = Internal.get_using prg in
    let env = Global.env () in
    let f {CInfo.name; typ; _} = name, [typ] in
    Option.map (interp_proof_using_gen f env evd [cinfo]) using
  in
  let poly = Internal.get_poly prg in
  let info = Info.make ~kind ~poly () in
  let lemma = Proof.start_core ~cinfo ~info ~proof_ending ?using evd  in
  let lemma = fst @@ Proof.by !default_tactic lemma in
  let lemma = Option.cata (fun tac -> Proof.set_endline_tactic tac lemma) lemma tac in
  lemma

let solve_obligations ~pm n tac =
  let prg = get_unique_prog ~pm n in
  solve_prg_obligations ~pm prg tac

(** Implements [Solve All Obligations with tac] *)
let solve_all_obligations ~pm tac =
  State.fold pm ~init:pm ~f:(fun k v pm ->
      solve_prg_obligations ~pm v tac |> fst)

(** Implements [Solve Obligations of name with tac] *)
let try_solve_obligations ~pm name tac =
  solve_obligations ~pm name tac |> fst

(** Implements [Obligation n of name with tac] *)
let obligation (user_num, name) ~pm tac =
  let num = pred user_num in
  let prg = get_unique_prog ~pm name in
  let { obls; remaining } = Internal.get_obligations prg in
  if num >= 0 && num < Array.length obls then
    let obl = obls.(num) in
    match obl.obl_body with
    | None -> solve_obligation prg num tac
    | Some r -> Error.already_solved user_num
  else Error.unknown_obligation num

(** Implements [Obligations of name] *)
let show_single_obligation i name obls x =
  let x = subst_deps_obl obls x in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let msg =
    str "Obligation" ++ spc ()
    ++ int (succ i)
    ++ spc () ++ str "of" ++ spc () ++ Id.print name ++ str ":" ++ spc ()
    ++ hov 1 (Printer.pr_constr_env env sigma x.obl_type
              ++ str "." ++ fnl ()) in
  Feedback.msg_info msg

let show_obligations_of_prg ?(msg = true) prg =
  let name = Internal.get_name prg in
  let {obls; remaining} = Internal.get_obligations prg in
  let showed = ref 5 in
    if msg then Feedback.msg_info (int remaining ++ str " obligation(s) remaining: ");
    Array.iteri
      (fun i x ->
         match x.obl_body with
         | None ->
           if !showed > 0 then begin
             decr showed;
             show_single_obligation i name obls x
           end
         | Some _ -> ())
      obls

let show_obligations ~pm ?(msg = true) name =
  let progs =
    match name with
    | None ->
      State.all pm
    | Some name ->
      (match State.find pm name with
       | Some prg -> [prg]
       | None -> Error.no_obligations (Some name))
  in
  List.iter (fun x -> show_obligations_of_prg ~msg x) progs

(** Implementation of the [Preterm of name] command *)
let show_term ~pm name =
  let prg = get_unique_prog ~pm name in
  ProgramDecl.show prg

let msg_generating_obl name obls =
  let len = Array.length obls in
  let info = Id.print name ++ str " has type-checked" in
  Feedback.msg_info
    (if len = 0 then info ++ str "."
     else
       info ++ str ", generating " ++ int len ++
       str (String.plural len " obligation"))

let add_definition ~pm ~info ~cinfo ~opaque ~uctx ?body
    ?tactic ?(reduce = reduce) ?using ?obl_hook obls =
  let obl_hook = Option.map (fun h -> State.PrgHook h) obl_hook in
  let prg =
    ProgramDecl.make ~info ~cinfo ~body ~opaque ~uctx ~reduce ~deps:[] ~possible_guard:None ?obl_hook ?using obls
  in
  let name = CInfo.get_name cinfo in
  let {obls;_} = Internal.get_obligations prg in
  if Int.equal (Array.length obls) 0 then (
    Flags.if_verbose (msg_generating_obl name) obls;
    let pm, cst = Obls_.declare_definition ~pm prg in
    pm, Defined cst)
  else
    let () = Flags.if_verbose (msg_generating_obl name) obls in
    let pm = State.add pm name prg in
    let pm, res = auto_solve_obligations ~pm (Some name) tactic in
    match res with
    | Remain rem ->
      Flags.if_verbose (show_obligations ~pm ~msg:false) (Some name);
      pm, res
    | _ -> pm, res

let add_mutual_definitions ~pm ~info ~cinfo ~opaque ~uctx ~bodies ~possible_guard
    ?tactic ?(reduce = reduce) ?using ?obl_hook obls =
  let obl_hook = Option.map (fun h -> State.PrgHook h) obl_hook in
  let deps = List.map CInfo.get_name cinfo in
  let pm =
    List.fold_left3
      (fun pm cinfo body obls ->
        let prg =
          ProgramDecl.make ~info ~cinfo ~opaque ~body:(Some body) ~uctx ~deps
            ~possible_guard:(Some possible_guard) ~reduce ?obl_hook ?using obls
        in
        State.add pm (CInfo.get_name cinfo) prg)
      pm cinfo bodies obls
  in
  let pm, _defined =
    List.fold_left
      (fun (pm, finished) x ->
        if finished then (pm, finished)
        else
          let pm, res = auto_solve_obligations ~pm (Some x) tactic in
          match res with
          | Defined _ ->
            (* If one definition is turned into a constant,
               the whole block is defined. *)
            (pm, true)
          | _ -> (pm, false))
      (pm, false) deps
  in
  pm

(** [admit_obligations ~pm name] implements [Admit Obligations of name] *)

let rec admit_prog ~pm prg =
  let {obls} = Internal.get_obligations prg in
  let is_open _ x = Option.is_empty x.obl_body && List.is_empty (deps_remaining obls x.obl_deps) in
  let i = match Array.findi is_open obls with
    | Some i -> i
    | None -> CErrors.anomaly (Pp.str "Could not find a solvable obligation.")
  in
  let proof = solve_obligation prg i None in
  let pm = Proof.save_admitted ~pm ~proof in
  match ProgMap.find_opt (Internal.get_name prg) pm with
  | Some prg -> admit_prog ~pm (CEphemeron.get prg)
  | None -> pm

let rec admit_all_obligations ~pm =
  let prg = State.first_pending pm in
  match prg with
  | None -> pm
  | Some prg ->
    let pm = admit_prog ~pm prg in
    admit_all_obligations ~pm

let admit_obligations ~pm name =
  match name with
  | None -> admit_all_obligations ~pm
  | Some _ ->
    let prg = get_unique_prog ~pm name in
    let pm = admit_prog ~pm prg in
    pm

(** Implements [Next Obligation of name with tac] and [Final Obligation of name with tac] *)
let next_obligation ~pm ?(final=false) name tac =
  let prg = match name with
    | None ->
      begin match State.first_pending pm with
        | Some prg -> prg
        | None ->
          Error.no_obligations None
      end
    | Some _ -> get_unique_prog ~pm name
  in
  let {obls; remaining} = Internal.get_obligations prg in
  let is_open _ x = Option.is_empty x.obl_body && List.is_empty (deps_remaining obls x.obl_deps) in
  let i = match Array.findi is_open obls with
    | Some i -> i
    | None ->
      match name with
      | None -> CErrors.anomaly (Pp.str "Could not find a solvable obligation.")
      | Some name -> CErrors.user_err (str "No more obligations for " ++ Id.print name ++ str ".")
  in
  let check_final = if not final then None
    else match name with
      | None -> Some AllFinal
      | Some name -> Some (SpecificFinal name)
  in
  solve_obligation ?check_final prg i tac

let check_program_libraries () =
  Rocqlib.check_required_library Rocqlib.datatypes_module_name;
  Rocqlib.check_required_library ["Corelib";"Init";"Specif"]

let program_inference_hook env sigma ev =
  let tac = !default_tactic in
  let evi = Evd.find_undefined sigma ev in
  let evi = Evarutil.nf_evar_info sigma evi in
  let env = Evd.evar_filtered_env env evi in
  try
    let concl = Evd.evar_concl evi in
    if not (Evarutil.is_ground_env sigma env &&
            Evarutil.is_ground_term sigma concl)
    then None
    else
      let c, sigma =
        Proof_.refine_by_tactic ~name:(Id.of_string "program_subproof")
          ~poly:false env sigma concl (Tacticals.tclSOLVE [tac])
      in
      Some (sigma, c)
  with
  | (Proof.OpenProof _ as e | Logic_monad.TacticFailure e) when CErrors.noncritical e ->
    CErrors.user_err Pp.(str "The statement obligations could not be resolved \
                      automatically, write a statement definition first.")

(* aliases *)
let prepare_obligations = prepare_obligations
let check_solved_obligations =
  let is_empty prg =
    let obls = (Internal.get_obligations (CEphemeron.get prg)).obls in
    let is_open x = Option.is_empty x.obl_body && List.is_empty (deps_remaining obls x.obl_deps) in
    Array.exists is_open obls in
  Obls_.check_solved_obligations is_empty
type fixpoint_kind = Obls_.fixpoint_kind =
  | IsFixpoint of lident option list | IsCoFixpoint
type nonrec progress = progress =
  | Remain of int | Dependent | Defined of GlobRef.t

end

module OblState = Obls_.State

let declare_constant ?loc ?local ~name ~kind ?typing_flags =
  declare_constant ~loc ?local ~name ~kind ~typing_flags

let declare_entry ?loc ~name ?scope ~kind ?user_warns ?hook ~impargs ~uctx entry =
  declare_entry ~loc ~name ?scope ~kind ~typing_flags:None ?clearbody:None ~user_warns ?hook ~impargs ~uctx entry

let declare_definition_full ~info ~cinfo ~opaque ~body ?using sigma =
  let c, uctx = declare_definition ~obls:[] ~info ~cinfo ~opaque ~body ?using sigma in
  c, if info.poly then Univ.ContextSet.empty else UState.context_set uctx

let declare_definition ~info ~cinfo ~opaque ~body ?using sigma =
  declare_definition ~obls:[] ~info ~cinfo ~opaque ~body ?using sigma |> fst
