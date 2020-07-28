(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
      ; scope : Locality.locality
      (**  [locality]: Locality of the original declaration *)
      ; dref : Names.GlobRef.t
      (** [ref]: identifier of the original declaration *)
      }
  end

  type 'a g = (S.t -> 'a -> 'a) CEphemeron.key
  type t = unit g

  let make_g hook = CEphemeron.create hook
  let make (hook : S.t -> unit) : t = CEphemeron.create (fun x () -> hook x)

  let call_g ?hook x s = Option.cata (fun hook -> CEphemeron.get hook x s) s hook
  let call ?hook x = Option.iter (fun hook -> CEphemeron.get hook x ()) hook

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
    ; scope : Locality.locality
    ; hook : Hook.t option
    }

  (** Note that [opaque] doesn't appear here as it is not known at the
     start of the proof in the interactive case. *)
  let make ?(poly=false) ?(inline=false) ?(kind=Decls.(IsDefinition Definition))
      ?(udecl=UState.default_univ_decl) ?(scope=Locality.Global Locality.ImportDefaultBehavior)
      ?hook () =
    { poly; inline; kind; udecl; scope; hook }

end

(** Declaration of constants and parameters *)

type 'a proof_entry = {
  proof_entry_body   : 'a Entries.const_entry_body;
  (* List of section variables *)
  proof_entry_secctx : Id.Set.t option;
  (* State id on which the completion of type checking is reported *)
  proof_entry_feedback : Stateid.t option;
  proof_entry_type        : Constr.types option;
  proof_entry_universes   : Entries.universes_entry;
  proof_entry_opaque      : bool;
  proof_entry_inline_code : bool;
}

let default_univ_entry = Entries.Monomorphic_entry Univ.ContextSet.empty

(** [univsbody] are universe-constraints attached to the body-only,
   used in vio-delayed opaque constants and private poly universes *)
let definition_entry_core ?(opaque=false) ?(inline=false) ?feedback_id ?section_vars ?types
    ?(univs=default_univ_entry) ?(eff=Evd.empty_side_effects) ?(univsbody=Univ.ContextSet.empty) body =
  { proof_entry_body = Future.from_val ((body,univsbody), eff);
    proof_entry_secctx = section_vars;
    proof_entry_type = types;
    proof_entry_universes = univs;
    proof_entry_opaque = opaque;
    proof_entry_feedback = feedback_id;
    proof_entry_inline_code = inline}

let definition_entry =
  definition_entry_core ?eff:None ?univsbody:None ?feedback_id:None ?section_vars:None

type 'a constant_entry =
  | DefinitionEntry of 'a proof_entry
  | ParameterEntry of Entries.parameter_entry
  | PrimitiveEntry of Entries.primitive_entry

type constant_obj = {
  cst_kind : Decls.logical_kind;
  cst_locl : Locality.import_status;
}

let load_constant i ((sp,kn), obj) =
  if Nametab.exists_cci sp then
    raise (DeclareUniv.AlreadyDeclared (None, Libnames.basename sp));
  let con = Global.constant_of_delta_kn kn in
  Nametab.push (Nametab.Until i) sp (GlobRef.ConstRef con);
  Dumpglob.add_constant_kind con obj.cst_kind

(* Opening means making the name without its module qualification available *)
let open_constant f i ((sp,kn), obj) =
  (* Never open a local definition *)
  match obj.cst_locl with
  | Locality.ImportNeedQualified -> ()
  | Locality.ImportDefaultBehavior ->
    let con = Global.constant_of_delta_kn kn in
    if Libobject.in_filter_ref (GlobRef.ConstRef con) f then
      Nametab.push (Nametab.Exactly i) sp (GlobRef.ConstRef con)

let exists_name id =
  Decls.variable_exists id || Global.exists_objlabel (Label.of_id id)

let check_exists id =
  if exists_name id then
    raise (DeclareUniv.AlreadyDeclared (None, id))

let cache_constant ((sp,kn), obj) =
  (* Invariant: the constant must exist in the logical environment *)
  let kn' =
    if Global.exists_objlabel (Label.of_id (Libnames.basename sp))
    then Constant.make1 kn
    else CErrors.anomaly Pp.(str"Missing constant " ++ Id.print(Libnames.basename sp) ++ str".")
  in
  assert (Constant.equal kn' (Constant.make1 kn));
  Nametab.push (Nametab.Until 1) sp (GlobRef.ConstRef (Constant.make1 kn));
  Dumpglob.add_constant_kind (Constant.make1 kn) obj.cst_kind

let discharge_constant ((sp, kn), obj) =
  Some obj

let classify_constant cst = Libobject.Substitute cst

let (objConstant : constant_obj Libobject.Dyn.tag) =
  let open Libobject in
  declare_object_full { (default_object "CONSTANT") with
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    classify_function = classify_constant;
    subst_function = ident_subst_function;
    discharge_function = discharge_constant }

let inConstant v = Libobject.Dyn.Easy.inj v objConstant

let update_tables c =
  Impargs.declare_constant_implicits c;
  Notation.declare_ref_arguments_scope Evd.empty (GlobRef.ConstRef c)

let register_constant kn kind local =
  let o = inConstant {
    cst_kind = kind;
    cst_locl = local;
  } in
  let id = Label.to_id (Constant.label kn) in
  let _ = Lib.add_leaf id o in
  update_tables kn

let register_side_effect (c, role) =
  let () = register_constant c Decls.(IsProof Theorem) Locality.ImportDefaultBehavior in
  match role with
  | None -> ()
  | Some (Evd.Schema (ind, kind)) -> DeclareScheme.declare_scheme kind [|ind,c|]

let get_roles export eff =
  let map c =
    let role = try Some (Cmap.find c eff.Evd.seff_roles) with Not_found -> None in
    (c, role)
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

let pure_definition_entry ?(opaque=false) ?(inline=false) ?types
    ?(univs=default_univ_entry) body =
  { proof_entry_body = Future.from_val ((body,Univ.ContextSet.empty), ());
    proof_entry_secctx = None;
    proof_entry_type = types;
    proof_entry_universes = univs;
    proof_entry_opaque = opaque;
    proof_entry_feedback = None;
    proof_entry_inline_code = inline}

let delayed_definition_entry ~opaque ?feedback_id ~section_vars ~univs ?types body =
  { proof_entry_body = body
  ; proof_entry_secctx = section_vars
  ; proof_entry_type = types
  ; proof_entry_universes = univs
  ; proof_entry_opaque = opaque
  ; proof_entry_feedback = feedback_id
  ; proof_entry_inline_code = false
  }

let cast_proof_entry e =
  let (body, ctx), () = Future.force e.proof_entry_body in
  let univs =
    if Univ.ContextSet.is_empty ctx then e.proof_entry_universes
    else match e.proof_entry_universes with
      | Entries.Monomorphic_entry ctx' ->
        (* This can actually happen, try compiling EqdepFacts for instance *)
        Entries.Monomorphic_entry (Univ.ContextSet.union ctx' ctx)
      | Entries.Polymorphic_entry _ ->
        CErrors.anomaly Pp.(str "Local universes in non-opaque polymorphic definition.");
  in
  { Entries.const_entry_body = body;
    const_entry_secctx = e.proof_entry_secctx;
    const_entry_feedback = e.proof_entry_feedback;
    const_entry_type = e.proof_entry_type;
    const_entry_universes = univs;
    const_entry_inline_code = e.proof_entry_inline_code;
  }

type ('a, 'b) effect_entry =
| EffectEntry : (private_constants, private_constants Entries.const_entry_body) effect_entry
| PureEntry : (unit, Constr.constr) effect_entry

let cast_opaque_proof_entry (type a b) (entry : (a, b) effect_entry) (e : a proof_entry) : b Entries.opaque_entry =
  let typ = match e.proof_entry_type with
  | None -> assert false
  | Some typ -> typ
  in
  let secctx = match e.proof_entry_secctx with
  | None ->
    let open Environ in
    let env = Global.env () in
    let hyp_typ, hyp_def =
      if List.is_empty (Environ.named_context env) then
        Id.Set.empty, Id.Set.empty
      else
        let ids_typ = global_vars_set env typ in
        let pf, env = match entry with
        | PureEntry ->
          let (pf, _), () = Future.force e.proof_entry_body in
          pf, env
        | EffectEntry ->
          let (pf, _), eff = Future.force e.proof_entry_body in
          let env = Safe_typing.push_private_constants env eff in
          pf, env
        in
        let vars = global_vars_set env pf in
        ids_typ, vars
    in
    let () = if Aux_file.recording () then record_aux env hyp_typ hyp_def in
    Environ.really_needed env (Id.Set.union hyp_typ hyp_def)
  | Some hyps -> hyps
  in
  let (body, univs : b * _) = match entry with
  | PureEntry ->
    let (body, uctx), () = Future.force e.proof_entry_body in
    let univs = match e.proof_entry_universes with
    | Entries.Monomorphic_entry uctx' ->
      Entries.Monomorphic_entry (Univ.ContextSet.union uctx uctx')
    | Entries.Polymorphic_entry _ ->
      assert (Univ.ContextSet.is_empty uctx);
      e.proof_entry_universes
    in
    body, univs
  | EffectEntry -> e.proof_entry_body, e.proof_entry_universes
  in
  { Entries.opaque_entry_body = body;
    opaque_entry_secctx = secctx;
    opaque_entry_feedback = e.proof_entry_feedback;
    opaque_entry_type = typ;
    opaque_entry_universes = univs;
  }

let feedback_axiom () = Feedback.(feedback AddedAxiom)

let is_unsafe_typing_flags () =
  let open Declarations in
  let flags = Environ.typing_flags (Global.env()) in
  not (flags.check_universes && flags.check_guarded && flags.check_positive)

let define_constant ~name cd =
  (* Logically define the constant and its subproofs, no libobject tampering *)
  let decl, unsafe = match cd with
    | DefinitionEntry de ->
      (* We deal with side effects *)
      if not de.proof_entry_opaque then
        let body, eff = Future.force de.proof_entry_body in
        (* This globally defines the side-effects in the environment
           and registers their libobjects. *)
        let () = export_side_effects eff in
        let de = { de with proof_entry_body = Future.from_val (body, ()) } in
        let cd = Entries.DefinitionEntry (cast_proof_entry de) in
        ConstantEntry cd, false
      else
        let map (body, eff) = body, eff.Evd.seff_private in
        let body = Future.chain de.proof_entry_body map in
        let de = { de with proof_entry_body = body } in
        let de = cast_opaque_proof_entry EffectEntry de in
        OpaqueEntry de, false
    | ParameterEntry e ->
      ConstantEntry (Entries.ParameterEntry e), not (Lib.is_modtype_strict())
    | PrimitiveEntry e ->
      ConstantEntry (Entries.PrimitiveEntry e), false
  in
  let kn = Global.add_constant name decl in
  if unsafe || is_unsafe_typing_flags() then feedback_axiom();
  kn

let declare_constant ?(local = Locality.ImportDefaultBehavior) ~name ~kind cd =
  let () = check_exists name in
  let kn = define_constant ~name cd in
  (* Register the libobjects attached to the constants *)
  let () = register_constant kn kind local in
  kn

let declare_private_constant ?role ?(local = Locality.ImportDefaultBehavior) ~name ~kind de =
  let kn, eff =
    let de =
      if not de.proof_entry_opaque then
        DefinitionEff (cast_proof_entry de)
      else
        let de = cast_opaque_proof_entry PureEntry de in
        OpaqueEff de
    in
    Global.add_private_constant name de
  in
  let () = register_constant kn kind local in
  let seff_roles = match role with
  | None -> Cmap.empty
  | Some r -> Cmap.singleton kn r
  in
  let eff = { Evd.seff_private = eff; Evd.seff_roles; } in
  kn, eff

let inline_private_constants ~uctx env ce =
  let body, eff = Future.force ce.proof_entry_body in
  let cb, ctx = Safe_typing.inline_private_constants env (body, eff.Evd.seff_private) in
  let uctx = UState.merge ~sideff:true Evd.univ_rigid uctx ctx in
  cb, uctx

(** Declaration of section variables and local definitions *)
type variable_declaration =
  | SectionLocalDef of Evd.side_effects proof_entry
  | SectionLocalAssum of { typ:Constr.types; impl:Glob_term.binding_kind; }

(* This object is only for things which iterate over objects to find
   variables (only Prettyp.print_context AFAICT) *)
let objVariable : unit Libobject.Dyn.tag =
  let open Libobject in
  declare_object_full { (default_object "VARIABLE") with
    classify_function = (fun () -> Dispose)}

let inVariable v = Libobject.Dyn.Easy.inj v objVariable

let declare_variable_core ~name ~kind d =
  (* Variables are distinguished by only short names *)
  if Decls.variable_exists name then
    raise (DeclareUniv.AlreadyDeclared (None, name));

  let impl,opaque = match d with (* Fails if not well-typed *)
    | SectionLocalAssum {typ;impl} ->
      let () = Global.push_named_assum (name,typ) in
      impl, true
    | SectionLocalDef (de) ->
      (* The body should already have been forced upstream because it is a
         section-local definition, but it's not enforced by typing *)
      let ((body, body_ui), eff) = Future.force de.proof_entry_body in
      let () = export_side_effects eff in
      let poly, entry_ui = match de.proof_entry_universes with
        | Entries.Monomorphic_entry uctx -> false, uctx
        | Entries.Polymorphic_entry (_, uctx) -> true, Univ.ContextSet.of_context uctx
      in
      let univs = Univ.ContextSet.union body_ui entry_ui in
      (* We must declare the universe constraints before type-checking the
         term. *)
      let () = DeclareUctx.declare_universe_context ~poly univs in
      let se = {
        Entries.secdef_body = body;
        secdef_secctx = de.proof_entry_secctx;
        secdef_feedback = de.proof_entry_feedback;
        secdef_type = de.proof_entry_type;
      } in
      let () = Global.push_named_def (name, se) in
      Glob_term.Explicit, de.proof_entry_opaque
  in
  Nametab.push (Nametab.Until 1) (Libnames.make_path DirPath.empty name) (GlobRef.VarRef name);
  Decls.(add_variable_data name {opaque;kind});
  ignore(Lib.add_leaf name (inVariable ()) : Libobject.object_name);
  Impargs.declare_var_implicits ~impl name;
  Notation.declare_ref_arguments_scope Evd.empty (GlobRef.VarRef name)

let declare_variable ~name ~kind ~typ ~impl =
  declare_variable_core ~name ~kind (SectionLocalAssum { typ; impl })

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

let recursive_message isfix i l =
  (if isfix then fixpoint_message i else cofixpoint_message) l

let definition_message id =
  Flags.if_verbose Feedback.msg_info (Id.print id ++ str " is defined")

let assumption_message id =
  (* Changing "assumed" to "declared", "assuming" referring more to
  the type of the object than to the name of the object (see
  discussion on coqdev: "Chapter 4 of the Reference Manual", 8/10/2015) *)
  Flags.if_verbose Feedback.msg_info (Id.print id ++ str " is declared")

module Internal = struct

  let map_entry_body ~f entry =
    { entry with proof_entry_body = Future.chain entry.proof_entry_body f }

  let map_entry_type ~f entry =
    { entry with proof_entry_type = f entry.proof_entry_type }

  let set_opacity ~opaque entry =
    { entry with proof_entry_opaque = opaque }

  let rec decompose len c t accu =
    let open Constr in
    let open Context.Rel.Declaration in
    if len = 0 then (c, t, accu)
    else match kind c, kind t with
      | Lambda (na, u, c), Prod (_, _, t) ->
        decompose (pred len) c t (LocalAssum (na, u) :: accu)
      | LetIn (na, b, u, c), LetIn (_, _, _, t) ->
        decompose (pred len) c t (LocalDef (na, b, u) :: accu)
      | _ -> assert false

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
          then mkVar (NamedDecl.get_id decl) :: accu
          else accu
        in
        shrink ctx sign c t accu
    | _ -> assert false

  let shrink_entry sign const =
    let typ = match const.proof_entry_type with
      | None -> assert false
      | Some t -> t
    in
    (* The body has been forced by the call to [build_constant_by_tactic] *)
    let () = assert (Future.is_over const.proof_entry_body) in
    let ((body, uctx), eff) = Future.force const.proof_entry_body in
    let (body, typ, ctx) = decompose (List.length sign) body typ [] in
    let (body, typ, args) = shrink ctx sign body typ [] in
    { const with
      proof_entry_body = Future.from_val ((body, uctx), eff)
    ; proof_entry_type = Some typ
    }, args

  module Constant = struct
    type t = constant_obj
    let tag = objConstant
    let kind obj = obj.cst_kind
  end

  let objVariable = objVariable

end

let declare_definition_scheme ~internal ~univs ~role ~name c =
  let kind = Decls.(IsDefinition Scheme) in
  let entry = pure_definition_entry ~univs c in
  let kn, eff = declare_private_constant ~role ~kind ~name entry in
  let () = if internal then () else definition_message name in
  kn, eff

(* Locality stuff *)
let declare_entry_core ~name ~scope ~kind ?hook ~obls ~impargs ~uctx entry =
  let should_suggest =
    entry.proof_entry_opaque
    && not (List.is_empty (Global.named_context()))
    && Option.is_empty entry.proof_entry_secctx
  in
  let ubind = UState.universe_binders uctx in
  let dref = match scope with
  | Locality.Discharge ->
    let () = declare_variable_core ~name ~kind (SectionLocalDef entry) in
    if should_suggest then Proof_using.suggest_variable (Global.env ()) name;
    Names.GlobRef.VarRef name
  | Locality.Global local ->
    let kn = declare_constant ~name ~local ~kind (DefinitionEntry entry) in
    let gr = Names.GlobRef.ConstRef kn in
    if should_suggest then Proof_using.suggest_constant (Global.env ()) kn;
    let () = DeclareUniv.declare_univ_binders gr ubind in
    gr
  in
  let () = Impargs.maybe_declare_manual_implicits false dref impargs in
  let () = definition_message name in
  Hook.call ?hook { Hook.S.uctx; obls; scope; dref };
  dref

let declare_entry = declare_entry_core ~obls:[]

let mutual_make_bodies ~fixitems ~rec_declaration ~possible_indexes =
  match possible_indexes with
  | Some possible_indexes ->
    let env = Global.env() in
    let indexes = Pretyping.search_guard env possible_indexes rec_declaration in
    let vars = Vars.universes_of_constr (Constr.mkFix ((indexes,0),rec_declaration)) in
    let fixdecls = CList.map_i (fun i _ -> Constr.mkFix ((indexes,i),rec_declaration)) 0 fixitems in
    vars, fixdecls, Some indexes
  | None ->
    let fixdecls = CList.map_i (fun i _ -> Constr.mkCoFix (i,rec_declaration)) 0 fixitems in
    let vars = Vars.universes_of_constr (List.hd fixdecls) in
    vars, fixdecls, None

let declare_mutually_recursive_core ~info ~cinfo ~opaque ~ntns ~uctx ~rec_declaration ~possible_indexes ?(restrict_ucontext=true) () =
  let { Info.poly; udecl; scope; kind; _ } = info in
  let vars, fixdecls, indexes =
    mutual_make_bodies ~fixitems:cinfo ~rec_declaration ~possible_indexes in
  let uctx, univs =
    (* XXX: Obligations don't do this, this seems like a bug? *)
    if restrict_ucontext
    then
      let uctx = UState.restrict uctx vars in
      let univs = UState.check_univ_decl ~poly uctx udecl in
      uctx, univs
    else
      let univs = UState.univ_entry ~poly uctx in
      uctx, univs
  in
  let csts = CList.map2
      (fun CInfo.{ name; typ; impargs } body ->
         let entry = definition_entry ~opaque ~types:typ ~univs body in
         declare_entry ~name ~scope ~kind ~impargs ~uctx entry)
      cinfo fixdecls
  in
  let isfix = Option.has_some possible_indexes in
  let fixnames = List.map (fun { CInfo.name } -> name) cinfo in
  recursive_message isfix indexes fixnames;
  List.iter (Metasyntax.add_notation_interpretation (Global.env())) ntns;
  csts

let declare_mutually_recursive = declare_mutually_recursive_core ~restrict_ucontext:true ()

let warn_let_as_axiom =
  CWarnings.create ~name:"let-as-axiom" ~category:"vernacular"
    Pp.(fun id -> strbrk "Let definition" ++ spc () ++ Names.Id.print id ++
                  spc () ++ strbrk "declared as an axiom.")

let declare_assumption ~name ~scope ~hook ~impargs ~uctx pe =
  let local = match scope with
    | Locality.Discharge -> warn_let_as_axiom name; Locality.ImportNeedQualified
    | Locality.Global local -> local
  in
  let kind = Decls.(IsAssumption Conjectural) in
  let decl = ParameterEntry pe in
  let kn = declare_constant ~name ~local ~kind decl in
  let dref = Names.GlobRef.ConstRef kn in
  let () = Impargs.maybe_declare_manual_implicits false dref impargs in
  let () = assumption_message name in
  let () = DeclareUniv.declare_univ_binders dref (UState.universe_binders uctx) in
  let () = Hook.(call ?hook { S.uctx; obls = []; scope; dref}) in
  dref

(* Preparing proof entries *)
let error_unresolved_evars env sigma t evars =
  let pr_unresolved_evar e =
    hov 2 (str"- " ++ Printer.pr_existential_key sigma e ++  str ": " ++
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
  let t = EConstr.of_constr t in
  let evars = Evarutil.undefined_evars_of_term sigma t in
  if not (Evar.Set.is_empty evars) then error_unresolved_evars env sigma t evars

let prepare_definition ~info ~opaque ~body ~typ sigma =
  let { Info.poly; udecl; inline; _ } = info in
  let env = Global.env () in
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:false
      sigma (fun nf -> nf body, Option.map nf typ)
  in
  Option.iter (check_evars_are_solved env sigma) types;
  check_evars_are_solved env sigma body;
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let entry = definition_entry ~opaque ~inline ?types ~univs body in
  let uctx = Evd.evar_universe_context sigma in
  entry, uctx

let declare_definition_core ~info ~cinfo ~opaque ~obls ~body sigma =
  let { CInfo.name; impargs; typ; _ } = cinfo in
  let entry, uctx = prepare_definition ~info ~opaque ~body ~typ sigma in
  let { Info.scope; kind; hook; _ } = info in
  declare_entry_core ~name ~scope ~kind ~impargs ~obls ?hook ~uctx entry, uctx

let declare_definition ~info ~cinfo ~opaque ~body sigma =
  declare_definition_core ~obls:[] ~info ~cinfo ~opaque ~body sigma |> fst

let prepare_obligation ~name ~types ~body sigma =
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
  let obls, _, body, cty = RetrieveObl.retrieve_obligations env name sigma 0 body types in
  let uctx = Evd.evar_universe_context sigma in
  body, cty, uctx, obls

let prepare_parameter ~poly ~udecl ~types sigma =
  let env = Global.env () in
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;
  let sigma, typ = Evarutil.finalize ~abort_on_undefined_evars:true
      sigma (fun nf -> nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  sigma, (None(*proof using*), (typ, univs), None(*inline*))

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
  let set_body ~body obl = {obl with obl_body = Some body}
end

type obligations = {obls : Obligation.t array; remaining : int}
type fixpoint_kind = IsFixpoint of lident option list | IsCoFixpoint

module ProgramDecl = struct

  type 'a t =
    { prg_cinfo : constr CInfo.t
    ; prg_info : Info.t
    ; prg_opaque : bool
    ; prg_hook : 'a Hook.g option
    ; prg_body : constr
    ; prg_uctx : UState.t
    ; prg_obligations : obligations
    ; prg_deps : Id.t list
    ; prg_fixkind : fixpoint_kind option
    ; prg_notations : Vernacexpr.decl_notation list
    ; prg_reduce : constr -> constr
    }

  open Obligation

  let make ~info ~cinfo ~opaque ~ntns ~reduce ~deps ~uctx ~body ~fixpoint_kind ?obl_hook obls =
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
    ; prg_hook = obl_hook
    ; prg_opaque = opaque
    ; prg_body = body
    ; prg_uctx
    ; prg_obligations = {obls = obls'; remaining = Array.length obls'}
    ; prg_deps = deps
    ; prg_fixkind = fixpoint_kind
    ; prg_notations = ntns
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
      let ctx, b = Term.decompose_lam_assum c in
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

let unfold_entry cst = Hints.HintsUnfoldEntry [EvalConstRef cst]

let add_hint local prg cst =
  let locality = if local then Goptions.OptLocal else Goptions.OptExport in
  Hints.add_hints ~locality [Id.to_string prg.prg_cinfo.CInfo.name] (unfold_entry cst)

(* true = hide obligations *)
let get_hide_obligations =
  Goptions.declare_bool_option_and_ref
    ~depr:true
    ~key:["Hide"; "Obligations"]
    ~value:false

let declare_obligation prg obl ~uctx ~types ~body =
  let poly = prg.prg_info.Info.poly in
  let univs = UState.univ_entry ~poly uctx in
  let body = prg.prg_reduce body in
  let types = Option.map prg.prg_reduce types in
  match obl.obl_status with
  | _, Evar_kinds.Expand ->
    (false, {obl with obl_body = Some (TermObl body)}, [])
  | force, Evar_kinds.Define opaque ->
    let opaque = (not force) && opaque in
    let poly = prg.prg_info.Info.poly in
    let ctx, body, ty, args =
      if not poly then shrink_body body types
      else ([], body, types, [||])
    in
    let ce = definition_entry ?types:ty ~opaque ~univs body in
    (* ppedrot: seems legit to have obligations as local *)
    let constant =
      declare_constant ~name:obl.obl_name
        ~local:Locality.ImportNeedQualified
        ~kind:Decls.(IsProof Property)
        (DefinitionEntry ce)
    in
    if not opaque then
      add_hint (Locality.make_section_locality None) prg constant;
    definition_message obl.obl_name;
    let body =
      match univs with
      | Entries.Polymorphic_entry (_, uctx) ->
        Some (DefinedObl (constant, Univ.UContext.instance uctx))
      | Entries.Monomorphic_entry _ ->
        Some
          (TermObl
             (it_mkLambda_or_LetIn_or_clean
                (mkApp (mkConst constant, args))
                ctx))
    in
    (true, {obl with obl_body = body}, [GlobRef.ConstRef constant])

(* Updating the obligation meta-info on close *)

let not_transp_msg =
  Pp.(
    str "Obligation should be transparent but was declared opaque."
    ++ spc ()
    ++ str "Use 'Defined' instead.")

let err_not_transp () =
  CErrors.user_err ~hdr:"Program" not_transp_msg

module ProgMap = Id.Map

module State = struct

  type t = t ProgramDecl.t CEphemeron.key ProgMap.t

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
end

(* In all cases, the use of the map is read-only so we don't expose the ref *)
let map_keys m = ProgMap.fold (fun k _ l -> k :: l) m []

let check_solved_obligations ~pm ~what_for : unit =
  if not (ProgMap.is_empty pm) then
    let keys = map_keys pm in
    let have_string = if Int.equal (List.length keys) 1 then " has " else " have " in
    CErrors.user_err ~hdr:"Program"
      Pp.(
        str "Unsolved obligations when closing "
        ++ what_for ++ str ":" ++ spc ()
        ++ prlist_with_sep spc (fun x -> Id.print x) keys
        ++ str have_string
        ++ str "unsolved obligations" )

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

let hide_obligation () =
  Coqlib.check_required_library ["Coq"; "Program"; "Tactics"];
  UnivGen.constr_of_monomorphic_global
    (Coqlib.lib_ref "program.tactics.obligation")

(* XXX: Is this the right place? *)
let rec prod_app t n =
  match
    Constr.kind
      (EConstr.Unsafe.to_constr
         (Termops.strip_outer_cast Evd.empty (EConstr.of_constr t)))
    (* FIXME *)
  with
  | Prod (_, _, b) -> Vars.subst1 n b
  | LetIn (_, b, t, b') -> prod_app (Vars.subst1 b b') n
  | _ ->
    CErrors.user_err ~hdr:"prod_app"
      Pp.(str "Needed a product, but didn't find one" ++ fnl ())

(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_applist t nL = List.fold_left prod_app t nL

let replace_appvars subst =
  let rec aux c =
    let f, l = decompose_app c in
    if isVar f then
      try
        let c' = List.map (Constr.map aux) l in
        let t, b = Id.List.assoc (destVar f) subst in
        mkApp
          ( delayed_force hide_obligation
          , [|prod_applist t c'; Term.applistc b c'|] )
      with Not_found -> Constr.map aux c
    else Constr.map aux c
  in
  Constr.map aux

let subst_prog subst prg =
  if get_hide_obligations () then
    ( replace_appvars subst prg.prg_body
    , replace_appvars subst (* Termops.refresh_universes *) prg.prg_cinfo.CInfo.typ )
  else
    let subst' = List.map (fun (n, (_, b)) -> (n, b)) subst in
    ( Vars.replace_vars subst' prg.prg_body
    , Vars.replace_vars subst' (* Termops.refresh_universes *) prg.prg_cinfo.CInfo.typ )

let declare_definition ~pm prg =
  let varsubst = obligation_substitution true prg in
  let sigma = Evd.from_ctx prg.prg_uctx in
  let body, types = subst_prog varsubst prg in
  let body, types = EConstr.(of_constr body, Some (of_constr types)) in
  let cinfo = { prg.prg_cinfo with CInfo.typ = types } in
  let name, info, opaque = prg.prg_cinfo.CInfo.name, prg.prg_info, prg.prg_opaque in
  let obls = List.map (fun (id, (_, c)) -> (id, c)) varsubst in
  (* XXX: This is doing normalization twice *)
  let kn, uctx = declare_definition_core ~cinfo ~info ~obls ~body ~opaque sigma in
  (* XXX: We call the obligation hook here, by consistency with the
     previous imperative behaviour, however I'm not sure this is right *)
  let pm = Hook.call_g ?hook:prg.prg_hook
      { Hook.S.uctx; obls; scope = prg.prg_info.Info.scope; dref = kn} pm in
  let pm = progmap_remove pm prg in
  pm, kn

let rec lam_index n t acc =
  match Constr.kind t with
  | Lambda ({Context.binder_name = Name n'}, _, _) when Id.equal n n' -> acc
  | Lambda (_, _, b) -> lam_index n b (succ acc)
  | _ -> raise Not_found

let compute_possible_guardness_evidences n fixbody fixtype =
  match n with
  | Some {CAst.loc; v = n} -> [lam_index n fixbody 0]
  | None ->
    (* If recursive argument was not given by user, we try all args.
         An earlier approach was to look only for inductive arguments,
         but doing it properly involves delta-reduction, and it finally
         doesn't seem to worth the effort (except for huge mutual
         fixpoints ?) *)
    let m = Termops.nb_prod Evd.empty (EConstr.of_constr fixtype) (* FIXME *) in
    let ctx = fst (Term.decompose_prod_n_assum m fixtype) in
    List.map_i (fun i _ -> i) 0 ctx

let declare_mutual_definition ~pm l =
  let len = List.length l in
  let first = List.hd l in
  let defobl x =
    let oblsubst = obligation_substitution true x in
    let subs, typ = subst_prog oblsubst x in
    let env = Global.env () in
    let sigma = Evd.from_ctx x.prg_uctx in
    let r = Retyping.relevance_of_type env sigma (EConstr.of_constr typ) in
    let term =
      snd (Reductionops.splay_lam_n env sigma len (EConstr.of_constr subs))
    in
    let typ =
      snd (Reductionops.splay_prod_n env sigma len (EConstr.of_constr typ))
    in
    let term = EConstr.to_constr sigma term in
    let typ = EConstr.to_constr sigma typ in
    let def = (x.prg_reduce term, r, x.prg_reduce typ, x.prg_cinfo.CInfo.impargs) in
    let oblsubst = List.map (fun (id, (_, c)) -> (id, c)) oblsubst in
    (def, oblsubst)
  in
  let defs, obls =
    List.fold_right
      (fun x (defs, obls) ->
        let xdef, xobls = defobl x in
        (xdef :: defs, xobls @ obls))
      l ([], [])
  in
  (*   let fixdefs = List.map reduce_fix fixdefs in *)
  let fixdefs, fixrs, fixtypes, fixitems =
    List.fold_right2
      (fun (d, r, typ, impargs) name (a1, a2, a3, a4) ->
        ( d :: a1
        , r :: a2
        , typ :: a3
        , CInfo.{name; typ; impargs; args = []} :: a4 ))
      defs first.prg_deps ([], [], [], [])
  in
  let fixkind = Option.get first.prg_fixkind in
  let arrrec, recvec = (Array.of_list fixtypes, Array.of_list fixdefs) in
  let rvec = Array.of_list fixrs in
  let namevec = Array.of_list (List.map (fun x -> Name x.prg_cinfo.CInfo.name) l) in
  let rec_declaration = (Array.map2 Context.make_annot namevec rvec, arrrec, recvec) in
  let possible_indexes =
    match fixkind with
    | IsFixpoint wfl ->
      Some (List.map3 compute_possible_guardness_evidences wfl fixdefs fixtypes)
    | IsCoFixpoint -> None
  in
  (* Declare the recursive definitions *)
  let kns =
    declare_mutually_recursive_core ~info:first.prg_info ~ntns:first.prg_notations
      ~uctx:first.prg_uctx ~rec_declaration ~possible_indexes ~opaque:first.prg_opaque
      ~restrict_ucontext:false ~cinfo:fixitems ()
  in
  (* Only for the first constant *)
  let dref = List.hd kns in
  let scope = first.prg_info.Info.scope in
  let s_hook = {Hook.S.uctx = first.prg_uctx; obls; scope; dref} in
  Hook.call ?hook:first.prg_info.Info.hook s_hook;
  (* XXX: We call the obligation hook here, by consistency with the
     previous imperative behaviour, however I'm not sure this is right *)
  let pm = Hook.call_g ?hook:first.prg_hook s_hook pm in
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
        let pm, kn = declare_mutual_definition ~pm progs in
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

let update_program_decl_on_defined ~pm prg obls num obl ~uctx rem ~auto =
  let obls = Array.copy obls in
  let () = obls.(num) <- obl in
  let prg = {prg with prg_uctx = uctx} in
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

type obligation_qed_info = {name : Id.t; num : int; auto : obligation_resolver}

let obligation_terminator ~pm ~entry ~uctx ~oinfo:{name; num; auto} =
  let env = Global.env () in
  let ty = entry.proof_entry_type in
  let body, uctx = inline_private_constants ~uctx env entry in
  let sigma = Evd.from_ctx uctx in
  Inductiveops.control_only_guard (Global.env ()) sigma
    (EConstr.of_constr body);
  (* Declare the obligation ourselves and drop the hook *)
  let prg = Option.get (State.find pm name) in
  let {obls; remaining = rem} = prg.prg_obligations in
  let obl = obls.(num) in
  let status =
    match (obl.obl_status, entry.proof_entry_opaque) with
    | (_, Evar_kinds.Expand), true -> err_not_transp ()
    | (true, _), true -> err_not_transp ()
    | (false, _), true -> Evar_kinds.Define true
    | (_, Evar_kinds.Define true), false -> Evar_kinds.Define false
    | (_, status), false -> status
  in
  let obl = {obl with obl_status = (false, status)} in
  let poly = prg.prg_info.Info.poly in
  let uctx = if poly then uctx else UState.union prg.prg_uctx uctx in
  let defined, obl, cst = declare_obligation prg obl ~body ~types:ty ~uctx in
  let prg_ctx =
    if poly then
      (* Polymorphic *)
      (* We merge the new universes and constraints of the
         polymorphic obligation with the existing ones *)
      UState.union prg.prg_uctx uctx
    else if
      (* The first obligation, if defined,
         declares the univs of the constant,
         each subsequent obligation declares its own additional
         universes and constraints if any *)
      defined
    then
      UState.from_env (Global.env ())
    else uctx
  in
  let pm =
    update_program_decl_on_defined ~pm prg obls num obl ~uctx:prg_ctx rem ~auto in
  pm, cst

(* Similar to the terminator but for the admitted path; this assumes
   the admitted constant was already declared.

   FIXME: There is duplication of this code with obligation_terminator
   and Obligations.admit_obligations *)
let obligation_admitted_terminator ~pm {name; num; auto} ctx' dref =
  let prg = Option.get (State.find pm name) in
  let {obls; remaining = rem} = prg.prg_obligations in
  let obl = obls.(num) in
  let cst = match dref with GlobRef.ConstRef cst -> cst | _ -> assert false in
  let transparent = Environ.evaluable_constant cst (Global.env ()) in
  let () =
    match obl.obl_status with
    | true, Evar_kinds.Expand | true, Evar_kinds.Define true ->
      if not transparent then err_not_transp ()
    | _ -> ()
  in
  let inst, ctx' =
    if not prg.prg_info.Info.poly (* Not polymorphic *) then
      (* The universe context was declared globally, we continue
         from the new global environment. *)
      let ctx = UState.from_env (Global.env ()) in
      let ctx' = UState.merge_subst ctx (UState.subst ctx') in
      (Univ.Instance.empty, ctx')
    else
      (* We get the right order somehow, but surely it could be enforced in a clearer way. *)
      let uctx = UState.context ctx' in
      (Univ.UContext.instance uctx, ctx')
  in
  let obl = {obl with obl_body = Some (DefinedObl (cst, inst))} in
  let () = if transparent then add_hint true prg cst in
  update_program_decl_on_defined ~pm prg obls num obl ~uctx:ctx' rem ~auto

end

(************************************************************************)
(* Handling of interactive proofs                                       *)
(************************************************************************)

type lemma_possible_guards = int list list

module Proof_ending = struct

  type t =
    | Regular
    | End_obligation of Obls_.obligation_qed_info
    | End_derive of { f : Id.t; name : Id.t }
    | End_equations of
        { hook : pm:Obls_.State.t -> Constant.t list -> Evd.evar_map -> Obls_.State.t
        ; i : Id.t
        ; types : (Environ.env * Evar.t * Evd.evar_info * EConstr.named_context * Evd.econstr) list
        ; sigma : Evd.evar_map
        }

end

(* Alias *)
module Proof_ = Proof
module Proof = struct

module Proof_info = struct

  type t =
    { cinfo : Constr.t CInfo.t list
    (** cinfo contains each individual constant info in a mutual decl *)
    ; info : Info.t
    ; proof_ending : Proof_ending.t CEphemeron.key
    (* This could be improved and the CEphemeron removed *)
    ; compute_guard : lemma_possible_guards
    (** thms and compute guard are specific only to
       start_lemma_with_initialization + regular terminator, so we
       could make this per-proof kind *)
    }

  let make ~cinfo ~info ?(compute_guard=[]) ?(proof_ending=Proof_ending.Regular) () =
    { cinfo
    ; info
    ; compute_guard
    ; proof_ending = CEphemeron.create proof_ending
    }

  (* This is used due to a deficiency on the API, should fix *)
  let add_first_thm ~pinfo ~name ~typ ~impargs =
    let cinfo : Constr.t CInfo.t = CInfo.make ~name ~impargs ~typ:(EConstr.Unsafe.to_constr typ) () in
    { pinfo with cinfo = cinfo :: pinfo.cinfo }

  (* This is called by the STM, and we have to fixup cinfo later as
     indeed it will not be correct *)
  let default () = make ~cinfo:[] ~info:(Info.make ()) ()
end

type t =
  { endline_tactic : Genarg.glob_generic_argument option
  ; section_vars : Id.Set.t option
  ; proof : Proof.t
  ; initial_euctx : UState.t
  (** The initial universe context (for the statement) *)
  ; pinfo : Proof_info.t
  }

(*** Proof Global manipulation ***)

let info { pinfo } = pinfo
let get ps = ps.proof
let get_name ps = (Proof.data ps.proof).Proof.name
let get_initial_euctx ps = ps.initial_euctx

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
      let Genarg.GenArg (Genarg.Glbwit tag, tac) = tac in
      let tac = Geninterp.interp tag ist tac in
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

let start_proof_core ~name ~typ ~pinfo ?(sign=initialize_named_context_for_proof ()) sigma =
  (* In ?sign, we remove the bodies of variables in the named context
     marked "opaque", this is a hack tho, see #10446, and
     build_constant_by_tactic uses a different method that would break
     program_inference_hook *)
  let { Proof_info.info = { Info.poly; _ }; _ } = pinfo in
  let goals = [Global.env_of_context sign, typ] in
  let proof = Proof.start ~name ~poly sigma goals in
  let initial_euctx = Evd.evar_universe_context Proof.((data proof).sigma) in
  { proof
  ; endline_tactic = None
  ; section_vars = None
  ; initial_euctx
  ; pinfo
  }

(** [start_proof ~info ~cinfo sigma] starts a proof of [cinfo].
   The proof is started in the evar map [sigma] (which
   can typically contain universe constraints) *)
let start_core ~info ~cinfo ?proof_ending sigma =
  let { CInfo.name; typ; _ } = cinfo in
  let cinfo = [{ cinfo with CInfo.typ = EConstr.Unsafe.to_constr cinfo.CInfo.typ }] in
  let pinfo = Proof_info.make ~cinfo ~info ?proof_ending () in
  start_proof_core ~name ~typ ~pinfo ?sign:None sigma

let start = start_core ?proof_ending:None

let start_dependent ~info ~name ~proof_ending goals =
  let proof = Proof.dependent_start ~name ~poly:info.Info.poly goals in
  let initial_euctx = Evd.evar_universe_context Proof.((data proof).sigma) in
  let cinfo = [] in
  let pinfo = Proof_info.make ~info ~cinfo ~proof_ending () in
  { proof
  ; endline_tactic = None
  ; section_vars = None
  ; initial_euctx
  ; pinfo
  }

let start_derive ~f ~name ~info goals =
  let proof_ending = Proof_ending.End_derive {f; name} in
  start_dependent ~info ~name ~proof_ending goals

let start_equations ~name ~info ~hook ~types sigma goals =
  let proof_ending = Proof_ending.End_equations {hook; i=name; types; sigma} in
  start_dependent ~name ~info ~proof_ending goals

let rec_tac_initializer finite guard thms snl =
  if finite then
    match List.map (fun { CInfo.name; typ } -> name, (EConstr.of_constr typ)) thms with
    | (id,_)::l -> Tactics.mutual_cofix id l 0
    | _ -> assert false
  else
    (* nl is dummy: it will be recomputed at Qed-time *)
    let nl = match snl with
     | None -> List.map succ (List.map List.last guard)
     | Some nl -> nl
    in match List.map2 (fun { CInfo.name; typ } n -> (name, n, (EConstr.of_constr typ))) thms nl with
       | (id,n,_)::l -> Tactics.mutual_fix id n l 0
       | _ -> assert false

let start_with_initialization ~info ~cinfo sigma =
  let { CInfo.name; typ; args } = cinfo in
  let init_tac = Tactics.auto_intros_tac args in
  let pinfo = Proof_info.make ~cinfo:[cinfo] ~info () in
  let lemma = start_proof_core ~name ~typ:(EConstr.of_constr typ) ~pinfo ?sign:None sigma in
  map lemma ~f:(fun p ->
      pi1 @@ Proof.run_tactic Global.(env ()) init_tac p)

type mutual_info = (bool * lemma_possible_guards * Constr.t option list option)

let start_mutual_with_initialization ~info ~cinfo ~mutual_info sigma snl =
  let intro_tac { CInfo.args; _ } = Tactics.auto_intros_tac args in
  let init_tac, compute_guard =
    let (finite,guard,init_terms) = mutual_info in
    let rec_tac = rec_tac_initializer finite guard cinfo snl in
    let term_tac =
      match init_terms with
      | None ->
        List.map intro_tac cinfo
      | Some init_terms ->
        (* This is the case for hybrid proof mode / definition
           fixpoint, where terms for some constants are given with := *)
        let tacl = List.map (Option.cata (EConstr.of_constr %> Tactics.exact_no_check) Tacticals.New.tclIDTAC) init_terms in
        List.map2 (fun tac thm -> Tacticals.New.tclTHEN tac (intro_tac thm)) tacl cinfo
    in
    Tacticals.New.tclTHENS rec_tac term_tac, guard
  in
  match cinfo with
  | [] -> CErrors.anomaly (Pp.str "No proof to start.")
  | { CInfo.name; typ; _} :: thms ->
    let pinfo = Proof_info.make ~cinfo ~info ~compute_guard () in
    (* start_lemma has the responsibility to add (name, impargs, typ)
       to thms, once Info.t is more refined this won't be necessary *)
    let typ = EConstr.of_constr typ in
    let lemma = start_proof_core ~name ~typ ~pinfo sigma in
    map lemma ~f:(fun p ->
        pi1 @@ Proof.run_tactic Global.(env ()) init_tac p)

let get_used_variables pf = pf.section_vars
let get_universe_decl pf = pf.pinfo.Proof_info.info.Info.udecl

let set_used_variables ps l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let ids = List.fold_right Id.Set.add l Id.Set.empty in
  let ctx = Environ.keep_hyps env ids in
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
  if not (Option.is_empty ps.section_vars) then
    CErrors.user_err Pp.(str "Used section variables can be declared only once");
  ctx, { ps with section_vars = Some (Context.Named.to_vars ctx) }

let get_open_goals ps =
  let Proof.{ goals; stack; shelf } = Proof.data ps.proof in
  List.length goals +
  List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) stack) +
  List.length shelf

type proof_object =
  { name : Names.Id.t
  (* [name] only used in the STM *)
  ; entries : Evd.side_effects proof_entry list
  ; uctx: UState.t
  }

let get_po_name { name } = name

let private_poly_univs =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Private";"Polymorphic";"Universes"]
    ~value:true

(* XXX: This is still separate from close_proof below due to drop_pt in the STM *)
(* XXX: Unsafe_typ:true is needed by vio files, see bf0499bc507d5a39c3d5e3bf1f69191339270729 *)
let prepare_proof ~unsafe_typ { proof } =
  let Proof.{name=pid;entry;poly} = Proof.data proof in
  let initial_goals = Proofview.initial_goals entry in
  let evd = Proof.return ~pid proof in
  let eff = Evd.eval_side_effects evd in
  let evd = Evd.minimize_universes evd in
  let to_constr_body c =
    match EConstr.to_constr_opt evd c with
    | Some p ->
      Vars.universes_of_constr p, p
    | None ->
      CErrors.user_err Pp.(str "Some unresolved existential variables remain")
  in
  let to_constr_typ t =
    if unsafe_typ
    then
      let t = EConstr.Unsafe.to_constr t in
      Vars.universes_of_constr t, t
    else to_constr_body t
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
  let proofs = List.map (fun (body, typ) -> (to_constr_body body, eff), to_constr_typ typ) initial_goals in
  proofs, Evd.evar_universe_context evd

let make_univs_deferred ~poly ~initial_euctx ~uctx ~udecl
    (used_univs_typ, typ) (used_univs_body, body) =
  let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
  let utyp = UState.univ_entry ~poly initial_euctx in
  let uctx = UState.constrain_variables (fst (UState.context_set initial_euctx)) uctx in
  (* For vi2vo compilation proofs are computed now but we need to
     complement the univ constraints of the typ with the ones of
     the body.  So we keep the two sets distinct. *)
  let uctx_body = UState.restrict uctx used_univs in
  let ubody = UState.check_mono_univ_decl uctx_body udecl in
  utyp, ubody

let make_univs_private_poly ~poly ~uctx ~udecl (used_univs_typ, typ) (used_univs_body, body) =
  let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
  let universes = UState.restrict uctx used_univs in
  let typus = UState.restrict universes used_univs_typ in
  let utyp = UState.check_univ_decl ~poly typus udecl in
  let ubody = Univ.ContextSet.diff
      (UState.context_set universes)
      (UState.context_set typus)
  in
  utyp, ubody

let make_univs ~poly ~uctx ~udecl (used_univs_typ, typ) (used_univs_body, body) =
  let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
  (* Since the proof is computed now, we can simply have 1 set of
     constraints in which we merge the ones for the body and the ones
     for the typ. We recheck the declaration after restricting with
     the actually used universes.
     TODO: check if restrict is really necessary now. *)
  let ctx = UState.restrict uctx used_univs in
  let utyp = UState.check_univ_decl ~poly ctx udecl in
  utyp, Univ.ContextSet.empty

let close_proof ~opaque ~keep_body_ucst_separate ps =

  let { section_vars; proof; initial_euctx; pinfo } = ps in
  let { Proof_info.info = { Info.udecl } } = pinfo in
  let { Proof.name; poly } = Proof.data proof in
  let unsafe_typ = keep_body_ucst_separate && not poly in
  let elist, uctx = prepare_proof ~unsafe_typ ps in
  let opaque = match opaque with
    | Vernacexpr.Opaque -> true
    | Vernacexpr.Transparent -> false in

  let make_entry ((((_ub, body) as b), eff), ((_ut, typ) as t)) =
    let utyp, ubody =
      (* allow_deferred case *)
      if not poly &&
         (keep_body_ucst_separate
          || not (Safe_typing.is_empty_private_constants eff.Evd.seff_private))
      then make_univs_deferred ~initial_euctx ~poly ~uctx ~udecl t b
      (* private_poly_univs case *)
      else if poly && opaque && private_poly_univs ()
      then make_univs_private_poly ~poly ~uctx ~udecl t b
      else make_univs ~poly ~uctx ~udecl t b
    in
    definition_entry_core ~opaque ?section_vars ~univs:utyp ~univsbody:ubody ~types:typ ~eff body
  in
  let entries = CList.map make_entry elist  in
  { name; entries; uctx }

type closed_proof_output = (Constr.t * Evd.side_effects) list * UState.t

let close_proof_delayed ~feedback_id ps (fpl : closed_proof_output Future.computation) =
  let { section_vars; proof; initial_euctx; pinfo } = ps in
  let { Proof_info.info = { Info.udecl } } = pinfo in
  let { Proof.name; poly; entry; sigma } = Proof.data proof in

  (* We don't allow poly = true in this path *)
  if poly then
    CErrors.anomaly (Pp.str "Cannot delay universe-polymorphic constants.");

  let fpl, uctx = Future.split2 fpl in
  (* Because of dependent subgoals at the beginning of proofs, we could
     have existential variables in the initial types of goals, we need to
     normalise them for the kernel. *)
  let subst_evar k = Evd.existential_opt_value0 sigma k in
  let nf = UnivSubst.nf_evars_and_universes_opt_subst subst_evar (UState.subst initial_euctx) in

  (* We only support opaque proofs, this will be enforced by using
     different entries soon *)
  let opaque = true in
  let make_entry p (_, types) =
    (* Already checked the univ_decl for the type universes when starting the proof. *)
    let univs = UState.univ_entry ~poly:false initial_euctx in
    let types = nf (EConstr.Unsafe.to_constr types) in

    Future.chain p (fun (pt,eff) ->
        (* Deferred proof, we already checked the universe declaration with
             the initial universes, ensure that the final universes respect
             the declaration as well. If the declaration is non-extensible,
             this will prevent the body from adding universes and constraints. *)
        let uctx = Future.force uctx in
        let uctx = UState.constrain_variables (fst (UState.context_set initial_euctx)) uctx in
        let used_univs = Univ.LSet.union
            (Vars.universes_of_constr types)
            (Vars.universes_of_constr pt)
        in
        let univs = UState.restrict uctx used_univs in
        let univs = UState.check_mono_univ_decl univs udecl in
        (pt,univs),eff)
    |> delayed_definition_entry ~opaque ~feedback_id ~section_vars ~univs ~types
  in
  let entries = Future.map2 make_entry fpl (Proofview.initial_goals entry) in
  { name; entries; uctx = initial_euctx }

let close_future_proof = close_proof_delayed

let return_partial_proof { proof } =
 let proofs = Proof.partial_proof proof in
 let Proof.{sigma=evd} = Proof.data proof in
 let eff = Evd.eval_side_effects evd in
 (* ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
     side-effects... This may explain why one need to uniquize side-effects
     thereafter... *)
 let proofs = List.map (fun c -> EConstr.Unsafe.to_constr c, eff) proofs in
 proofs, Evd.evar_universe_context evd

let return_proof ps =
  let p, uctx = prepare_proof ~unsafe_typ:false ps in
  List.map (fun (((_ub, body),eff),_) -> (body,eff)) p, uctx

let update_global_env =
  map ~f:(fun p ->
      let { Proof.sigma } = Proof.data p in
      let tac = Proofview.Unsafe.tclEVARS (Evd.update_sigma_env sigma (Global.env ())) in
      let p, (status,info), _ = Proof.run_tactic (Global.env ()) tac p in
      p)

let next = let n = ref 0 in fun () -> incr n; !n

let by tac = map_fold ~f:(Proof.solve (Goal_select.SelectNth 1) None tac)

let build_constant_by_tactic ~name ?(opaque=Vernacexpr.Transparent) ~uctx ~sign ~poly (typ : EConstr.t) tac =
  let evd = Evd.from_ctx uctx in
  let typ_ = EConstr.Unsafe.to_constr typ in
  let cinfo = [CInfo.make ~name ~typ:typ_ ()] in
  let info = Info.make ~poly () in
  let pinfo = Proof_info.make ~cinfo ~info () in
  let pf = start_proof_core ~name ~typ ~pinfo ~sign evd in
  let pf, status = by tac pf in
  let { entries; uctx } = close_proof ~opaque ~keep_body_ucst_separate:false pf in
  match entries with
  | [entry] ->
    entry, status, uctx
  | _ ->
    CErrors.anomaly Pp.(str "[build_constant_by_tactic] close_proof returned more than one proof term")

let build_by_tactic ?(side_eff=true) env ~uctx ~poly ~typ tac =
  let name = Id.of_string ("temporary_proof"^string_of_int (next())) in
  let sign = Environ.(val_of_named_context (named_context env)) in
  let ce, status, uctx = build_constant_by_tactic ~name ~uctx ~sign ~poly typ tac in
  let cb, uctx =
    if side_eff then inline_private_constants ~uctx env ce
    else
      (* GG: side effects won't get reset: no need to treat their universes specially *)
      let (cb, ctx), _eff = Future.force ce.proof_entry_body in
      cb, UState.merge ~sideff:false Evd.univ_rigid uctx ctx
  in
  cb, ce.proof_entry_type, ce.proof_entry_universes, status, uctx

let declare_abstract ~name ~poly ~kind ~sign ~secsign ~opaque ~solve_tac sigma concl =
  (* EJGA: flush_and_check_evars is only used in abstract, could we
     use a different API? *)
  let concl =
    try Evarutil.flush_and_check_evars sigma concl
    with Evarutil.Uninstantiated_evar _ ->
      CErrors.user_err Pp.(str "\"abstract\" cannot handle existentials.")
  in
  let sigma, concl =
    (* FIXME: should be done only if the tactic succeeds *)
    let sigma = Evd.minimize_universes sigma in
    sigma, Evarutil.nf_evars_universes sigma concl
  in
  let concl = EConstr.of_constr concl in
  let uctx = Evd.evar_universe_context sigma in
  let (const, safe, uctx) =
    try build_constant_by_tactic ~name ~opaque:Vernacexpr.Transparent ~poly ~uctx ~sign:secsign concl solve_tac
    with Logic_monad.TacticFailure e as src ->
    (* if the tactic [tac] fails, it reports a [TacticFailure e],
       which is an error irrelevant to the proof system (in fact it
       means that [e] comes from [tac] failing to yield enough
       success). Hence it reraises [e]. *)
    let (_, info) = Exninfo.capture src in
    Exninfo.iraise (e, info)
  in
  let sigma = Evd.set_universe_context sigma uctx in
  let body, effs = Future.force const.proof_entry_body in
  (* We drop the side-effects from the entry, they already exist in the ambient environment *)
  let const = Internal.map_entry_body const ~f:(fun _ -> body, ()) in
  (* EJGA: Hack related to the above call to
     `build_constant_by_tactic` with `~opaque:Transparent`. Even if
     the abstracted term is destined to be opaque, if we trigger the
     `if poly && opaque && private_poly_univs ()` in `close_proof`
     kernel will boom. This deserves more investigation. *)
  let const = Internal.set_opacity ~opaque const in
  let const, args = Internal.shrink_entry sign const in
  let cst () =
    (* do not compute the implicit arguments, it may be costly *)
    let () = Impargs.make_implicit_args false in
    (* ppedrot: seems legit to have abstracted subproofs as local*)
    declare_private_constant ~local:Locality.ImportNeedQualified ~name ~kind const
  in
  let cst, eff = Impargs.with_implicit_protection cst () in
  let inst = match const.proof_entry_universes with
  | Entries.Monomorphic_entry _ -> EConstr.EInstance.empty
  | Entries.Polymorphic_entry (_, ctx) ->
    (* We mimic what the kernel does, that is ensuring that no additional
       constraints appear in the body of polymorphic constants. Ideally this
       should be enforced statically. *)
    let (_, body_uctx), _ = Future.force const.proof_entry_body in
    let () = assert (Univ.ContextSet.is_empty body_uctx) in
    EConstr.EInstance.make (Univ.UContext.instance ctx)
  in
  let args = List.map EConstr.of_constr args in
  let lem = EConstr.mkConstU (cst, inst) in
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

(* Support for mutually proved theorems *)

(* XXX: this should be unified with the code for non-interactive
   mutuals previously on this file. *)
module MutualEntry : sig

  val declare_variable
    : pinfo:Proof_info.t
    -> uctx:UState.t
    -> Entries.parameter_entry
    -> Names.GlobRef.t list

  val declare_mutdef
    (* Common to all recthms *)
    : pinfo:Proof_info.t
    -> uctx:UState.t
    -> entry:Evd.side_effects proof_entry
    -> Names.GlobRef.t list

end = struct

  (* XXX: Refactor this with the code in [Declare.declare_mutdef] *)
  let guess_decreasing env possible_indexes ((body, ctx), eff) =
    let open Constr in
    match Constr.kind body with
    | Fix ((nv,0),(_,_,fixdefs as fixdecls)) ->
      let env = Safe_typing.push_private_constants env eff.Evd.seff_private in
      let indexes = Pretyping.search_guard env possible_indexes fixdecls in
      (mkFix ((indexes,0),fixdecls), ctx), eff
    | _ -> (body, ctx), eff

  let select_body i t =
    let open Constr in
    match Constr.kind t with
    | Fix ((nv,0),decls) -> mkFix ((nv,i),decls)
    | CoFix (0,decls) -> mkCoFix (i,decls)
    | _ ->
      CErrors.anomaly
        Pp.(str "Not a proof by induction: " ++
            Termops.Internal.debug_print_constr (EConstr.of_constr t) ++ str ".")

  let declare_mutdef ~uctx ~pinfo pe i CInfo.{ name; impargs; typ; _} =
    let { Proof_info.info; compute_guard; _ } = pinfo in
    let { Info.hook; scope; kind; _ } = info in
    (* if i = 0 , we don't touch the type; this is for compat
       but not clear it is the right thing to do.
    *)
    let pe, ubind =
      if i > 0 && not (CList.is_empty compute_guard)
      then Internal.map_entry_type pe ~f:(fun _ -> Some typ), UnivNames.empty_binders
      else pe, UState.universe_binders uctx
    in
    (* We when compute_guard was [] in the previous step we should not
       substitute the body *)
    let pe = match compute_guard with
      | [] -> pe
      | _ ->
        Internal.map_entry_body pe
          ~f:(fun ((body, ctx), eff) -> (select_body i body, ctx), eff)
    in
    declare_entry ~name ~scope ~kind ?hook ~impargs ~uctx pe

  let declare_mutdef ~pinfo ~uctx ~entry =
    let pe = match pinfo.Proof_info.compute_guard with
    | [] ->
      (* Not a recursive statement *)
      entry
    | possible_indexes ->
      (* Try all combinations... not optimal *)
      let env = Global.env() in
      Internal.map_entry_body entry
        ~f:(guess_decreasing env possible_indexes)
    in
    List.map_i (declare_mutdef ~pinfo ~uctx pe) 0 pinfo.Proof_info.cinfo

  let declare_variable ~pinfo ~uctx pe =
    let { Info.scope; hook } = pinfo.Proof_info.info in
    List.map_i (
      fun i { CInfo.name; typ; impargs } ->
        declare_assumption ~name ~scope ~hook ~impargs ~uctx pe
    ) 0 pinfo.Proof_info.cinfo

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
  else match get_used_variables proof, pproofs with
    | Some _ as x, _ -> x
    | None, pproof :: _ ->
      let env = Global.env () in
      let ids_typ = Environ.global_vars_set env typ in
      (* [pproof] is evar-normalized by [partial_proof]. We don't
         count variables appearing only in the type of evars. *)
      let ids_def = Environ.global_vars_set env (EConstr.Unsafe.to_constr pproof) in
      Some (Environ.really_needed env (Id.Set.union ids_typ ids_def))
    | _ -> None

let finish_admitted ~pm ~pinfo ~uctx pe =
  let cst = MutualEntry.declare_variable ~pinfo ~uctx pe in
  (* If the constant was an obligation we need to update the program map *)
  match CEphemeron.get pinfo.Proof_info.proof_ending with
  | Proof_ending.End_obligation oinfo ->
    Obls_.obligation_admitted_terminator ~pm oinfo uctx (List.hd cst)
  | _ -> pm

let save_admitted ~pm ~proof =
  let udecl = get_universe_decl proof in
  let Proof.{ poly; entry } = Proof.data (get proof) in
  let typ = match Proofview.initial_goals entry with
    | [typ] -> snd typ
    | _ -> CErrors.anomaly ~label:"Lemmas.save_lemma_admitted" (Pp.str "more than one statement.")
  in
  let typ = EConstr.Unsafe.to_constr typ in
  let iproof = get proof in
  let pproofs = Proof.partial_proof iproof in
  let sec_vars = compute_proof_using_for_admitted proof typ pproofs in
  let uctx = get_initial_euctx proof in
  let univs = UState.check_univ_decl ~poly uctx udecl in
  finish_admitted ~pm ~pinfo:proof.pinfo ~uctx (sec_vars, (typ, univs), None)

(************************************************************************)
(* Saving a lemma-like constant                                         *)
(************************************************************************)

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
  let f_def = Internal.set_opacity ~opaque:false f_def in
  let f_kind = Decls.(IsDefinition Definition) in
  let f_def = DefinitionEntry f_def in
  let f_kn = declare_constant ~name:f ~kind:f_kind f_def in
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
    | None -> assert false (* Declare always sets type here. *)
  in
  (* The references of [f] are subsituted appropriately. *)
  let lemma_def = Internal.map_entry_type lemma_def ~f:lemma_pretype in
  (* The same is done in the body of the proof. *)
  let lemma_def = Internal.map_entry_body lemma_def ~f:(fun ((b,ctx),fx) -> (substf b, ctx), fx) in
  let lemma_def = DefinitionEntry lemma_def in
  let ct = declare_constant ~name ~kind:Decls.(IsProof Proposition) lemma_def in
  [GlobRef.ConstRef ct]

let finish_proved_equations ~pm ~kind ~hook i proof_obj types sigma0 =

  let obls = ref 1 in
  let sigma, recobls =
    CList.fold_left2_map (fun sigma (_evar_env, ev, _evi, local_context, _type) entry ->
        let id =
          match Evd.evar_ident ev sigma0 with
          | Some id -> id
          | None -> let n = !obls in incr obls; Nameops.add_suffix i ("_obligation_" ^ string_of_int n)
        in
        let entry, args = Internal.shrink_entry local_context entry in
        let cst = declare_constant ~name:id ~kind (DefinitionEntry entry) in
        let sigma, app = Evarutil.new_global sigma (GlobRef.ConstRef cst) in
        let sigma = Evd.define ev (EConstr.applist (app, List.map EConstr.of_constr args)) sigma in
        sigma, cst) sigma0
      types proof_obj.entries
  in
  let pm = hook ~pm recobls sigma in
  pm, List.map (fun cst -> GlobRef.ConstRef cst) recobls

let check_single_entry { entries; uctx } label =
  match entries with
  | [entry] -> entry, uctx
  | _ ->
    CErrors.anomaly ~label Pp.(str "close_proof returned more than one proof term")

let finalize_proof ~pm proof_obj proof_info =
  let open Proof_ending in
  match CEphemeron.default proof_info.Proof_info.proof_ending Regular with
  | Regular ->
    let entry, uctx = check_single_entry proof_obj "Proof.save" in
    pm, MutualEntry.declare_mutdef ~entry ~uctx ~pinfo:proof_info
  | End_obligation oinfo ->
    let entry, uctx = check_single_entry proof_obj "Obligation.save" in
    Obls_.obligation_terminator ~pm ~entry ~uctx ~oinfo
  | End_derive { f ; name } ->
    pm, finish_derived ~f ~name ~entries:proof_obj.entries
  | End_equations { hook; i; types; sigma } ->
    let kind = proof_info.Proof_info.info.Info.kind in
    finish_proved_equations ~pm ~kind ~hook i proof_obj types sigma

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
  finalize_proof ~pm proof_obj proof_info

let save_regular ~proof ~opaque ~idopt =
  let open Proof_ending in
  match CEphemeron.default proof.pinfo.Proof_info.proof_ending Regular with
  | Regular ->
    let (_, grs) : Obls_.State.t * _ = save ~pm:Obls_.State.empty ~proof ~opaque ~idopt in
    grs
  | _ -> CErrors.anomaly Pp.(str "save_regular: unexpected proof ending")

(***********************************************************************)
(* Special case to close a lemma without forcing a proof               *)
(***********************************************************************)
let save_lemma_admitted_delayed ~pm ~proof ~pinfo =
  let { entries; uctx } = proof in
  if List.length entries <> 1 then
    CErrors.user_err Pp.(str "Admitted does not support multiple statements");
  let { proof_entry_secctx; proof_entry_type; proof_entry_universes } = List.hd entries in
  let poly = match proof_entry_universes with
    | Entries.Monomorphic_entry _ -> false
    | Entries.Polymorphic_entry (_, _) -> true in
  let typ = match proof_entry_type with
    | None -> CErrors.user_err Pp.(str "Admitted requires an explicit statement");
    | Some typ -> typ in
  let ctx = UState.univ_entry ~poly uctx in
  let sec_vars = if get_keep_admitted_vars () then proof_entry_secctx else None in
  finish_admitted ~pm ~uctx ~pinfo (sec_vars, (typ, ctx), None)

let save_lemma_proved_delayed ~pm ~proof ~pinfo ~idopt =
  (* vio2vo calls this but with invalid info, we have to workaround
     that to add the name to the info structure *)
  if CList.is_empty pinfo.Proof_info.cinfo then
    let name = get_po_name proof in
    let info = Proof_info.add_first_thm ~pinfo ~name ~typ:EConstr.mkSet ~impargs:[] in
    finalize_proof ~pm proof info
  else
    let info = process_idopt_for_save ~idopt pinfo in
    finalize_proof ~pm proof info

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
  EConstr.Unsafe.to_constr (Reductionops.clos_norm_flags CClosure.betaiota env sigma (EConstr.of_constr c))

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
    CErrors.user_err
      ( str "Obligation" ++ spc () ++ int num ++ str "already" ++ spc ()
        ++ str "solved." )

  let depends num rem =
    CErrors.user_err
      ( str "Obligation " ++ int num
        ++ str " depends on obligation(s) "
        ++ pr_sequence (fun x -> int (succ x)) rem)

end

let default_tactic = ref (Proofview.tclUNIT ())

let evar_of_obligation o = Evd.make_evar (Global.named_context_val ()) (EConstr.of_constr o.obl_type)

let subst_deps expand obls deps t =
  let osubst = Obls_.obl_substitution expand obls deps in
    (Vars.replace_vars (List.map (fun (n, (_, b)) -> n, b) osubst) t)

let subst_deps_obl obls obl =
  let t' = subst_deps true obls obl.obl_deps obl.obl_type in
  Obligation.set_type ~typ:t' obl

open Evd

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
  CWarnings.create ~name:"solve_obligation_error" ~category:"tactics"
    (fun err ->
      Pp.seq
        [ str "Solve Obligations tactic returned error: "
        ; err
        ; fnl ()
        ; str "This will become an error in the future" ])

let solve_by_tac ?loc name evi t ~poly ~uctx =
  (* the status is dropped. *)
  try
    let env = Global.env () in
    let body, types, _univs, _, uctx =
      build_by_tactic env ~uctx ~poly ~typ:evi.evar_concl t in
    Inductiveops.control_only_guard env (Evd.from_ctx uctx) (EConstr.of_constr body);
    Some (body, types, uctx)
  with
  | Tacticals.FailError (_, s) as exn ->
    let _ = Exninfo.capture exn in
    CErrors.user_err ?loc ~hdr:"solve_obligation" (Lazy.force s)
  (* If the proof is open we absorb the error and leave the obligation open *)
  | Proof_.OpenProof _ ->
    None
  | e when CErrors.noncritical e ->
    let err = CErrors.print e in
    warn_solve_errored ?loc err;
    None

let get_unique_prog ~pm prg =
  match State.get_unique_open_prog pm prg with
  | Ok prg -> prg
  | Error [] ->
    Error.no_obligations None
  | Error ((id :: _) as ids) ->
    Error.ambiguous_program id ids

let rec solve_obligation prg num tac =
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
  let scope = Locality.Global Locality.ImportNeedQualified in
  let kind = kind_of_obligation (snd obl.obl_status) in
  let evd = Evd.from_ctx (Internal.get_uctx prg) in
  let evd = Evd.update_sigma_env evd (Global.env ()) in
  let auto ~pm n oblset tac = auto_solve_obligations ~pm n ~oblset tac in
  let proof_ending =
    let name = Internal.get_name prg in
    Proof_ending.End_obligation {name; num; auto}
  in
  let cinfo = CInfo.make ~name:obl.obl_name ~typ:(EConstr.of_constr obl.obl_type) () in
  let poly = Internal.get_poly prg in
  let info = Info.make ~scope ~kind ~poly () in
  let lemma = Proof.start_core ~cinfo ~info ~proof_ending evd  in
  let lemma = fst @@ Proof.by !default_tactic lemma in
  let lemma = Option.cata (fun tac -> Proof.set_endline_tactic tac lemma) lemma tac in
  lemma

and obligation (user_num, name, typ) ~pm tac =
  let num = pred user_num in
  let prg = get_unique_prog ~pm name in
  let { obls; remaining } = Internal.get_obligations prg in
  if num >= 0 && num < Array.length obls then
    let obl = obls.(num) in
    match obl.obl_body with
    | None -> solve_obligation prg num tac
    | Some r -> Error.already_solved num
  else Error.unknown_obligation num

and solve_obligation_by_tac prg obls i tac =
  let obl = obls.(i) in
    match obl.obl_body with
    | Some _ -> None
    | None ->
      if List.is_empty (deps_remaining obls obl.obl_deps) then
        let obl = subst_deps_obl obls obl in
        let tac =
          match tac with
          | Some t -> t
          | None ->
            match obl.obl_tac with
            | Some t -> t
            | None -> !default_tactic
        in
        let uctx = Internal.get_uctx prg in
        let uctx = UState.update_sigma_env uctx (Global.env ()) in
        let poly = Internal.get_poly prg in
        match solve_by_tac ?loc:(fst obl.obl_location) obl.obl_name (evar_of_obligation obl) tac ~poly ~uctx with
        | None -> None
        | Some (t, ty, uctx) ->
          let prg = ProgramDecl.Internal.set_uctx ~uctx prg in
          let def, obl', _cst = declare_obligation prg obl ~body:t ~types:ty ~uctx in
          obls.(i) <- obl';
          if def && not poly then (
            (* Declare the term constraints with the first obligation only *)
            let uctx_global = UState.from_env (Global.env ()) in
            let uctx = UState.merge_subst uctx_global (UState.subst uctx) in
            Some (ProgramDecl.Internal.set_uctx ~uctx prg))
          else Some prg
      else None

and solve_prg_obligations ~pm prg ?oblset tac =
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

and solve_obligations ~pm n tac =
  let prg = get_unique_prog ~pm n in
  solve_prg_obligations ~pm prg tac

and solve_all_obligations ~pm tac =
  State.fold pm ~init:pm ~f:(fun k v pm ->
      solve_prg_obligations ~pm v tac |> fst)

and try_solve_obligation ~pm n prg tac =
  let prg = get_unique_prog ~pm prg in
  let {obls; remaining} = Internal.get_obligations prg in
  let obls' = Array.copy obls in
  match solve_obligation_by_tac prg obls' n tac with
  | Some prg' ->
    let pm, _ = update_obls ~pm prg' obls' (pred remaining) in
    pm
  | None -> pm

and try_solve_obligations ~pm n tac =
  solve_obligations ~pm n tac |> fst

and auto_solve_obligations ~pm n ?oblset tac : State.t * progress =
  Flags.if_verbose Feedback.msg_info
    (str "Solving obligations automatically...");
  let prg = get_unique_prog ~pm n in
  solve_prg_obligations ~pm prg ?oblset tac

let show_single_obligation i n obls x =
  let x = subst_deps_obl obls x in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let msg =
    str "Obligation" ++ spc ()
    ++ int (succ i)
    ++ spc () ++ str "of" ++ spc () ++ Id.print n ++ str ":" ++ spc ()
    ++ hov 1 (Printer.pr_constr_env env sigma x.obl_type
              ++ str "." ++ fnl ()) in
  Feedback.msg_info msg

let show_obligations_of_prg ?(msg = true) prg =
  let n = Internal.get_name prg in
  let {obls; remaining} = Internal.get_obligations prg in
  let showed = ref 5 in
    if msg then Feedback.msg_info (int remaining ++ str " obligation(s) remaining: ");
    Array.iteri
      (fun i x ->
         match x.obl_body with
         | None ->
           if !showed > 0 then begin
             decr showed;
             show_single_obligation i n obls x
           end
         | Some _ -> ())
      obls

let show_obligations ~pm ?(msg = true) n =
  let progs =
    match n with
    | None ->
      State.all pm
    | Some n ->
      (match State.find pm n with
       | Some prg -> [prg]
       | None -> Error.no_obligations (Some n))
  in
  List.iter (fun x -> show_obligations_of_prg ~msg x) progs

let show_term ~pm n =
  let prg = get_unique_prog ~pm n in
  ProgramDecl.show prg

let msg_generating_obl name obls =
  let len = Array.length obls in
  let info = Id.print name ++ str " has type-checked" in
  Feedback.msg_info
    (if len = 0 then info ++ str "."
     else
       info ++ str ", generating " ++ int len ++
       str (String.plural len " obligation"))

let add_definition ~pm ~cinfo ~info ?obl_hook ?term ~uctx
    ?tactic ?(reduce = reduce) ?(opaque = false) obls =
  let prg =
    ProgramDecl.make ~info ~cinfo ~body:term ~opaque ~uctx ~reduce ~ntns:[] ~deps:[] ~fixpoint_kind:None ?obl_hook obls
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

let add_mutual_definitions l ~pm ~info ?obl_hook ~uctx
    ?tactic ?(reduce = reduce) ?(opaque = false) ~ntns fixkind =
  let deps = List.map (fun (ci,_,_) -> CInfo.get_name ci) l in
  let pm =
    List.fold_left
      (fun pm (cinfo, b, obls) ->
        let prg =
          ProgramDecl.make ~info ~cinfo ~opaque ~body:(Some b) ~uctx ~deps
            ~fixpoint_kind:(Some fixkind) ~ntns ~reduce ?obl_hook obls
        in
        State.add pm (CInfo.get_name cinfo) prg)
      pm l
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

let admit_prog ~pm prg =
  let {obls; remaining} = Internal.get_obligations prg in
  let obls = Array.copy obls in
    Array.iteri
      (fun i x ->
        match x.obl_body with
        | None ->
            let x = subst_deps_obl obls x in
            let uctx = Internal.get_uctx prg in
            let univs = UState.univ_entry ~poly:false uctx in
            let kn = declare_constant ~name:x.obl_name ~local:Locality.ImportNeedQualified
              (ParameterEntry (None, (x.obl_type, univs), None)) ~kind:Decls.(IsAssumption Conjectural)
            in
              assumption_message x.obl_name;
              obls.(i) <- Obligation.set_body ~body:(DefinedObl (kn, Univ.Instance.empty)) x
        | Some _ -> ())
      obls;
  Obls_.update_obls ~pm prg obls 0

(* get_any_prog *)
let rec admit_all_obligations ~pm =
  let prg = State.first_pending pm in
  match prg with
  | None -> pm
  | Some prg ->
    let pm, _prog = admit_prog ~pm prg in
    admit_all_obligations ~pm

let admit_obligations ~pm n =
  match n with
  | None -> admit_all_obligations ~pm
  | Some _ ->
    let prg = get_unique_prog ~pm n in
    let pm, _ = admit_prog ~pm prg in
    pm

let next_obligation ~pm n tac =
  let prg = match n with
    | None -> State.first_pending pm |> Option.get
    | Some _ -> get_unique_prog ~pm n
  in
  let {obls; remaining} = Internal.get_obligations prg in
  let is_open _ x = Option.is_empty x.obl_body && List.is_empty (deps_remaining obls x.obl_deps) in
  let i = match Array.findi is_open obls with
    | Some i -> i
    | None -> CErrors.anomaly (Pp.str "Could not find a solvable obligation.")
  in
  solve_obligation prg i tac

let check_program_libraries () =
  Coqlib.check_required_library Coqlib.datatypes_module_name;
  Coqlib.check_required_library ["Coq";"Init";"Specif"];
  Coqlib.check_required_library ["Coq";"Program";"Tactics"]

(* aliases *)
let prepare_obligation = prepare_obligation
let check_solved_obligations = Obls_.check_solved_obligations
type fixpoint_kind = Obls_.fixpoint_kind =
  | IsFixpoint of lident option list | IsCoFixpoint
type nonrec progress = progress =
  | Remain of int | Dependent | Defined of GlobRef.t

end

module OblState = Obls_.State
