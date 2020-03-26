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
open Declarations
open Entries
open Safe_typing
open Libobject
open Lib

(* object_kind , id *)
exception AlreadyDeclared of (string option * Id.t)

let _ = CErrors.register_handler (function
    | AlreadyDeclared (kind, id) ->
      Some
        (seq [ Pp.pr_opt_no_spc (fun s -> str s ++ spc ()) kind
             ; Id.print id; str " already exists."])
    | _ ->
      None)

module NamedDecl = Context.Named.Declaration

type import_status = ImportDefaultBehavior | ImportNeedQualified

(** Monomorphic universes need to survive sections. *)

let name_instance inst =
  let map lvl = match Univ.Level.name lvl with
    | None -> (* Having Prop/Set/Var as section universes makes no sense *)
      assert false
    | Some na ->
      try
        let qid = Nametab.shortest_qualid_of_universe na in
        Name (Libnames.qualid_basename qid)
      with Not_found ->
        (* Best-effort naming from the string representation of the level.
           See univNames.ml for a similar hack. *)
        Name (Id.of_string_soft (Univ.Level.to_string lvl))
  in
  Array.map map (Univ.Instance.to_array inst)

let declare_universe_context ~poly ctx =
  if poly then
    let uctx = Univ.ContextSet.to_context ctx in
    let nas = name_instance (Univ.UContext.instance uctx) in
    Global.push_section_context (nas, uctx)
  else
    Global.push_context_set ~strict:true ctx

(** Declaration of constants and parameters *)

type constant_obj = {
  cst_kind : Decls.logical_kind;
  cst_locl : import_status;
}

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

type 'a constant_entry =
  | DefinitionEntry of 'a proof_entry
  | ParameterEntry of parameter_entry
  | PrimitiveEntry of primitive_entry

(* At load-time, the segment starting from the module name to the discharge *)
(* section (if Remark or Fact) is needed to access a construction *)
let load_constant i ((sp,kn), obj) =
  if Nametab.exists_cci sp then
    raise (AlreadyDeclared (None, Libnames.basename sp));
  let con = Global.constant_of_delta_kn kn in
  Nametab.push (Nametab.Until i) sp (GlobRef.ConstRef con);
  Dumpglob.add_constant_kind con obj.cst_kind

(* Opening means making the name without its module qualification available *)
let open_constant i ((sp,kn), obj) =
  (* Never open a local definition *)
  match obj.cst_locl with
  | ImportNeedQualified -> ()
  | ImportDefaultBehavior ->
    let con = Global.constant_of_delta_kn kn in
    Nametab.push (Nametab.Exactly i) sp (GlobRef.ConstRef con)

let exists_name id =
  Decls.variable_exists id || Global.exists_objlabel (Label.of_id id)

let check_exists id =
  if exists_name id then
    raise (AlreadyDeclared (None, id))

let cache_constant ((sp,kn), obj) =
  (* Invariant: the constant must exist in the logical environment, except when
     redefining it when exiting a section. See [discharge_constant]. *)
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

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant cst = {
  cst_kind = cst.cst_kind;
  cst_locl = cst.cst_locl;
}

let classify_constant cst = Substitute (dummy_constant cst)

let (objConstant : constant_obj Libobject.Dyn.tag) =
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
  let _ = add_leaf id o in
  update_tables kn

let register_side_effect (c, role) =
  let () = register_constant c Decls.(IsProof Theorem) ImportDefaultBehavior in
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

let default_univ_entry = Monomorphic_entry Univ.ContextSet.empty

let definition_entry ?fix_exn ?(opaque=false) ?(inline=false) ?feedback_id ?section_vars ?types
    ?(univs=default_univ_entry) ?(eff=Evd.empty_side_effects) ?(univc=Univ.ContextSet.empty) body =
  { proof_entry_body = Future.from_val ?fix_exn ((body,univc), eff);
    proof_entry_secctx = section_vars;
    proof_entry_type = types;
    proof_entry_universes = univs;
    proof_entry_opaque = opaque;
    proof_entry_feedback = feedback_id;
    proof_entry_inline_code = inline}

let pure_definition_entry ?fix_exn ?(opaque=false) ?(inline=false) ?types
    ?(univs=default_univ_entry) body =
  { proof_entry_body = Future.from_val ?fix_exn ((body,Univ.ContextSet.empty), ());
    proof_entry_secctx = None;
    proof_entry_type = types;
    proof_entry_universes = univs;
    proof_entry_opaque = opaque;
    proof_entry_feedback = None;
    proof_entry_inline_code = inline}

let delayed_definition_entry ?(opaque=false) ?(inline=false) ?feedback_id ?section_vars ?(univs=default_univ_entry) ?types body =
  { proof_entry_body = body
  ; proof_entry_secctx = section_vars
  ; proof_entry_type = types
  ; proof_entry_universes = univs
  ; proof_entry_opaque = opaque
  ; proof_entry_feedback = feedback_id
  ; proof_entry_inline_code = inline
  }

let cast_proof_entry e =
  let (body, ctx), () = Future.force e.proof_entry_body in
  let univs =
    if Univ.ContextSet.is_empty ctx then e.proof_entry_universes
    else match e.proof_entry_universes with
      | Monomorphic_entry ctx' ->
        (* This can actually happen, try compiling EqdepFacts for instance *)
        Monomorphic_entry (Univ.ContextSet.union ctx' ctx)
      | Polymorphic_entry _ ->
        CErrors.anomaly Pp.(str "Local universes in non-opaque polymorphic definition.");
  in
  {
    const_entry_body = body;
    const_entry_secctx = e.proof_entry_secctx;
    const_entry_feedback = e.proof_entry_feedback;
    const_entry_type = e.proof_entry_type;
    const_entry_universes = univs;
    const_entry_inline_code = e.proof_entry_inline_code;
  }

type ('a, 'b) effect_entry =
| EffectEntry : (private_constants, private_constants Entries.const_entry_body) effect_entry
| PureEntry : (unit, Constr.constr) effect_entry

let cast_opaque_proof_entry (type a b) (entry : (a, b) effect_entry) (e : a proof_entry) : b opaque_entry =
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
    | Monomorphic_entry uctx' -> Monomorphic_entry (Univ.ContextSet.union uctx uctx')
    | Polymorphic_entry _ ->
      assert (Univ.ContextSet.is_empty uctx);
      e.proof_entry_universes
    in
    body, univs
  | EffectEntry -> e.proof_entry_body, e.proof_entry_universes
  in
  {
    opaque_entry_body = body;
    opaque_entry_secctx = secctx;
    opaque_entry_feedback = e.proof_entry_feedback;
    opaque_entry_type = typ;
    opaque_entry_universes = univs;
  }

let feedback_axiom () = Feedback.(feedback AddedAxiom)

let is_unsafe_typing_flags () =
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

let declare_constant ?(local = ImportDefaultBehavior) ~name ~kind cd =
  let () = check_exists name in
  let kn = define_constant ~name cd in
  (* Register the libobjects attached to the constants *)
  let () = register_constant kn kind local in
  kn

let declare_private_constant ?role ?(local = ImportDefaultBehavior) ~name ~kind de =
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
  declare_object_full { (default_object "VARIABLE") with
    classify_function = (fun () -> Dispose)}

let inVariable v = Libobject.Dyn.Easy.inj v objVariable

let declare_variable ~name ~kind d =
  (* Variables are distinguished by only short names *)
  if Decls.variable_exists name then
    raise (AlreadyDeclared (None, name));

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
        | Monomorphic_entry uctx -> false, uctx
        | Polymorphic_entry (_, uctx) -> true, Univ.ContextSet.of_context uctx
      in
      let univs = Univ.ContextSet.union body_ui entry_ui in
      (* We must declare the universe constraints before type-checking the
         term. *)
      let () = declare_universe_context ~poly univs in
      let se = {
        secdef_body = body;
        secdef_secctx = de.proof_entry_secctx;
        secdef_feedback = de.proof_entry_feedback;
        secdef_type = de.proof_entry_type;
      } in
      let () = Global.push_named_def (name, se) in
      Glob_term.Explicit, de.proof_entry_opaque
  in
  Nametab.push (Nametab.Until 1) (Libnames.make_path DirPath.empty name) (GlobRef.VarRef name);
  Decls.(add_variable_data name {opaque;kind});
  ignore(add_leaf name (inVariable ()) : Libobject.object_name);
  Impargs.declare_var_implicits ~impl name;
  Notation.declare_ref_arguments_scope Evd.empty (GlobRef.VarRef name)

(* Declaration messages *)

let pr_rank i = pr_nth (i+1)

let fixpoint_message indexes l =
  Flags.if_verbose Feedback.msg_info (match l with
  | [] -> CErrors.anomaly (Pp.str "no recursive definition.")
  | [id] -> Id.print id ++ str " is recursively defined" ++
      (match indexes with
         | Some [|i|] -> str " (decreasing on "++pr_rank i++str " argument)"
         | _ -> mt ())
  | l -> hov 0 (prlist_with_sep pr_comma Id.print l ++
                  spc () ++ str "are recursively defined" ++
                  match indexes with
                    | Some a -> spc () ++ str "(decreasing respectively on " ++
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

  let get_fix_exn entry = Future.fix_exn_of entry.proof_entry_body

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

  type nonrec constant_obj = constant_obj

  let objVariable = objVariable
  let objConstant = objConstant

end
