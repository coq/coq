(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
      seq [ Pp.pr_opt_no_spc (fun s -> str s ++ spc ()) kind
          ; Id.print id; str " already exists."]
    | _ ->
      raise CErrors.Unhandled)

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
    Global.push_context_set false ctx

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

let (inConstant : constant_obj -> obj) =
  declare_object { (default_object "CONSTANT") with
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    classify_function = classify_constant;
    subst_function = ident_subst_function;
    discharge_function = discharge_constant }

let declare_scheme = ref (fun _ _ -> assert false)
let set_declare_scheme f = declare_scheme := f

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
  | Some (Evd.Schema (ind, kind)) -> !declare_scheme kind [|ind,c|]

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
let definition_entry ?fix_exn ?(opaque=false) ?(inline=false) ?types
    ?(univs=default_univ_entry) ?(eff=Evd.empty_side_effects) body =
  { proof_entry_body = Future.from_val ?fix_exn ((body,Univ.ContextSet.empty), eff);
    proof_entry_secctx = None;
    proof_entry_type = types;
    proof_entry_universes = univs;
    proof_entry_opaque = opaque;
    proof_entry_feedback = None;
    proof_entry_inline_code = inline}

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

type 'a effect_entry =
| EffectEntry : private_constants effect_entry
| PureEntry : unit effect_entry

let cast_opaque_proof_entry (type a) (entry : a effect_entry) (e : a proof_entry) =
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
  {
    opaque_entry_body = e.proof_entry_body;
    opaque_entry_secctx = secctx;
    opaque_entry_feedback = e.proof_entry_feedback;
    opaque_entry_type = typ;
    opaque_entry_universes = e.proof_entry_universes;
  }

let get_roles export eff =
  let map c =
    let role = try Some (Cmap.find c eff.Evd.seff_roles) with Not_found -> None in
    (c, role)
  in
  List.map map export

let feedback_axiom () = Feedback.(feedback AddedAxiom)
let is_unsafe_typing_flags () =
  let flags = Environ.typing_flags (Global.env()) in
  not (flags.check_universes && flags.check_guarded && flags.check_positive)

let define_constant ~name cd =
  (* Logically define the constant and its subproofs, no libobject tampering *)
  let export, decl, unsafe = match cd with
  | DefinitionEntry de ->
    (* We deal with side effects *)
    if not de.proof_entry_opaque then
      (* This globally defines the side-effects in the environment. *)
      let body, eff = Future.force de.proof_entry_body in
      let body, export = Global.export_private_constants (body, eff.Evd.seff_private) in
      let export = get_roles export eff in
      let de = { de with proof_entry_body = Future.from_val (body, ()) } in
      let cd = Entries.DefinitionEntry (cast_proof_entry de) in
      export, ConstantEntry cd, false
    else
      let map (body, eff) = body, eff.Evd.seff_private in
      let body = Future.chain de.proof_entry_body map in
      let de = { de with proof_entry_body = body } in
      let de = cast_opaque_proof_entry EffectEntry de in
      [], OpaqueEntry de, false
  | ParameterEntry e ->
    [], ConstantEntry (Entries.ParameterEntry e), not (Lib.is_modtype_strict())
  | PrimitiveEntry e ->
    [], ConstantEntry (Entries.PrimitiveEntry e), false
  in
  let kn = Global.add_constant name decl in
  if unsafe || is_unsafe_typing_flags() then feedback_axiom();
  kn, export

let declare_constant ?(local = ImportDefaultBehavior) ~name ~kind cd =
  let () = check_exists name in
  let kn, export = define_constant ~name cd in
  (* Register the libobjects attached to the constants and its subproofs *)
  let () = List.iter register_side_effect export in
  let () = register_constant kn kind local in
  kn

let declare_private_constant ?role ?(local = ImportDefaultBehavior) ~name ~kind de =
  let kn, eff =
    let de =
      if not de.proof_entry_opaque then
        let body, () = Future.force de.proof_entry_body in
        let de = { de with proof_entry_body = Future.from_val (body, ()) } in
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

(** Declaration of section variables and local definitions *)
type variable_declaration =
  | SectionLocalDef of Evd.side_effects proof_entry
  | SectionLocalAssum of { typ:Constr.types; impl:Glob_term.binding_kind; }

(* This object is only for things which iterate over objects to find
   variables (only Prettyp.print_context AFAICT) *)
let inVariable : unit -> obj =
  declare_object { (default_object "VARIABLE") with
    classify_function = (fun () -> Dispose)}

let declare_variable ~name ~kind d =
  (* Constr raisonne sur les noms courts *)
  if Decls.variable_exists name then
    raise (AlreadyDeclared (None, name));

  let impl,opaque = match d with (* Fails if not well-typed *)
    | SectionLocalAssum {typ;impl} ->
      let () = Global.push_named_assum (name,typ) in
      impl, true
    | SectionLocalDef (de) ->
      (* The body should already have been forced upstream because it is a
         section-local definition, but it's not enforced by typing *)
      let (body, eff) = Future.force de.proof_entry_body in
      let ((body, uctx), export) = Global.export_private_constants (body, eff.Evd.seff_private) in
      let eff = get_roles export eff in
      let () = List.iter register_side_effect eff in
      let poly, univs = match de.proof_entry_universes with
        | Monomorphic_entry uctx -> false, uctx
        | Polymorphic_entry (_, uctx) -> true, Univ.ContextSet.of_context uctx
      in
      let univs = Univ.ContextSet.union uctx univs in
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

(** Declaration of inductive blocks *)
let declare_inductive_argument_scopes kn mie =
  List.iteri (fun i {mind_entry_consnames=lc} ->
    Notation.declare_ref_arguments_scope Evd.empty (GlobRef.IndRef (kn,i));
    for j=1 to List.length lc do
      Notation.declare_ref_arguments_scope Evd.empty (GlobRef.ConstructRef ((kn,i),j));
    done) mie.mind_entry_inds

type inductive_obj = {
  ind_names : (Id.t * Id.t list) list
  (* For each block, name of the type + name of constructors *)
}

let inductive_names sp kn obj =
  let (dp,_) = Libnames.repr_path sp in
  let kn = Global.mind_of_delta_kn kn in
  let names, _ =
    List.fold_left
      (fun (names, n) (typename, consnames) ->
         let ind_p = (kn,n) in
         let names, _ =
           List.fold_left
             (fun (names, p) l ->
                let sp =
                  Libnames.make_path dp l
                in
                  ((sp, GlobRef.ConstructRef (ind_p,p)) :: names, p+1))
             (names, 1) consnames in
         let sp = Libnames.make_path dp typename
         in
           ((sp, GlobRef.IndRef ind_p) :: names, n+1))
      ([], 0) obj.ind_names
  in names

let load_inductive i ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until i) sp ref ) names

let open_inductive i ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Exactly i) sp ref) names

let cache_inductive ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until 1) sp ref) names

let discharge_inductive ((sp, kn), names) =
  Some names

let inInductive : inductive_obj -> obj =
  declare_object {(default_object "INDUCTIVE") with
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    classify_function = (fun a -> Substitute a);
    subst_function = ident_subst_function;
    discharge_function = discharge_inductive;
  }

let cache_prim (_,(p,c)) = Recordops.register_primitive_projection p c

let load_prim _ p = cache_prim p

let subst_prim (subst,(p,c)) = Mod_subst.subst_proj_repr subst p, Mod_subst.subst_constant subst c

let discharge_prim (_,(p,c)) = Some (Lib.discharge_proj_repr p, c)

let inPrim : (Projection.Repr.t * Constant.t) -> obj =
  declare_object {
    (default_object "PRIMPROJS") with
    cache_function = cache_prim ;
    load_function = load_prim;
    subst_function = subst_prim;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_prim }

let declare_primitive_projection p c = Lib.add_anonymous_leaf (inPrim (p,c))

let declare_one_projection univs (mind,_ as ind) ~proj_npars proj_arg label (term,types) =
  let name = Label.to_id label in
  let univs, u = match univs with
    | Monomorphic_entry _ ->
      (* Global constraints already defined through the inductive *)
      default_univ_entry, Univ.Instance.empty
    | Polymorphic_entry (nas, ctx) ->
      Polymorphic_entry (nas, ctx), Univ.UContext.instance ctx
  in
  let term = Vars.subst_instance_constr u term in
  let types = Vars.subst_instance_constr u types in
  let entry = definition_entry ~types ~univs term in
  let cst = declare_constant ~name ~kind:Decls.(IsDefinition StructureComponent) (DefinitionEntry entry) in
  let p = Projection.Repr.make ind ~proj_npars ~proj_arg label in
  declare_primitive_projection p cst

let declare_projections univs mind =
  let env = Global.env () in
  let mib = Environ.lookup_mind mind env in
  match mib.mind_record with
  | PrimRecord info ->
    let iter_ind i (_, labs, _, _) =
      let ind = (mind, i) in
      let projs = Inductiveops.compute_projections env ind in
      Array.iter2_i (declare_one_projection univs ind ~proj_npars:mib.mind_nparams) labs projs
    in
    let () = Array.iteri iter_ind info in
    true
  | FakeRecord -> false
  | NotRecord -> false

(* for initial declaration *)
let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> CErrors.anomaly (Pp.str "cannot declare an empty list of inductives.") in
  let map_names mip = (mip.mind_entry_typename, mip.mind_entry_consnames) in
  let names = List.map map_names mie.mind_entry_inds in
  List.iter (fun (typ, cons) -> check_exists typ; List.iter check_exists cons) names;
  let _kn' = Global.add_mind id mie in
  let (sp,kn as oname) = add_leaf id (inInductive { ind_names = names }) in
  if is_unsafe_typing_flags() then feedback_axiom();
  let mind = Global.mind_of_delta_kn kn in
  let isprim = declare_projections mie.mind_entry_universes mind in
  Impargs.declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  oname, isprim

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

(** Global universes are not substitutive objects but global objects
   bound at the *library* or *module* level. The polymorphic flag is
   used to distinguish universes declared in polymorphic sections, which
   are discharged and do not remain in scope. *)

type universe_source =
  | BoundUniv (* polymorphic universe, bound in a function (this will go away someday) *)
  | QualifiedUniv of Id.t (* global universe introduced by some global value *)
  | UnqualifiedUniv (* other global universe *)

type universe_name_decl = universe_source * (Id.t * Univ.Level.UGlobal.t) list

let check_exists_universe sp =
  if Nametab.exists_universe sp then
    raise (AlreadyDeclared (Some "Universe", Libnames.basename sp))
  else ()

let qualify_univ i dp src id =
  match src with
  | BoundUniv | UnqualifiedUniv ->
    i,  Libnames.make_path dp id
  | QualifiedUniv l ->
    let dp = DirPath.repr dp in
    Nametab.map_visibility succ i, Libnames.make_path (DirPath.make (l::dp)) id

let do_univ_name ~check i dp src (id,univ) =
  let i, sp = qualify_univ i dp src id in
  if check then check_exists_universe sp;
  Nametab.push_universe i sp univ

let cache_univ_names ((sp, _), (src, univs)) =
  let depth = sections_depth () in
  let dp = Libnames.pop_dirpath_n depth (Libnames.dirpath sp) in
  List.iter (do_univ_name ~check:true (Nametab.Until 1) dp src) univs

let load_univ_names i ((sp, _), (src, univs)) =
  List.iter (do_univ_name ~check:false (Nametab.Until i) (Libnames.dirpath sp) src) univs

let open_univ_names i ((sp, _), (src, univs)) =
  List.iter (do_univ_name ~check:false (Nametab.Exactly i) (Libnames.dirpath sp) src) univs

let discharge_univ_names = function
  | _, (BoundUniv, _) -> None
  | _, ((QualifiedUniv _ | UnqualifiedUniv), _ as x) -> Some x

let input_univ_names : universe_name_decl -> Libobject.obj =
  declare_object
    { (default_object "Global universe name state") with
      cache_function = cache_univ_names;
      load_function = load_univ_names;
      open_function = open_univ_names;
      discharge_function = discharge_univ_names;
      subst_function = (fun (subst, a) -> (* Actually the name is generated once and for all. *) a);
      classify_function = (fun a -> Substitute a) }

let declare_univ_binders gr pl =
  if Global.is_polymorphic gr then
    ()
  else
    let l = let open GlobRef in match gr with
      | ConstRef c -> Label.to_id @@ Constant.label c
      | IndRef (c, _) -> Label.to_id @@ MutInd.label c
      | VarRef id ->
        CErrors.anomaly ~label:"declare_univ_binders" Pp.(str "declare_univ_binders on variable " ++ Id.print id ++ str".")
      | ConstructRef _ ->
        CErrors.anomaly ~label:"declare_univ_binders"
          Pp.(str "declare_univ_binders on an constructor reference")
    in
    let univs = Id.Map.fold (fun id univ univs ->
        match Univ.Level.name univ with
        | None -> assert false (* having Prop/Set/Var as binders is nonsense *)
        | Some univ -> (id,univ)::univs) pl []
    in
    Lib.add_anonymous_leaf (input_univ_names (QualifiedUniv l, univs))

let do_universe ~poly l =
  let in_section = Global.sections_are_opened () in
  let () =
    if poly && not in_section then
      CErrors.user_err ~hdr:"Constraint"
                   (str"Cannot declare polymorphic universes outside sections")
  in
  let l = List.map (fun {CAst.v=id} -> (id, UnivGen.new_univ_global ())) l in
  let ctx = List.fold_left (fun ctx (_,qid) -> Univ.LSet.add (Univ.Level.make qid) ctx)
      Univ.LSet.empty l, Univ.Constraint.empty
  in
  let src = if poly then BoundUniv else UnqualifiedUniv in
  let () = Lib.add_anonymous_leaf (input_univ_names (src, l)) in
  declare_universe_context ~poly ctx

let do_constraint ~poly l =
  let open Univ in
  let u_of_id x =
    Pretyping.interp_known_glob_level (Evd.from_env (Global.env ())) x
  in
  let constraints = List.fold_left (fun acc (l, d, r) ->
      let lu = u_of_id l and ru = u_of_id r in
      Constraint.add (lu, d, ru) acc)
      Constraint.empty l
  in
  let uctx = ContextSet.add_constraints constraints ContextSet.empty in
  declare_universe_context ~poly uctx
