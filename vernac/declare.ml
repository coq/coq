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

type opacity_flag = Vernacexpr.opacity_flag = Opaque | Transparent

type t =
  { endline_tactic : Genarg.glob_generic_argument option
  ; section_vars : Id.Set.t option
  ; proof : Proof.t
  ; udecl: UState.universe_decl
  (** Initial universe declarations *)
  ; initial_euctx : UState.t
  (** The initial universe context (for the statement) *)
  }

(*** Proof Global manipulation ***)

let get_proof ps = ps.proof
let get_proof_name ps = (Proof.data ps.proof).Proof.name

let get_initial_euctx ps = ps.initial_euctx

let map_proof f p = { p with proof = f p.proof }
let map_fold_proof f p = let proof, res = f p.proof in { p with proof }, res

let map_fold_proof_endline f ps =
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

let compact_the_proof pf = map_proof Proof.compact pf

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac ps =
  { ps with endline_tactic = Some tac }

(** [start_proof ~name ~udecl ~poly sigma goals] starts a proof of
   name [name] with goals [goals] (a list of pairs of environment and
   conclusion). The proof is started in the evar map [sigma] (which
   can typically contain universe constraints), and with universe
   bindings [udecl]. *)
let start_proof ~name ~udecl ~poly sigma goals =
  let proof = Proof.start ~name ~poly sigma goals in
  let initial_euctx = Evd.evar_universe_context Proof.((data proof).sigma) in
  { proof
  ; endline_tactic = None
  ; section_vars = None
  ; udecl
  ; initial_euctx
  }

let start_dependent_proof ~name ~udecl ~poly goals =
  let proof = Proof.dependent_start ~name ~poly goals in
  let initial_euctx = Evd.evar_universe_context Proof.((data proof).sigma) in
  { proof
  ; endline_tactic = None
  ; section_vars = None
  ; udecl
  ; initial_euctx
  }

let get_used_variables pf = pf.section_vars
let get_universe_decl pf = pf.udecl

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

type import_status = Locality.import_status = ImportDefaultBehavior | ImportNeedQualified

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

let definition_entry ?fix_exn ?(opaque=false) ?(inline=false) ?feedback_id ?section_vars ?types
    ?(univs=default_univ_entry) ?(eff=Evd.empty_side_effects) ?(univsbody=Univ.ContextSet.empty) body =
  { proof_entry_body = Future.from_val ?fix_exn ((body,univsbody), eff);
    proof_entry_secctx = section_vars;
    proof_entry_type = types;
    proof_entry_universes = univs;
    proof_entry_opaque = opaque;
    proof_entry_feedback = feedback_id;
    proof_entry_inline_code = inline}

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
    | Some p -> p
    | None -> CErrors.user_err Pp.(str "Some unresolved existential variables remain")
  in
  let to_constr_typ t =
    if unsafe_typ then EConstr.Unsafe.to_constr t else to_constr_body t
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

let close_proof ~opaque ~keep_body_ucst_separate ps =

  let { section_vars; proof; udecl; initial_euctx } = ps in
  let { Proof.name; poly } = Proof.data proof in
  let unsafe_typ = keep_body_ucst_separate && not poly in
  let elist, uctx = prepare_proof ~unsafe_typ ps in
  let opaque = match opaque with Opaque -> true | Transparent -> false in

  let make_entry ((body, eff), typ) =

    let allow_deferred =
      not poly &&
      (keep_body_ucst_separate
       || not (Safe_typing.is_empty_private_constants eff.Evd.seff_private))
    in
    let used_univs_body = Vars.universes_of_constr body in
    let used_univs_typ = Vars.universes_of_constr typ in
    let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
    let utyp, ubody =
      if allow_deferred then
        let utyp = UState.univ_entry ~poly initial_euctx in
        let uctx = UState.constrain_variables (fst (UState.context_set initial_euctx)) uctx in
        (* For vi2vo compilation proofs are computed now but we need to
           complement the univ constraints of the typ with the ones of
           the body.  So we keep the two sets distinct. *)
        let uctx_body = UState.restrict uctx used_univs in
        let ubody = UState.check_mono_univ_decl uctx_body udecl in
        utyp, ubody
      else if poly && opaque && private_poly_univs () then
        let universes = UState.restrict uctx used_univs in
        let typus = UState.restrict universes used_univs_typ in
        let utyp = UState.check_univ_decl ~poly typus udecl in
        let ubody = Univ.ContextSet.diff
            (UState.context_set universes)
            (UState.context_set typus)
        in
        utyp, ubody
      else
        (* Since the proof is computed now, we can simply have 1 set of
           constraints in which we merge the ones for the body and the ones
           for the typ. We recheck the declaration after restricting with
           the actually used universes.
           TODO: check if restrict is really necessary now. *)
        let ctx = UState.restrict uctx used_univs in
        let utyp = UState.check_univ_decl ~poly ctx udecl in
        utyp, Univ.ContextSet.empty
    in
    definition_entry ~opaque ?section_vars ~univs:utyp ~univsbody:ubody ~types:typ ~eff body
  in
  let entries = CList.map make_entry elist  in
  { name; entries; uctx }

type 'a constant_entry =
  | DefinitionEntry of 'a proof_entry
  | ParameterEntry of Entries.parameter_entry
  | PrimitiveEntry of Entries.primitive_entry

type constant_obj = {
  cst_kind : Decls.logical_kind;
  cst_locl : import_status;
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
  | ImportNeedQualified -> ()
  | ImportDefaultBehavior ->
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

let pure_definition_entry ?fix_exn ?(opaque=false) ?(inline=false) ?types
    ?(univs=default_univ_entry) body =
  { proof_entry_body = Future.from_val ?fix_exn ((body,Univ.ContextSet.empty), ());
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

let declare_constant ?(local = ImportDefaultBehavior) ~name ~kind cd =
  let () = check_exists name in
  let kn = define_constant ~name cd in
  (* Register the libobjects attached to the constants *)
  let () = register_constant kn kind local in
  kn

let get_cd_fix_exn = function
  | DefinitionEntry de ->
    Future.fix_exn_of de.proof_entry_body
  | _ -> fun x -> x

let declare_constant ?local ~name ~kind cd =
  try declare_constant ?local ~name ~kind cd
  with exn ->
    let exn = Exninfo.capture exn in
    Exninfo.iraise (get_cd_fix_exn cd exn)

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
  let open Libobject in
  declare_object_full { (default_object "VARIABLE") with
    classify_function = (fun () -> Dispose)}

let inVariable v = Libobject.Dyn.Easy.inj v objVariable

let declare_variable ~name ~kind d =
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

  type nonrec constant_obj = constant_obj

  let objVariable = objVariable
  let objConstant = objConstant

end
(*** Proof Global Environment ***)

type closed_proof_output = (Constr.t * Evd.side_effects) list * UState.t

let close_proof_delayed ~feedback_id ps (fpl : closed_proof_output Future.computation) =
  let { section_vars; proof; udecl; initial_euctx } = ps in
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
  List.map fst p, uctx

let update_global_env =
  map_proof (fun p ->
      let { Proof.sigma } = Proof.data p in
      let tac = Proofview.Unsafe.tclEVARS (Evd.update_sigma_env sigma (Global.env ())) in
      let p, (status,info), _ = Proof.run_tactic (Global.env ()) tac p in
      p)

let next = let n = ref 0 in fun () -> incr n; !n

let by tac = map_fold_proof (Proof.solve (Goal_select.SelectNth 1) None tac)

let build_constant_by_tactic ~name ?(opaque=Transparent) ~uctx ~sign ~poly typ tac =
  let evd = Evd.from_ctx uctx in
  let goals = [ (Global.env_of_context sign , typ) ] in
  let pf = start_proof ~name ~poly ~udecl:UState.default_univ_decl evd goals in
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
    try build_constant_by_tactic ~name ~opaque:Transparent ~poly ~uctx ~sign:secsign concl solve_tac
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
     `if poly && opaque && private_poly_univs ()` in `Proof_global`
     kernel will boom. This deserves more investigation. *)
  let const = Internal.set_opacity ~opaque const in
  let const, args = Internal.shrink_entry sign const in
  let cst () =
    (* do not compute the implicit arguments, it may be costly *)
    let () = Impargs.make_implicit_args false in
    (* ppedrot: seems legit to have abstracted subproofs as local*)
    declare_private_constant ~local:ImportNeedQualified ~name ~kind const
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
  let p = get_proof pf in
  Proof.get_goal_context_gen p i

let get_current_goal_context pf =
  let p = get_proof pf in
  try Proof.get_goal_context_gen p 1
  with
  | Proof.NoSuchGoal _ ->
    (* spiwack: returning empty evar_map, since if there is no goal,
       under focus, there is no accessible evar either. EJGA: this
       seems strange, as we have pf *)
    let env = Global.env () in
    Evd.from_env env, env

let get_current_context pf =
  let p = get_proof pf in
  Proof.get_proof_context p

let declare_definition_scheme ~internal ~univs ~role ~name c =
  let kind = Decls.(IsDefinition Scheme) in
  let entry = pure_definition_entry ~univs c in
  let kn, eff = declare_private_constant ~role ~kind ~name entry in
  let () = if internal then () else definition_message name in
  kn, eff

let _ = Ind_tables.declare_definition_scheme := declare_definition_scheme
let _ = Abstract.declare_abstract := declare_abstract

let declare_universe_context = DeclareUctx.declare_universe_context

type locality = Locality.locality = | Discharge | Global of import_status

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
      ; scope : locality
      (**  [locality]: Locality of the original declaration *)
      ; dref : Names.GlobRef.t
      (** [ref]: identifier of the original declaration *)
      }
  end

  type t = (S.t -> unit) CEphemeron.key

  let make hook = CEphemeron.create hook

  let call ?hook x = Option.iter (fun hook -> CEphemeron.get hook x) hook

end

(* Locality stuff *)
let declare_entry ~name ~scope ~kind ?hook ?(obls=[]) ~impargs ~uctx entry =
  let should_suggest = entry.proof_entry_opaque &&
                       Option.is_empty entry.proof_entry_secctx in
  let ubind = UState.universe_binders uctx in
  let dref = match scope with
  | Discharge ->
    let () = declare_variable ~name ~kind (SectionLocalDef entry) in
    if should_suggest then Proof_using.suggest_variable (Global.env ()) name;
    Names.GlobRef.VarRef name
  | Global local ->
    let kn = declare_constant ~name ~local ~kind (DefinitionEntry entry) in
    let gr = Names.GlobRef.ConstRef kn in
    if should_suggest then Proof_using.suggest_constant (Global.env ()) kn;
    let () = DeclareUniv.declare_univ_binders gr ubind in
    gr
  in
  let () = Impargs.maybe_declare_manual_implicits false dref impargs in
  let () = definition_message name in
  Option.iter (fun hook -> Hook.call ~hook { Hook.S.uctx; obls; scope; dref }) hook;
  dref

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

module Recthm = struct
  type t =
    { name : Names.Id.t
    (** Name of theorem *)
    ; typ : Constr.t
    (** Type of theorem  *)
    ; args : Names.Name.t list
    (** Names to pre-introduce  *)
    ; impargs : Impargs.manual_implicits
    (** Explicitily declared implicit arguments  *)
    }
end

let declare_mutually_recursive ~opaque ~scope ~kind ~poly ~uctx ~udecl ~ntns ~rec_declaration ~possible_indexes ?(restrict_ucontext=true) fixitems =
  let vars, fixdecls, indexes =
    mutual_make_bodies ~fixitems ~rec_declaration ~possible_indexes in
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
      (fun Recthm.{ name; typ; impargs } body ->
         let entry = definition_entry ~opaque ~types:typ ~univs body in
         declare_entry ~name ~scope ~kind ~impargs ~uctx entry)
      fixitems fixdecls
  in
  let isfix = Option.has_some possible_indexes in
  let fixnames = List.map (fun { Recthm.name } -> name) fixitems in
  recursive_message isfix indexes fixnames;
  List.iter (Metasyntax.add_notation_interpretation (Global.env())) ntns;
  csts

let warn_let_as_axiom =
  CWarnings.create ~name:"let-as-axiom" ~category:"vernacular"
    Pp.(fun id -> strbrk "Let definition" ++ spc () ++ Names.Id.print id ++
                  spc () ++ strbrk "declared as an axiom.")

let declare_assumption ~name ~scope ~hook ~impargs ~uctx pe =
  let local = match scope with
    | Discharge -> warn_let_as_axiom name; ImportNeedQualified
    | Global local -> local
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

let declare_assumption ?fix_exn ~name ~scope ~hook ~impargs ~uctx pe =
  try declare_assumption ~name ~scope ~hook ~impargs ~uctx pe
  with exn ->
    let exn = Exninfo.capture exn in
    let exn = Option.cata (fun fix -> fix exn) exn fix_exn in
    Exninfo.iraise exn

(* Preparing proof entries *)

let prepare_definition ?opaque ?inline ?fix_exn ~poly ~udecl ~types ~body sigma =
  let env = Global.env () in
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:true
      sigma (fun nf -> nf body, Option.map nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let entry = definition_entry ?fix_exn ?opaque ?inline ?types ~univs body in
  let uctx = Evd.evar_universe_context sigma in
  entry, uctx

let declare_definition ~name ~scope ~kind ~opaque ~impargs ~udecl ?hook
    ?obls ~poly ?inline ~types ~body ?fix_exn sigma =
  let entry, uctx = prepare_definition ?fix_exn ~opaque ~poly ~udecl ~types ~body ?inline sigma in
  declare_entry ~name ~scope ~kind ~impargs ?obls ?hook ~uctx entry

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

(* Compat: will remove *)
exception AlreadyDeclared = DeclareUniv.AlreadyDeclared

module Obls = struct

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
  type t =
    { prg_name : Id.t
    ; prg_body : constr
    ; prg_type : constr
    ; prg_ctx : UState.t
    ; prg_univdecl : UState.universe_decl
    ; prg_obligations : obligations
    ; prg_deps : Id.t list
    ; prg_fixkind : fixpoint_kind option
    ; prg_implicits : Impargs.manual_implicits
    ; prg_notations : Vernacexpr.decl_notation list
    ; prg_poly : bool
    ; prg_scope : locality
    ; prg_kind : Decls.definition_object_kind
    ; prg_reduce : constr -> constr
    ; prg_hook : Hook.t option
    ; prg_opaque : bool }

  open Obligation

  let make ?(opaque = false) ?hook n ~udecl ~uctx ~impargs ~poly ~scope ~kind b
      t deps fixkind notations obls reduce =
    let obls', b =
      match b with
      | None ->
        assert (Int.equal (Array.length obls) 0);
        let n = Nameops.add_suffix n "_obligation" in
        ( [| { obl_name = n
             ; obl_body = None
             ; obl_location = Loc.tag Evar_kinds.InternalHole
             ; obl_type = t
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
    let ctx = UState.make_flexible_nonalgebraic uctx in
    { prg_name = n
    ; prg_body = b
    ; prg_type = reduce t
    ; prg_ctx = ctx
    ; prg_univdecl = udecl
    ; prg_obligations = {obls = obls'; remaining = Array.length obls'}
    ; prg_deps = deps
    ; prg_fixkind = fixkind
    ; prg_notations = notations
    ; prg_implicits = impargs
    ; prg_poly = poly
    ; prg_scope = scope
    ; prg_kind = kind
    ; prg_reduce = reduce
    ; prg_hook = hook
    ; prg_opaque = opaque }

  let set_uctx ~uctx prg = {prg with prg_ctx = uctx}
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
  Hints.add_hints ~locality [Id.to_string prg.prg_name] (unfold_entry cst)

(* true = hide obligations *)
let get_hide_obligations =
  Goptions.declare_bool_option_and_ref
    ~depr:true
    ~key:["Hide"; "Obligations"]
    ~value:false

let declare_obligation prg obl ~uctx ~types ~body =
  let univs = UState.univ_entry ~poly:prg.prg_poly uctx in
  let body = prg.prg_reduce body in
  let types = Option.map prg.prg_reduce types in
  match obl.obl_status with
  | _, Evar_kinds.Expand -> (false, {obl with obl_body = Some (TermObl body)})
  | force, Evar_kinds.Define opaque ->
    let opaque = (not force) && opaque in
    let poly = prg.prg_poly in
    let ctx, body, ty, args =
      if not poly then shrink_body body types
      else ([], body, types, [||])
    in
    let ce = definition_entry ?types:ty ~opaque ~univs body in
    (* ppedrot: seems legit to have obligations as local *)
    let constant =
      declare_constant ~name:obl.obl_name
        ~local:ImportNeedQualified
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
    (true, {obl with obl_body = body})

(* Updating the obligation meta-info on close *)

let not_transp_msg =
  Pp.(
    str "Obligation should be transparent but was declared opaque."
    ++ spc ()
    ++ str "Use 'Defined' instead.")

let pperror cmd = CErrors.user_err ~hdr:"Program" cmd
let err_not_transp () = pperror not_transp_msg

module ProgMap = Id.Map

module StateFunctional = struct

  type t = ProgramDecl.t CEphemeron.key ProgMap.t

  let _empty = ProgMap.empty

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

module State = struct

  type t = StateFunctional.t

  open StateFunctional

  let prg_ref, prg_tag =
    Summary.ref_tag ProgMap.empty ~name:"program-tcc-table"

  let num_pending () = num_pending !prg_ref
  let first_pending () = first_pending !prg_ref
  let get_unique_open_prog id = get_unique_open_prog !prg_ref id
  let add id prg = prg_ref := add !prg_ref id prg
  let fold ~f ~init = fold !prg_ref ~f ~init
  let all () = all !prg_ref
  let find id = find !prg_ref id

end

(* In all cases, the use of the map is read-only so we don't expose the ref *)
let map_keys m = ProgMap.fold (fun k _ l -> k :: l) m []

let check_solved_obligations ~what_for : unit =
  if not (ProgMap.is_empty !State.prg_ref) then
    let keys = map_keys !State.prg_ref in
    let have_string = if Int.equal (List.length keys) 1 then " has " else " have " in
    CErrors.user_err ~hdr:"Program"
      Pp.(
        str "Unsolved obligations when closing "
        ++ what_for ++ str ":" ++ spc ()
        ++ prlist_with_sep spc (fun x -> Id.print x) keys
        ++ str have_string
        ++ str "unsolved obligations" )

let map_replace k v m = ProgMap.add k (CEphemeron.create v) (ProgMap.remove k m)
let progmap_remove pm prg = ProgMap.remove prg.prg_name pm
let progmap_replace prg' pm = map_replace prg'.prg_name prg' pm
let obligations_solved prg = Int.equal prg.prg_obligations.remaining 0

let obligations_message rem =
  Format.asprintf "%s %s remaining"
    (if rem > 0 then string_of_int rem else "No more")
    (CString.plural rem "obligation")
  |> Pp.str |> Flags.if_verbose Feedback.msg_info

type progress = Remain of int | Dependent | Defined of GlobRef.t

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
    , replace_appvars subst (* Termops.refresh_universes *) prg.prg_type )
  else
    let subst' = List.map (fun (n, (_, b)) -> (n, b)) subst in
    ( Vars.replace_vars subst' prg.prg_body
    , Vars.replace_vars subst' (* Termops.refresh_universes *) prg.prg_type )

let stm_get_fix_exn = ref (fun _ x -> x)

let declare_definition prg =
  let varsubst = obligation_substitution true prg in
  let sigma = Evd.from_ctx prg.prg_ctx in
  let body, types = subst_prog varsubst prg in
  let body, types = EConstr.(of_constr body, Some (of_constr types)) in
  (* All these should be grouped into a struct a some point *)
  let opaque, poly, udecl, hook =
    (prg.prg_opaque, prg.prg_poly, prg.prg_univdecl, prg.prg_hook)
  in
  let name, scope, kind, impargs =
    ( prg.prg_name
    , prg.prg_scope
    , Decls.(IsDefinition prg.prg_kind)
    , prg.prg_implicits )
  in
  let fix_exn = !stm_get_fix_exn () in
  let obls = List.map (fun (id, (_, c)) -> (id, c)) varsubst in
  (* XXX: This is doing normalization twice *)
  let kn =
    declare_definition ~name ~scope ~kind ~impargs ?hook ~obls
      ~fix_exn ~opaque ~poly ~udecl ~types ~body sigma
  in
  let pm = progmap_remove !State.prg_ref prg in
  State.prg_ref := pm;
  kn

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

let declare_mutual_definition l =
  let len = List.length l in
  let first = List.hd l in
  let defobl x =
    let oblsubst = obligation_substitution true x in
    let subs, typ = subst_prog oblsubst x in
    let env = Global.env () in
    let sigma = Evd.from_ctx x.prg_ctx in
    let r = Retyping.relevance_of_type env sigma (EConstr.of_constr typ) in
    let term =
      snd (Reductionops.splay_lam_n env sigma len (EConstr.of_constr subs))
    in
    let typ =
      snd (Reductionops.splay_prod_n env sigma len (EConstr.of_constr typ))
    in
    let term = EConstr.to_constr sigma term in
    let typ = EConstr.to_constr sigma typ in
    let def = (x.prg_reduce term, r, x.prg_reduce typ, x.prg_implicits) in
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
        , Recthm.{name; typ; impargs; args = []} :: a4 ))
      defs first.prg_deps ([], [], [], [])
  in
  let fixkind = Option.get first.prg_fixkind in
  let arrrec, recvec = (Array.of_list fixtypes, Array.of_list fixdefs) in
  let rvec = Array.of_list fixrs in
  let namevec = Array.of_list (List.map (fun x -> Name x.prg_name) l) in
  let rec_declaration = (Array.map2 Context.make_annot namevec rvec, arrrec, recvec) in
  let possible_indexes =
    match fixkind with
    | IsFixpoint wfl ->
      Some (List.map3 compute_possible_guardness_evidences wfl fixdefs fixtypes)
    | IsCoFixpoint -> None
  in
  (* In the future we will pack all this in a proper record *)
  let poly, scope, ntns, opaque =
    (first.prg_poly, first.prg_scope, first.prg_notations, first.prg_opaque)
  in
  let kind =
    if fixkind != IsCoFixpoint then Decls.(IsDefinition Fixpoint)
    else Decls.(IsDefinition CoFixpoint)
  in
  (* Declare the recursive definitions *)
  let udecl = UState.default_univ_decl in
  let kns =
    declare_mutually_recursive ~scope ~opaque ~kind ~udecl ~ntns
      ~uctx:first.prg_ctx ~rec_declaration ~possible_indexes ~poly
      ~restrict_ucontext:false fixitems
  in
  (* Only for the first constant *)
  let dref = List.hd kns in
  Hook.(
    call ?hook:first.prg_hook {S.uctx = first.prg_ctx; obls; scope; dref});
  let pm = List.fold_left progmap_remove !State.prg_ref l in
  State.prg_ref := pm;
  dref

let update_obls prg obls rem =
  let prg_obligations = {obls; remaining = rem} in
  let prg' = {prg with prg_obligations} in
  let pm = progmap_replace prg' !State.prg_ref in
  State.prg_ref := pm;
  obligations_message rem;
  if rem > 0 then Remain rem
  else
    match prg'.prg_deps with
    | [] ->
      let kn = declare_definition prg' in
      let pm = progmap_remove !State.prg_ref prg' in
      State.prg_ref := pm;
      Defined kn
    | l ->
      let progs =
        List.map (fun x -> CEphemeron.get (ProgMap.find x pm)) prg'.prg_deps
      in
      if List.for_all (fun x -> obligations_solved x) progs then
        let kn = declare_mutual_definition progs in
        Defined kn
      else Dependent

let dependencies obls n =
  let res = ref Int.Set.empty in
  Array.iteri
    (fun i obl ->
      if (not (Int.equal i n)) && Int.Set.mem n obl.obl_deps then
        res := Int.Set.add i !res)
    obls;
  !res

let update_program_decl_on_defined prg obls num obl ~uctx rem ~auto =
  let obls = Array.copy obls in
  let () = obls.(num) <- obl in
  let prg = {prg with prg_ctx = uctx} in
  let _progress = update_obls prg obls (pred rem) in
  let () =
    if pred rem > 0 then
      let deps = dependencies obls num in
      if not (Int.Set.is_empty deps) then
        let _progress = auto (Some prg.prg_name) deps None in
        ()
      else ()
    else ()
  in
  ()

type obligation_resolver =
     Id.t option
  -> Int.Set.t
  -> unit Proofview.tactic option
  -> progress

type obligation_qed_info = {name : Id.t; num : int; auto : obligation_resolver}

let obligation_terminator entries uctx {name; num; auto} =
  match entries with
  | [entry] ->
    let env = Global.env () in
    let ty = entry.proof_entry_type in
    let body, uctx = inline_private_constants ~uctx env entry in
    let sigma = Evd.from_ctx uctx in
    Inductiveops.control_only_guard (Global.env ()) sigma
      (EConstr.of_constr body);
    (* Declare the obligation ourselves and drop the hook *)
    let prg = Option.get (State.find name) in
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
    let uctx = if prg.prg_poly then uctx else UState.union prg.prg_ctx uctx in
    let defined, obl = declare_obligation prg obl ~body ~types:ty ~uctx in
    let prg_ctx =
      if prg.prg_poly then
        (* Polymorphic *)
        (* We merge the new universes and constraints of the
           polymorphic obligation with the existing ones *)
        UState.union prg.prg_ctx uctx
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
    update_program_decl_on_defined prg obls num obl ~uctx:prg_ctx rem ~auto
  | _ ->
    CErrors.anomaly
      Pp.(
        str
          "[obligation_terminator] close_proof returned more than one proof \
           term")

(* Similar to the terminator but for the admitted path; this assumes
   the admitted constant was already declared.

   FIXME: There is duplication of this code with obligation_terminator
   and Obligations.admit_obligations *)
let obligation_admitted_terminator {name; num; auto} ctx' dref =
  let prg = Option.get (State.find name) in
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
    if not prg.prg_poly (* Not polymorphic *) then
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
  update_program_decl_on_defined prg obls num obl ~uctx:ctx' rem ~auto

end

(************************************************************************)
(* Commom constant saving path, for both Qed and Admitted               *)
(************************************************************************)

(* Support for mutually proved theorems *)

module Proof_ending = struct

  type t =
    | Regular
    | End_obligation of Obls.obligation_qed_info
    | End_derive of { f : Id.t; name : Id.t }
    | End_equations of
        { hook : Constant.t list -> Evd.evar_map -> unit
        ; i : Id.t
        ; types : (Environ.env * Evar.t * Evd.evar_info * EConstr.named_context * Evd.econstr) list
        ; sigma : Evd.evar_map
        }

end

type lemma_possible_guards = int list list

module Info = struct

  type t =
    { hook : Hook.t option
    ; proof_ending : Proof_ending.t CEphemeron.key
    (* This could be improved and the CEphemeron removed *)
    ; scope : locality
    ; kind : Decls.logical_kind
    (* thms and compute guard are specific only to start_lemma_with_initialization + regular terminator *)
    ; thms : Recthm.t list
    ; compute_guard : lemma_possible_guards
    }

  let make ?hook ?(proof_ending=Proof_ending.Regular) ?(scope=Global ImportDefaultBehavior)
      ?(kind=Decls.(IsProof Lemma)) ?(compute_guard=[]) ?(thms=[]) () =
    { hook
    ; compute_guard
    ; proof_ending = CEphemeron.create proof_ending
    ; thms
    ; scope
    ; kind
    }

  (* This is used due to a deficiency on the API, should fix *)
  let add_first_thm ~info ~name ~typ ~impargs =
    let thms =
      { Recthm.name
      ; impargs
      ; typ = EConstr.Unsafe.to_constr typ
      ; args = [] } :: info.thms
    in
    { info with thms }

end

(* XXX: this should be unified with the code for non-interactive
   mutuals previously on this file. *)
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
    -> Evd.side_effects proof_entry
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

  let declare_mutdef ~uctx ~info pe i Recthm.{ name; impargs; typ; _} =
    let { Info.hook; scope; kind; compute_guard; _ } = info in
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

  let declare_mutdef ~info ~uctx const =
    let pe = match info.Info.compute_guard with
    | [] ->
      (* Not a recursive statement *)
      const
    | possible_indexes ->
      (* Try all combinations... not optimal *)
      let env = Global.env() in
      Internal.map_entry_body const
        ~f:(guess_decreasing env possible_indexes)
    in
    List.map_i (declare_mutdef ~info ~uctx pe) 0 info.Info.thms

  let declare_variable ~info ~uctx pe =
    let { Info.scope; hook } = info in
    List.map_i (
      fun i { Recthm.name; typ; impargs } ->
        declare_assumption ~name ~scope ~hook ~impargs ~uctx pe
    ) 0 info.Info.thms

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

let finish_admitted ~info ~uctx pe =
  let cst = MutualEntry.declare_variable ~info ~uctx pe in
  (* If the constant was an obligation we need to update the program map *)
  match CEphemeron.get info.Info.proof_ending with
  | Proof_ending.End_obligation oinfo ->
    Obls.obligation_admitted_terminator oinfo uctx (List.hd cst)
  | _ -> ()

let save_lemma_admitted ~proof ~info  =
  let udecl = get_universe_decl proof in
  let Proof.{ poly; entry } = Proof.data (get_proof proof) in
  let typ = match Proofview.initial_goals entry with
    | [typ] -> snd typ
    | _ -> CErrors.anomaly ~label:"Lemmas.save_lemma_admitted" (Pp.str "more than one statement.")
  in
  let typ = EConstr.Unsafe.to_constr typ in
  let iproof = get_proof proof in
  let pproofs = Proof.partial_proof iproof in
  let sec_vars = compute_proof_using_for_admitted proof typ pproofs in
  let uctx = get_initial_euctx proof in
  let univs = UState.check_univ_decl ~poly uctx udecl in
  finish_admitted ~info ~uctx (sec_vars, (typ, univs), None)

(************************************************************************)
(* Saving a lemma-like constant                                         *)
(************************************************************************)

let finish_proved po info =
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
  let _ : Names.Constant.t = declare_constant ~name ~kind:Decls.(IsProof Proposition) lemma_def in
  ()

let finish_proved_equations ~kind ~hook i proof_obj types sigma0 =

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
  hook recobls sigma

let finalize_proof proof_obj proof_info =
  let open Proof_ending in
  match CEphemeron.default proof_info.Info.proof_ending Regular with
  | Regular ->
    finish_proved proof_obj proof_info
  | End_obligation oinfo ->
    Obls.obligation_terminator proof_obj.entries proof_obj.uctx oinfo
  | End_derive { f ; name } ->
    finish_derived ~f ~name ~entries:proof_obj.entries
  | End_equations { hook; i; types; sigma } ->
    finish_proved_equations ~kind:proof_info.Info.kind ~hook i proof_obj types sigma

let err_save_forbidden_in_place_of_qed () =
  CErrors.user_err (Pp.str "Cannot use Save with more than one constant or in this proof mode")

let process_idopt_for_save ~idopt info =
  match idopt with
  | None -> info
  | Some { CAst.v = save_name } ->
    (* Save foo was used; we override the info in the first theorem *)
    let thms =
      match info.Info.thms, CEphemeron.default info.Info.proof_ending Proof_ending.Regular with
      | [ { Recthm.name; _} as decl ], Proof_ending.Regular ->
        [ { decl with Recthm.name = save_name } ]
      | _ ->
        err_save_forbidden_in_place_of_qed ()
    in { info with Info.thms }

let save_lemma_proved ~proof ~info ~opaque ~idopt =
  (* Env and sigma are just used for error printing in save_remaining_recthms *)
  let proof_obj = close_proof ~opaque ~keep_body_ucst_separate:false proof in
  let proof_info = process_idopt_for_save ~idopt info in
  finalize_proof proof_obj proof_info

(***********************************************************************)
(* Special case to close a lemma without forcing a proof               *)
(***********************************************************************)
let save_lemma_admitted_delayed ~proof ~info =
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
  finish_admitted ~uctx ~info (sec_vars, (typ, ctx), None)

let save_lemma_proved_delayed ~proof ~info ~idopt =
  (* vio2vo calls this but with invalid info, we have to workaround
     that to add the name to the info structure *)
  if CList.is_empty info.Info.thms then
    let name = get_po_name proof in
    let info = Info.add_first_thm ~info ~name ~typ:EConstr.mkSet ~impargs:[] in
    finalize_proof proof info
  else
    let info = process_idopt_for_save ~idopt info in
    finalize_proof proof info

module Proof = struct
  type nonrec t = t
  let get_proof = get_proof
  let get_proof_name = get_proof_name
  let map_proof = map_proof
  let map_fold_proof = map_fold_proof
  let map_fold_proof_endline = map_fold_proof_endline
  let set_endline_tactic = set_endline_tactic
  let set_used_variables = set_used_variables
  let compact = compact_the_proof
  let update_global_env = update_global_env
  let get_open_goals = get_open_goals
end
