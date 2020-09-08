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

type import_status = ImportDefaultBehavior | ImportNeedQualified

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

  module Constant = struct
    type t = constant_obj
    let tag = objConstant
    let kind obj = obj.cst_kind
  end

  let objVariable = objVariable

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

module Proof = struct
  type nonrec t = t
  let get_proof = get_proof
  let get_proof_name = get_proof_name
  let get_used_variables = get_used_variables
  let get_universe_decl = get_universe_decl
  let get_initial_euctx = get_initial_euctx
  let map_proof = map_proof
  let map_fold_proof = map_fold_proof
  let map_fold_proof_endline = map_fold_proof_endline
  let set_endline_tactic = set_endline_tactic
  let set_used_variables = set_used_variables
  let compact = compact_the_proof
  let update_global_env = update_global_env
  let get_open_goals = get_open_goals
end

let declare_definition_scheme ~internal ~univs ~role ~name c =
  let kind = Decls.(IsDefinition Scheme) in
  let entry = pure_definition_entry ~univs c in
  let kn, eff = declare_private_constant ~role ~kind ~name entry in
  let () = if internal then () else definition_message name in
  kn, eff

let _ = Ind_tables.declare_definition_scheme := declare_definition_scheme
let _ = Abstract.declare_abstract := declare_abstract

let declare_universe_context = DeclareUctx.declare_universe_context

type locality = Discharge | Global of import_status

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
  let should_suggest =
    entry.proof_entry_opaque
    && not (List.is_empty (Global.named_context()))
    && Option.is_empty entry.proof_entry_secctx
  in
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

let prepare_definition ?opaque ?inline ?fix_exn ~poly ~udecl ~types ~body sigma =
  let env = Global.env () in
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:false
      sigma (fun nf -> nf body, Option.map nf types)
  in
  Option.iter (check_evars_are_solved env sigma) types;
  check_evars_are_solved env sigma body;
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let entry = definition_entry ?fix_exn ?opaque ?inline ?types ~univs body in
  let uctx = Evd.evar_universe_context sigma in
  entry, uctx

let declare_definition ~name ~scope ~kind ~opaque ~impargs ~udecl ?hook
    ?obls ~poly ?inline ~types ~body ?fix_exn sigma =
  let entry, uctx = prepare_definition ?fix_exn ~opaque ~poly ~udecl ~types ~body ?inline sigma in
  declare_entry ~name ~scope ~kind ~impargs ?obls ?hook ~uctx entry

let prepare_obligation ?opaque ?inline ~name ~poly ~udecl ~types ~body sigma =
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:false
      sigma (fun nf -> nf body, Option.map nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let ce = definition_entry ?opaque ?inline ?types ~univs body in
  let env = Global.env () in
  let (c,ctx), sideff = Future.force ce.proof_entry_body in
  assert(Safe_typing.is_empty_private_constants sideff.Evd.seff_private);
  assert(Univ.ContextSet.is_empty ctx);
  RetrieveObl.check_evars env sigma;
  let c = EConstr.of_constr c in
  let typ = match ce.proof_entry_type with
    | Some t -> EConstr.of_constr t
    | None -> Retyping.get_type_of env sigma c
  in
  let obls, _, c, cty = RetrieveObl.retrieve_obligations env name sigma 0 c typ in
  let uctx = Evd.evar_universe_context sigma in
  c, cty, uctx, obls

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
