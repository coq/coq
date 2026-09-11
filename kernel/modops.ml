(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)
(* Inlining and more liberal use of modules and module types by Claudio
   Sacerdoti, Nov 2004 *)
(* New structure-based model of modules and miscellaneous bug fixes by
   Élie Soubiran, from Feb 2008 *)

(* This file provides with various operations on modules and module types *)

open Util
open Names
open Constr
open Declarations
open Mod_declarations
open Declareops
open Environ
open Mod_subst

(** {6 Errors } *)

type signature_mismatch_error =
  | InductiveFieldExpected of mutual_inductive_body
  | DefinitionFieldExpected
  | ModuleFieldExpected
  | ModuleTypeFieldExpected
  | NotConvertibleInductiveField of Id.t * (env * types * types) option
  | NotConvertibleConstructorField of Id.t * (env * types * types) option
  | NotConvertibleBodyField of (env * constr * constr) option
  | NotConvertibleTypeField of env * types * types
  | CumulativeStatusExpected of bool
  | PolymorphicStatusExpected of bool
  | NotSameConstructorNamesField of Id.t array * Id.t array
  | NotSameInductiveNameInBlockField of Id.t * Id.t
  | FiniteInductiveFieldExpected of bool
  | InductiveNumbersFieldExpected of { got : int; expected : int }
  | InductiveParams of { env : Environ.env; got : rel_context; expected : rel_context }
  | RecordFieldExpected of bool
  | RecordProjectionsExpected of { expected : Name.t list; got : Name.t list }
  | NotEqualInductiveAliases of MutInd.t * MutInd.t
  | IncompatibleUniverses of { err : UGraph.univ_inconsistency; env : env; t1 : types; t2 : types }
  | IncompatibleQualities of { err : QGraph.elimination_error; env : env; t1 : types; t2 : types }
  | IncompatiblePolymorphism of env * types * types
  | IncompatibleUnivConstraints of { env : env; got : UVars.AbstractContext.t; expect : UVars.AbstractContext.t }
  | IncompatibleVariance
  | NoRewriteRulesSubtyping

type with_constraint_error =
  | WithSignatureMismatch of signature_mismatch_error
  | WithCannotConstrainPrimitive
  | WithCannotConstrainSymbol

type subtyping_trace_elt =
  | Submodule of Id.t
  | FunctorArgument of int

type module_typing_error =
  | SignatureMismatch of subtyping_trace_elt list * Id.t * signature_mismatch_error
  | LabelAlreadyDeclared of Id.t
  | NotAFunctor
  | IsAFunctor of ModPath.t
  | IncompatibleModuleTypes of module_type_body * module_type_body
  | NotEqualModulePaths of ModPath.t * ModPath.t
  | NoSuchLabel of Id.t * ModPath.t
  | NotAModuleLabel of Id.t
  | NotAConstant of Id.t
  | IncorrectWithConstraint of Id.t * with_constraint_error
  | GenerativeModuleExpected of Id.t
  | LabelMissing of Id.t * string
  | IncludeRestrictedFunctor of ModPath.t

exception ModuleTypingError of module_typing_error

let error_existing_label l =
  raise (ModuleTypingError (LabelAlreadyDeclared l))

let error_not_a_functor () =
  raise (ModuleTypingError NotAFunctor)

let error_is_a_functor mp =
  raise (ModuleTypingError (IsAFunctor mp))

let error_incompatible_modtypes mexpr1 mexpr2 =
  raise (ModuleTypingError (IncompatibleModuleTypes (mexpr1,mexpr2)))

let error_not_equal_modpaths mp1 mp2 =
  raise (ModuleTypingError (NotEqualModulePaths (mp1,mp2)))

let error_signature_mismatch trace l why =
  raise (ModuleTypingError (SignatureMismatch (trace,l,why)))

let error_no_such_label l mp =
  raise (ModuleTypingError (NoSuchLabel (l,mp)))

let error_not_a_module_label s =
  raise (ModuleTypingError (NotAModuleLabel s))

let error_not_a_constant l =
  raise (ModuleTypingError (NotAConstant l))

let error_incorrect_with_constraint l err =
  raise (ModuleTypingError (IncorrectWithConstraint (l, err)))

let error_generative_module_expected l =
  raise (ModuleTypingError (GenerativeModuleExpected l))

let error_no_such_label_sub l l1 =
  raise (ModuleTypingError (LabelMissing (l,l1)))

let error_include_restricted_functor mp =
  raise (ModuleTypingError (IncludeRestrictedFunctor mp))

(** {6 Operations on functors } *)

let is_functor = function
  | NoFunctor _ -> false
  | MoreFunctor _ -> true

let destr_functor = function
  | NoFunctor _ -> error_not_a_functor ()
  | MoreFunctor (mbid,ty,x) -> (mbid,ty,x)

let destr_nofunctor mp = function
  | NoFunctor a -> a
  | MoreFunctor _ -> error_is_a_functor mp

let get_global_delta mb = match mod_global_delta mb with
| None -> assert false
| Some delta -> delta

(** {6 Misc operations } *)

let check_modpath_equiv env mp1 mp2 =
  if ModPath.equal mp1 mp2 then ()
  else
    let mp1' = mp_of_delta (mod_delta @@ lookup_module mp1 env) mp1 in
    let mp2' = mp_of_delta (mod_delta @@ lookup_module mp2 env) mp2 in
    if ModPath.equal mp1' mp2' then ()
    else error_not_equal_modpaths mp1 mp2

let rec annotate_module_expression me mty = match me, mty with
| MENoFunctor me, (NoFunctor _ | MoreFunctor _) -> NoFunctor me
| MEMoreFunctor me, MoreFunctor (mbid, arg, mty) ->
  let me = annotate_module_expression me mty in
  MoreFunctor (mbid, arg, me)
| MEMoreFunctor _, NoFunctor _ -> assert false

let rec annotate_struct_body body sign = match sign with
| NoFunctor _ -> NoFunctor body
| MoreFunctor (mbid, mty, sign) ->
  MoreFunctor (mbid, mty, annotate_struct_body body sign)

(** {6 Substitutions of modular structures } *)

let subst_signature subst = subst_signature subst_codom subst
let subst_structure subst = subst_structure subst_codom subst

(** {6 Adding a module in the environment } *)

let add_retroknowledge l env =
  List.fold_left Primred.add_retroknowledge env l

let rec add_structure : type a. _ -> _ -> a delta_resolver -> _ -> _ -> _ =
  fun mp sign resolver linkinfo env ->
  let add_field env (l,elem) = match elem with
    | SFBconst cb ->
      let c = constant_of_delta_kn resolver (KerName.make mp l) in
      Environ.add_constant_key c cb linkinfo env
    | SFBmind mib ->
      let mind = mind_of_delta_kn resolver (KerName.make mp l) in
      let mib =
        if mib.mind_private != None then
          { mib with mind_private = Some true }
        else mib
      in
      Environ.add_mind_key mind mib linkinfo env
    | SFBmodule mb -> add_module (MPdot (mp, l)) mb linkinfo env (* adds components as well *)
    | SFBmodtype mtb -> Environ.add_modtype (MPdot (mp, l)) mtb env
    | SFBrules r -> Environ.add_rewrite_rules r.rewrules_rules env
  in
  List.fold_left add_field env sign

and add_module mp mb linkinfo env =
  let env = Environ.shallow_add_module mp mb env in
  match mod_type mb with
  | NoFunctor struc ->
    let delta = get_global_delta mb in
    add_structure mp struc delta linkinfo env
  | MoreFunctor _ -> env

let add_linked_module mp mb linkinfo env =
  add_module mp mb linkinfo env

let add_structure mp sign resolver env =
  add_structure mp sign resolver no_link_info env

let add_module mp mb env =
  add_module mp mb no_link_info env

let add_module_parameter mbid mtb env =
  add_module (MPbound mbid) (module_body_of_type mtb) env

(** {6 Recompiling the VM bytecode of a module}

    The checker does not trust the VM bytecode serialized in a [.vo] file, nor
    the code descriptors [const_body_code] stored in the declarations: both are
    attacker-controlled data the typechecker cannot validate. Instead it
    recompiles the bytecode of every constant from the body it is about to
    check, and records it in a table of its own, so that the code the VM runs
    agrees with the checked body by construction. *)

let push_bytecode vmtab code =
  let open Vmemitcodes in
  match code with
  | BCdefined (mask, code, patches) ->
    let vmtab, index = Vmlibrary.add code vmtab in
    vmtab, BCdefined (mask, index, patches)
  | (BCalias _ | BCconstant | BCuncompiled) as code -> vmtab, code

let compile_constant_bytecode env vmtab cb =
  let code =
    Vmbytegen.compile_constant_body ~fail_on_error:false env
      cb.const_universes cb.const_body
  in
  let vmtab, code = push_bytecode vmtab code in
  vmtab, { cb with const_body_code = code }

(* The environment is threaded exactly as in [add_structure], so that each
   constant is compiled in the environment it is declared in. *)
let rec compile_structure env vmtab mp res struc =
  let fold (env, vmtab, accu) (lab, sfb) = match sfb with
  | SFBconst cb ->
    let c = constant_of_delta_kn res (KerName.make mp lab) in
    let vmtab, cb = compile_constant_bytecode env vmtab cb in
    Environ.add_constant c cb env, vmtab, (lab, SFBconst cb) :: accu
  | SFBmind mib ->
    let mind = mind_of_delta_kn res (KerName.make mp lab) in
    Environ.add_mind mind mib env, vmtab, (lab, sfb) :: accu
  | SFBmodule mb ->
    let mp = MPdot (mp, lab) in
    let vmtab, mb = compile_module_bytecode env vmtab mp mb in
    add_module mp mb env, vmtab, (lab, SFBmodule mb) :: accu
  | SFBmodtype mtb ->
    let mp = MPdot (mp, lab) in
    let vmtab, mtb = compile_module_bytecode env vmtab mp mtb in
    Environ.add_modtype mp mtb env, vmtab, (lab, SFBmodtype mtb) :: accu
  | SFBrules rrb ->
    Environ.add_rewrite_rules rrb.rewrules_rules env, vmtab, (lab, sfb) :: accu
  in
  let (_ : env), vmtab, accu = List.fold_left fold (env, vmtab, []) struc in
  vmtab, List.rev accu

and compile_signature env vmtab mp res = function
  | MoreFunctor (arg_id, mtb, body) ->
    let vmtab, mtb = compile_module_bytecode env vmtab (MPbound arg_id) mtb in
    let env = add_module_parameter arg_id mtb env in
    let vmtab, body = compile_signature env vmtab mp res body in
    vmtab, MoreFunctor (arg_id, mtb, body)
  | NoFunctor struc ->
    let vmtab, struc = compile_structure env vmtab mp res struc in
    vmtab, NoFunctor struc

and compile_module_bytecode : 'a. env -> Vmlibrary.t -> ModPath.t ->
  'a generic_module_body -> Vmlibrary.t * 'a generic_module_body =
  fun env vmtab mp mb ->
  let vmtab, sign = compile_signature env vmtab mp (mod_delta mb) (mod_type mb) in
  vmtab, set_signature sign mb

(** {6 Strengthening a signature for subtyping } *)

let strengthen_const mp_from l cb resolver =
  match cb.const_body with
  | Def _ -> cb
  | _ ->
    let kn = KerName.make mp_from l in
    let con = constant_of_delta_kn resolver kn in
    let u = UVars.make_abstract_instance (Declareops.constant_polymorphic_context cb) in
      { cb with
        const_body = Def (mkConstU (con,u));
        const_body_code = Vmbytegen.compile_alias con }

let rec strengthen_module mp mb = match mod_type mb with
| NoFunctor struc ->
  let delta_mb = get_global_delta mb in
  if mp_is_alias delta_mb mp then mb (* already strengthened *)
  else
    let reso, struc' = strengthen_signature mp struc delta_mb in
    let reso = lift_mp_delta_resolver mp (add_delta_resolver delta_mb reso) in
    strengthen_module_body ~src:mp (NoFunctor struc') reso mb
| MoreFunctor _ -> mb

and strengthen_signature : type a.
  ModPath.t -> structure_body -> a delta_resolver ->
    mod_body delta_resolver * structure_body =
  fun mp struc reso0 ->
  let strengthen_field reso item = match item with
  | (l, SFBconst cb) ->
    reso, (l, SFBconst (strengthen_const mp l cb reso0))
  | (l, SFBmodule mb) ->
    let mp' = MPdot (mp, l) in
    let mb' = strengthen_module mp' mb in
    let reso = match mod_global_delta mb with
    | None ->
      (* See {!strengthen_and_subst_module} *)
      lift_mp_delta_resolver mp' reso
    | Some delta ->
      add_delta_resolver delta reso
    in
    reso, (l, SFBmodule mb')
  | (_, (SFBmind _ | SFBrules _ | SFBmodtype _)) ->
    reso, item
  in
  List.fold_left_map strengthen_field (empty_delta_resolver mp) struc

let strengthen mtb mp = match mod_type mtb with
| NoFunctor struc ->
  let delta_mtb = get_global_delta mtb in
  (* Has mtb already been strengthened ? *)
  if mp_is_alias delta_mtb mp then mtb
  else
    let reso', struc' = strengthen_signature mp struc delta_mtb in
    let reso' = add_delta_resolver delta_mtb (of_body_delta_resolver (lift_mp_delta_resolver mp reso')) in
    strengthen_module_type struc' reso' mtb
| MoreFunctor _ -> mtb

(** Aliasing of a module depending on the nature of the target.

    [Module M := P] makes [M] another name for [P], so the resolver records the
    full equivalence [M ↦ P].

    [Include P] within a module [M] must never record an equivalence keyed on
    [M]. [M] is not [P], it receives the fields of [P] but may be extended with
    further fields later on which should not be aliased with [M] at the risk
    of inconsistency. We must further refine the situation in two cases.
    If [P] is a ground module, paths [P.l] are valid and aliasing can refer to
    them. If [P] is a functor application, it is a transient object which does
    not exist in the environment. Aliasing cannot refer to the source fields,
    i.e. we adopt a generative semantics. *)
type aliasing =
| AliasDef (** Case [Module M := P] *)
| AliasIncl of bool (** Case [Include P], the boolean is true when [P] ground *)

(** {6 Strengthening a module for [Module M := M'] or [Include M] } *)

let rec strengthen_and_subst_module mb subst mp_from mp_to =
  match mod_type mb with
  | NoFunctor struc ->
    let delta_mb = get_global_delta mb in
    let mb_is_an_alias = mp_is_alias delta_mb mp_from in
    if mb_is_an_alias then
      subst_module subst_dom_codom subst mp_from mb
    else
      let reso',struc' =
        strengthen_and_subst_struct struc subst
          mp_from mp_to false AliasDef delta_mb
      in
      (* Don't forget to add the original resolver up to substitution *)
      let reso' = add_delta_resolver (subst_dom_delta_resolver mp_from mp_to delta_mb) (add_mp_delta_resolver mp_to mp_from reso') in
      strengthen_module_body ~src:mp_from (NoFunctor struc') reso' mb
  | MoreFunctor _ ->
    let subst = add_mp mp_from mp_to (empty_delta_resolver mp_to) subst in
    subst_module subst_dom_codom subst mp_from mb

and strengthen_and_subst_struct struc subst mp_from mp_to alias incl reso =
  (* Relate the field [l] of the copy to the field of the source. *)
  let include_field accu l = match incl with
  | AliasDef ->
    (* Already a consequence of the alias [mp_from ↦ mp_to] *)
    accu
  | AliasIncl ground ->
    (* Add per-field aliases as the parent module doesn't have the global one *)
    let kn_from = KerName.make mp_from l in
    let kn_to = KerName.make mp_to l in
    let kn_canonical = kn_of_delta reso kn_from in
    if ground then
      (* Pick the canonical name of the actual object [kn_from]. *)
      if KerName.equal kn_to kn_canonical then
        (* This only happens for Include Self and will fail later with a duplicate label error. *)
        accu
      else add_kn_delta_resolver kn_to kn_canonical accu
    else
      (* [kn_from] is a transient name that only exists locally *)
      let kn_canonical = subst_kn subst kn_canonical in
      (* TODO: we should have a more robust check *)
      if KerName.equal kn_to kn_canonical then accu
      else add_kn_delta_resolver kn_to kn_canonical accu
  in
  let strengthen_and_subst_field reso' item = match item with
    | (l,SFBconst cb) ->
        let cb' = subst_const_body subst cb in
        let cb' =
          if alias then (* optimization *) cb'
          else strengthen_const mp_from l cb' reso
        in
        let item' = if cb' == cb then item else (l, SFBconst cb') in
        include_field reso' l, item'
    | (l,SFBmind mib) ->
        let mib' = subst_mind_body subst mib in
        let item' = if mib' == mib then item else (l, SFBmind mib') in
        (* Same as constant *)
        include_field reso' l, item'
    | (l, SFBrules rrb) ->
        let rrb' = subst_rewrite_rules subst rrb in
        let item' = if rrb' == rrb then item else (l, SFBrules rrb') in
        (* Same as constant *)
        include_field reso' l, item'
    | (l,SFBmodule mb) ->
        let mp_from' = MPdot (mp_from,l) in
        let mp_to' = MPdot (mp_to,l) in
        let mb' = if alias then
          subst_module subst_dom_codom subst mp_from' mb
        else
          strengthen_and_subst_module mb subst mp_from' mp_to'
        in
        let item' = if mb' == mb then item else (l, SFBmodule mb') in
        (* if mb is a functor we should not derive new equivalences
           on names, hence we add the fact that the functor can only
           be equivalent to itself. If we adopt an applicative
           semantic for functor this should be changed.*)
        begin match mod_global_delta mb' with
        | None -> (* functor case *)
          lift_mp_delta_resolver mp_to' reso', item'
        | Some delta ->
          add_delta_resolver delta reso', item'
        end
    | (l,SFBmodtype mty) ->
        let mp_from' = MPdot (mp_from,l) in
        let mp_to' = MPdot(mp_to,l) in
        let subst' = add_mp mp_from' mp_to' (empty_delta_resolver mp_to') subst in
        let mty' = subst_modtype subst_dom_codom subst' mp_from' mty in
        let item' = if mty' == mty then item else (l, SFBmodtype mty') in
        lift_mp_delta_resolver mp_to' reso', item'
  in
  List.Smart.fold_left_map strengthen_and_subst_field (empty_delta_resolver mp_to) struc

(** [include_applied_structure mp_from struc reso mp] includes into [mp] the
    result of a functor application, which {!Mod_typing} has elaborated at the
    functor's own path [mp_from]. Nothing is strengthened, as there is no module
    at [mp_from]. *)
let include_applied_structure mp_from struc reso mp =
  (* [reso] may record an equivalence for [mp_from], saying where the fields of
     the application really live -- that is how [Module F (X : T) := X] reports
     that applying [F] yields the argument. α-renamed onto [mp] it is what gives
     the copied names their canonical form, so it belongs in the substitution;
     it must not reach the resolver we return, which is [mp]'s. *)
  let subst =
    map_mp mp_from mp
      (of_body_delta_resolver (subst_dom_delta_resolver mp_from mp reso))
  in
  let reso', struc' =
    strengthen_and_subst_struct struc subst mp_from mp true (AliasIncl false) reso
  in
  struc', reso'

(** Let P be a module path when we write:
     "Module M:=P." or "Module M. Include P. End M."
    We need to perform two operations to compute the body of M.
    - The first one is applying the substitution {P <- M} on the type of P, i.e.
      to replace any expression in P referring to P itself by the same
      expression referring instead to M
    - The second one is strengthening, i.e. associating to each
      abstract/opaque field t in P a defined field t := Q.t where Q is the
      Delta-normal form of P (possibly P itself):
      - in the alias case "Module M:=P." where "P" is already an alias
        with canonical form "Q": add the module Delta-equivalence "M := Q"
      - in the alias case where P is not itself an alias:
        add the module Delta-equivalence "M := P"
      - in the "Include" case: add a Delta-equivalence "t := t'" where
        "t'" is the canonical form of "P.t" on each field *)

let strengthen_and_subst_module_body mp_from mb mp include_b = match mod_type mb with
  | NoFunctor struc ->
    let delta_mb = get_global_delta mb in
    let mb_is_an_alias = mp_is_alias delta_mb mp_from in
    (* if mb.mod_mp is an alias then the strengthening is useless
       (i.e. it is already done)*)
    let mp_alias = mp_of_delta delta_mb mp_from in
    let new_resolver =
      let dom = subst_dom_delta_resolver mp_from mp delta_mb in
      if ModPath.equal mp mp_alias then
        (* This only happens for Include Self and will fail later with a duplicate label error. *)
        dom
      else add_mp_delta_resolver mp mp_alias dom
    in
    let subst = map_mp mp_from mp (of_body_delta_resolver new_resolver) in
    let reso',struc' =
      strengthen_and_subst_struct struc subst
        mp_from mp mb_is_an_alias (if include_b then AliasIncl true else AliasDef) delta_mb
    in
    let reso' = if include_b then reso' else add_delta_resolver new_resolver reso' in
    strengthen_module_body ~src:mp_from (NoFunctor struc') reso' mb
  | MoreFunctor _ ->
    (* Functor inclusion is handled by [Mod_typing]. *)
    let () = assert (not include_b) in
    let subst = map_mp mp_from mp (empty_delta_resolver mp) in
    Mod_declarations.subst_module subst_dom_codom subst mp_from mb

(* [mp_from] is the ambient modpath of [sign] *)
let subst_modtype_signature_and_resolver mp_from mp_to sign reso =
  let subst = map_mp mp_from mp_to (empty_delta_resolver mp_to) in
  Mod_declarations.subst_signature subst_dom_codom subst mp_from sign, subst_dom_codom_delta_resolver subst reso

let rec collect_mbid l sign =  match sign with
  | MoreFunctor (mbid,ty,m) ->
    let m' = collect_mbid (MBId.Set.add mbid l) m in
    if m==m' then sign else MoreFunctor (mbid,ty,m')
  | NoFunctor struc ->
    let struc' = clean_structure l struc in
    if struc==struc' then sign else NoFunctor struc'

let clean_bounded_mod_expr sign =
  if is_functor sign then collect_mbid MBId.Set.empty sign else sign

(** {6 Building map of constants to inline } *)

(* The result carries inlined bodies, so it is a substitution resolver; the
   [delta] it starts from is the resolver of the module being passed. *)
let inline_delta_resolver env inl mp mbid mtb delta =
  let constants = inline_of_delta inl (mod_delta mtb) in
  let rec make_inline delta = function
    | [] -> delta
    | kn :: r ->
      let kn = replace_mp_in_kn (MPbound mbid) mp kn in
      let con = constant_of_delta_kn delta kn in
      if not (Environ.mem_constant con env) then
        error_no_such_label_sub (Constant.label con)
          (ModPath.to_string (Constant.modpath con))
      else
        let constant = lookup_constant con env in
        let l = make_inline delta r in
        match constant.const_body with
        | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> l
        | Def constr ->
          let ctx = Declareops.constant_polymorphic_context constant in
          let constr = {UVars.univ_abstracted_value=constr; univ_abstracted_binder=ctx} in
          add_inline_body_delta_resolver kn constr l
  in
  make_inline (forget_inline_delta_resolver delta) constants
