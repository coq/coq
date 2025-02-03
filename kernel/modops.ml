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
  | NotConvertibleInductiveField of Id.t
  | NotConvertibleConstructorField of Id.t
  | NotConvertibleBodyField
  | NotConvertibleTypeField of env * types * types
  | CumulativeStatusExpected of bool
  | PolymorphicStatusExpected of bool
  | NotSameConstructorNamesField
  | NotSameInductiveNameInBlockField
  | FiniteInductiveFieldExpected of bool
  | InductiveNumbersFieldExpected of int
  | InductiveParamsNumberField of int
  | RecordFieldExpected of bool
  | RecordProjectionsExpected of Name.t list
  | NotEqualInductiveAliases
  | IncompatibleUniverses of UGraph.univ_inconsistency
  | IncompatiblePolymorphism of env * types * types
  | IncompatibleConstraints of { got : UVars.AbstractContext.t; expect : UVars.AbstractContext.t }
  | IncompatibleVariance
  | NoRewriteRulesSubtyping

type subtyping_trace_elt =
  | Submodule of Label.t
  | FunctorArgument of int

type module_typing_error =
  | SignatureMismatch of subtyping_trace_elt list * Label.t * signature_mismatch_error
  | LabelAlreadyDeclared of Label.t
  | NotAFunctor
  | IsAFunctor of ModPath.t
  | IncompatibleModuleTypes of module_type_body * module_type_body
  | NotEqualModulePaths of ModPath.t * ModPath.t
  | NoSuchLabel of Label.t * ModPath.t
  | NotAModuleLabel of Label.t
  | NotAConstant of Label.t
  | IncorrectWithConstraint of Label.t
  | GenerativeModuleExpected of Label.t
  | LabelMissing of Label.t * string
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

let error_incorrect_with_constraint l =
  raise (ModuleTypingError (IncorrectWithConstraint l))

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

let module_type_of_module = Mod_declarations.module_type_of_module
let module_body_of_type = Mod_declarations.module_body_of_type

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

let rec add_structure mp sign resolver linkinfo env =
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
      Environ.add_mind_key mind (mib,ref linkinfo) env
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
    add_retroknowledge (mod_retroknowledge mb)
      (add_structure mp struc delta linkinfo env)
  | MoreFunctor _ -> env

let add_linked_module mp mb linkinfo env =
  add_module mp mb linkinfo env

let add_structure mp sign resolver env =
  add_structure mp sign resolver no_link_info env

let add_module mp mb env =
  add_module mp mb no_link_info env

let add_module_parameter mbid mtb env =
  add_module (MPbound mbid) (module_body_of_type mtb) env

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
        const_body_code = Some (Vmbytegen.compile_alias con) }

let rec strengthen_module mp mb = match mod_type mb with
| NoFunctor struc ->
  let delta_mb = get_global_delta mb in
  if mp_in_delta mp delta_mb then mb
  else
    let reso, struc' = strengthen_signature mp struc delta_mb in
    let reso = add_mp_delta_resolver mp mp (add_delta_resolver delta_mb reso) in
    strengthen_module_body ~src:mp (NoFunctor struc') reso mb
| MoreFunctor _ -> mb

and strengthen_signature mp struc reso0 =
  let strengthen_field reso item = match item with
  | (l, SFBconst cb) ->
    reso, (l, SFBconst (strengthen_const mp l cb reso0))
  | (l, SFBmodule mb) ->
    let mp' = MPdot (mp, l) in
    let mb' = strengthen_module mp' mb in
    let reso = match mod_global_delta mb with
    | None ->
      (* See {!strengthen_and_subst_module} *)
      add_mp_delta_resolver mp' mp' reso
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
  if mp_in_delta mp delta_mtb then mtb
  else
    let reso', struc' = strengthen_signature mp struc delta_mtb in
    let reso' = add_delta_resolver delta_mtb (add_mp_delta_resolver mp mp reso') in
    strengthen_module_type struc' reso' mtb
| MoreFunctor _ -> mtb

(** {6 Strengthening a module for [Module M := M'] or [Include M] } *)

let rec strengthen_and_subst_module mb subst mp_from mp_to =
  match mod_type mb with
  | NoFunctor struc ->
    let delta_mb = get_global_delta mb in
    let mb_is_an_alias = mp_in_delta mp_from delta_mb in
    if mb_is_an_alias then subst_module subst_dom subst mp_from mb
    else
      let reso',struc' =
        strengthen_and_subst_struct struc subst
          mp_from mp_to false false delta_mb
      in
      let reso' = add_mp_delta_resolver mp_to mp_from reso' in
      strengthen_module_body ~src:mp_from (NoFunctor struc') reso' mb
  | MoreFunctor _ ->
    let subst = add_mp mp_from mp_to (empty_delta_resolver mp_to) subst in
    subst_module subst_dom subst mp_from mb

and strengthen_and_subst_struct struc subst mp_from mp_to alias incl reso =
  let strengthen_and_subst_field reso' item = match item with
    | (l,SFBconst cb) ->
        let cb' = subst_const_body subst cb in
        let cb' =
          if alias then (* optimization *) cb'
          else strengthen_const mp_from l cb' reso
        in
        let item' = if cb' == cb then item else (l, SFBconst cb') in
        if incl then
          (* If we are performing an inclusion we need to add
             the fact that the constant mp_to.l is \Delta-equivalent
             to reso(mp_from.l) *)
          let kn_from = KerName.make mp_from l in
          let kn_to = KerName.make mp_to l in
          let kn_canonical = kn_of_delta reso kn_from in
          add_kn_delta_resolver kn_to kn_canonical reso', item'
        else
          (* In this case the fact that the constant mp_to.l is
             \Delta-equivalent to resolver(mp_from.l) is already known
             because reso' contains mp_to maps to reso(mp_from) *)
          reso', item'
    | (l,SFBmind mib) ->
        let mib' = subst_mind_body subst mib in
        let item' = if mib' == mib then item else (l, SFBmind mib') in
        (* Same as constant *)
        if incl then
          let kn_from = KerName.make mp_from l in
          let kn_to = KerName.make mp_to l in
          let kn_canonical = kn_of_delta reso kn_from in
          add_kn_delta_resolver kn_to kn_canonical reso', item'
        else
          reso', item'
    | (l, SFBrules rrb) ->
        let rrb' = subst_rewrite_rules subst rrb in
        let item' = if rrb' == rrb then item else (l, SFBrules rrb') in
        (* Same as constant *)
        if incl then
          let kn_from = KerName.make mp_from l in
          let kn_to = KerName.make mp_to l in
          let kn_canonical = kn_of_delta reso kn_from in
          add_kn_delta_resolver kn_to kn_canonical reso', item'
        else
          reso', item'
    | (l,SFBmodule mb) ->
        let mp_from' = MPdot (mp_from,l) in
        let mp_to' = MPdot (mp_to,l) in
        let mb' = if alias then
          subst_module subst_dom subst mp_from' mb
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
          add_mp_delta_resolver mp_to' mp_to' reso', item'
        | Some delta ->
          add_delta_resolver delta reso', item'
        end
    | (l,SFBmodtype mty) ->
        let mp_from' = MPdot (mp_from,l) in
        let mp_to' = MPdot(mp_to,l) in
        let subst' = add_mp mp_from' mp_to' (empty_delta_resolver mp_to') subst in
        let mty' = subst_modtype (subst_shallow_dom_codom subst') subst' mp_from' mty in
        let item' = if mty' == mty then item else (l, SFBmodtype mty') in
        add_mp_delta_resolver mp_to' mp_to' reso', item'
  in
  List.Smart.fold_left_map strengthen_and_subst_field (empty_delta_resolver mp_to) struc

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
    let mb_is_an_alias = mp_in_delta mp_from delta_mb in
    (* if mb.mod_mp is an alias then the strengthening is useless
       (i.e. it is already done)*)
    let mp_alias = mp_of_delta delta_mb mp_from in
    let subst_resolver = map_mp mp_from mp (empty_delta_resolver mp) in
    let new_resolver =
      add_mp_delta_resolver mp mp_alias
        (subst_dom_delta_resolver subst_resolver delta_mb)
    in
    let subst = map_mp mp_from mp new_resolver in
    let reso',struc' =
      strengthen_and_subst_struct struc subst
        mp_from mp mb_is_an_alias include_b delta_mb
    in
    let reso' = if include_b then reso' else add_delta_resolver new_resolver reso' in
    strengthen_module_body ~src:mp_from (NoFunctor struc') reso' mb
  | MoreFunctor _ ->
    let subst = map_mp mp_from mp (empty_delta_resolver mp) in
    Mod_declarations.subst_module subst_dom_codom subst mp_from mb

(* [mp_from] is the ambient modpath of [sign] *)
let subst_modtype_signature_and_resolver mp_from mp_to sign reso =
  let subst = map_mp mp_from mp_to (empty_delta_resolver mp_to) in
  Mod_declarations.subst_signature subst_dom_codom subst mp_from sign, subst_dom_codom_delta_resolver subst reso

let rec collect_mbid l sign =  match sign with
  | MoreFunctor (mbid,ty,m) ->
    let m' = collect_mbid (MBIset.add mbid l) m in
    if m==m' then sign else MoreFunctor (mbid,ty,m')
  | NoFunctor struc ->
    let struc' = clean_structure l struc in
    if struc==struc' then sign else NoFunctor struc'

let clean_bounded_mod_expr sign =
  if is_functor sign then collect_mbid MBIset.empty sign else sign

(** {6 Building map of constants to inline } *)

let inline_delta_resolver env inl mp mbid mtb delta =
  let constants = inline_of_delta inl (mod_delta mtb) in
  let rec make_inline delta = function
    | [] -> delta
    | (lev,kn)::r ->
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
          add_inline_delta_resolver kn (lev, Some constr) l
  in
  make_inline delta constants
