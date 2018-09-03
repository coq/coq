(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre as part of the rebuilding of
   Coq around a purely functional abstract type-checker, Dec 1999 *)

(* This file provides the entry points to the kernel type-checker. It
   defines the abstract type of well-formed environments and
   implements the rules that build well-formed environments.

   An environment is made of constants and inductive types (E), of
   section declarations (Delta), of local bound-by-index declarations
   (Gamma) and of universe constraints (C). Below E[Delta,Gamma] |-_C
   means that the tuple E, Delta, Gamma, C is a well-formed
   environment. Main rules are:

   empty_environment:

     ------
     [,] |-

   push_named_assum(a,T):

     E[Delta,Gamma] |-_G
     ------------------------
     E[Delta,Gamma,a:T] |-_G'

   push_named_def(a,t,T):

     E[Delta,Gamma] |-_G
     ---------------------------
     E[Delta,Gamma,a:=t:T] |-_G'

   add_constant(ConstantEntry(DefinitionEntry(c,t,T))):

     E[Delta,Gamma] |-_G
     ---------------------------
     E,c:=t:T[Delta,Gamma] |-_G'

   add_constant(ConstantEntry(ParameterEntry(c,T))):

     E[Delta,Gamma] |-_G
     ------------------------
     E,c:T[Delta,Gamma] |-_G'

   add_mind(Ind(Ind[Gamma_p](Gamma_I:=Gamma_C))):

     E[Delta,Gamma] |-_G
     ------------------------
     E,Ind[Gamma_p](Gamma_I:=Gamma_C)[Delta,Gamma] |-_G'

   etc.
*)

open CErrors
open Util
open Names
open Declarations
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

(** {6 Safe environments }

  Fields of [safe_environment] :

  - [env] : the underlying environment (cf Environ)
  - [modpath] : the current module name
  - [modvariant] :
    * NONE before coqtop initialization
    * LIBRARY at toplevel of a compilation or a regular coqtop session
    * STRUCT (params,oldsenv) : inside a local module, with
      module parameters [params] and earlier environment [oldsenv]
    * SIG (params,oldsenv) : same for a local module type
  - [modresolver] : delta_resolver concerning the module content
  - [paramresolver] : delta_resolver concerning the module parameters
  - [revstruct] : current module content, most recent declarations first
  - [modlabels] and [objlabels] : names defined in the current module,
      either for modules/modtypes or for constants/inductives.
      These fields could be deduced from [revstruct], but they allow faster
      name freshness checks.
 - [univ] and [future_cst] : current and future universe constraints
 - [engagement] : are we Set-impredicative? does the universe hierarchy collapse?
 - [required] : names and digests of Require'd libraries since big-bang.
      This field will only grow
 - [loads] : list of libraries Require'd inside the current module.
      They will be propagated to the upper module level when
      the current module ends.
 - [local_retroknowledge]

*)

type vodigest =
  | Dvo_or_vi of Digest.t        (* The digest of the seg_lib part *)
  | Dvivo of Digest.t * Digest.t (* The digest of the seg_lib + seg_univ part *)

let digest_match ~actual ~required =
  match actual, required with
  | Dvo_or_vi d1, Dvo_or_vi d2
  | Dvivo (d1,_), Dvo_or_vi d2 -> String.equal d1 d2
  | Dvivo (d1,e1), Dvivo (d2,e2) -> String.equal d1 d2 && String.equal e1 e2
  | Dvo_or_vi _, Dvivo _ -> false

type library_info = DirPath.t * vodigest

(** Functor and funsig parameters, most recent first *)
type module_parameters = (MBId.t * module_type_body) list

module DPMap = Map.Make(DirPath)

type safe_environment =
  { env : Environ.env;
    modpath : ModPath.t;
    modvariant : modvariant;
    modresolver : Mod_subst.delta_resolver;
    paramresolver : Mod_subst.delta_resolver;
    revstruct : structure_body;
    modlabels : Label.Set.t;
    objlabels : Label.Set.t;
    univ : Univ.ContextSet.t;
    future_cst : Univ.ContextSet.t Future.computation list;
    engagement : engagement option;
    required : vodigest DPMap.t;
    loads : (ModPath.t * module_body) list;
    local_retroknowledge : Retroknowledge.action list;
    native_symbols : Nativecode.symbols DPMap.t }

and modvariant =
  | NONE
  | LIBRARY
  | SIG of module_parameters * safe_environment (** saved env *)
  | STRUCT of module_parameters * safe_environment (** saved env *)

let rec library_dp_of_senv senv =
  match senv.modvariant with
  | NONE | LIBRARY -> ModPath.dp senv.modpath
  | SIG(_,senv) -> library_dp_of_senv senv
  | STRUCT(_,senv) -> library_dp_of_senv senv

let empty_environment =
  { env = Environ.empty_env;
    modpath = ModPath.initial;
    modvariant = NONE;
    modresolver = Mod_subst.empty_delta_resolver;
    paramresolver = Mod_subst.empty_delta_resolver;
    revstruct = [];
    modlabels = Label.Set.empty;
    objlabels = Label.Set.empty;
    future_cst = [];
    univ = Univ.ContextSet.empty;
    engagement = None;
    required = DPMap.empty;
    loads = [];
    local_retroknowledge = [];
    native_symbols = DPMap.empty }

let is_initial senv =
  match senv.revstruct, senv.modvariant with
  | [], NONE -> ModPath.equal senv.modpath ModPath.initial
  | _ -> false

let delta_of_senv senv = senv.modresolver,senv.paramresolver

(** The safe_environment state monad *)

type safe_transformer0 = safe_environment -> safe_environment
type 'a safe_transformer = safe_environment -> 'a * safe_environment


(** {6 Engagement } *)

let set_engagement_opt env = function
  | Some c -> Environ.set_engagement c env
  | None -> env

let set_engagement c senv =
  { senv with
    env = Environ.set_engagement c senv.env;
    engagement = Some c }

let set_typing_flags c senv =
  { senv with env = Environ.set_typing_flags c senv.env }

(** Check that the engagement [c] expected by a library matches
    the current (initial) one *)
let check_engagement env expected_impredicative_set =
  let impredicative_set = Environ.engagement env in
  begin
    match impredicative_set, expected_impredicative_set with
    | PredicativeSet, ImpredicativeSet ->
        CErrors.user_err Pp.(str "Needs option -impredicative-set.")
    | _ -> ()
  end

(** {6 Stm machinery } *)

let get_opaque_body env cbo =
  match cbo.const_body with
  | Undef _ -> assert false
  | Def _ -> `Nothing
  | OpaqueDef opaque ->
      `Opaque
        (Opaqueproof.force_proof (Environ.opaque_tables env) opaque,
         Opaqueproof.force_constraints (Environ.opaque_tables env) opaque)

type private_constants = Term_typing.side_effects

let empty_private_constants = Term_typing.empty_seff
let add_private = Term_typing.add_seff
let concat_private = Term_typing.concat_seff
let mk_pure_proof = Term_typing.mk_pure_proof
let inline_private_constants_in_constr = Term_typing.inline_side_effects
let inline_private_constants_in_definition_entry = Term_typing.inline_entry_side_effects
let side_effects_of_private_constants = Term_typing.uniq_seff

let make_eff env cst r =
  let open Entries in
  let cbo = Environ.lookup_constant cst env.env in
  {
    seff_constant = cst;
    seff_body = cbo;
    seff_env = get_opaque_body env.env cbo;
    seff_role = r;
  }

let private_con_of_con env c =
  let open Entries in
  let eff = [make_eff env c Subproof] in
  add_private env.revstruct eff empty_private_constants

let private_con_of_scheme ~kind env cl =
  let open Entries in
  let eff = List.map (fun (i, c) -> make_eff env c (Schema (i, kind))) cl in
  add_private env.revstruct eff empty_private_constants

let universes_of_private eff =
  let open Entries in
  let fold acc eff =
    let acc = match eff.seff_env with
    | `Nothing -> acc
    | `Opaque (_, ctx) -> ctx :: acc
    in
    match eff.seff_body.const_universes with
    | Monomorphic_const ctx -> ctx :: acc
    | Polymorphic_const _ -> acc
  in
  List.fold_left fold [] (Term_typing.uniq_seff eff)

let env_of_safe_env senv = senv.env
let env_of_senv = env_of_safe_env

type constraints_addition =
  | Now of bool * Univ.ContextSet.t
  | Later of Univ.ContextSet.t Future.computation

let add_constraints cst senv =
  match cst with
  | Later fc -> 
    {senv with future_cst = fc :: senv.future_cst}
  | Now (poly,cst) ->
  { senv with
    env = Environ.push_context_set ~strict:(not poly) cst senv.env;
    univ = Univ.ContextSet.union cst senv.univ }

let add_constraints_list cst senv =
  List.fold_left (fun acc c -> add_constraints c acc) senv cst

let push_context_set poly ctx = add_constraints (Now (poly,ctx))
let push_context poly ctx = add_constraints (Now (poly,Univ.ContextSet.of_context ctx))

let is_curmod_library senv =
  match senv.modvariant with LIBRARY -> true | _ -> false

let join_safe_environment ?(except=Future.UUIDSet.empty) e =
  Modops.join_structure except (Environ.opaque_tables e.env) e.revstruct;
  List.fold_left
    (fun e fc ->
       if Future.UUIDSet.mem (Future.uuid fc) except then e
       else add_constraints (Now (false, Future.join fc)) e)
    {e with future_cst = []} e.future_cst

let is_joined_environment e = List.is_empty e.future_cst 

(** {6 Various checks } *)

let exists_modlabel l senv = Label.Set.mem l senv.modlabels
let exists_objlabel l senv = Label.Set.mem l senv.objlabels

let check_modlabel l senv =
  if exists_modlabel l senv then Modops.error_existing_label l

let check_objlabel l senv =
  if exists_objlabel l senv then Modops.error_existing_label l

let check_objlabels ls senv =
  Label.Set.iter (fun l -> check_objlabel l senv) ls

(** Are we closing the right module / modtype ?
    No user error here, since the opening/ending coherence
    is now verified in [vernac_end_segment] *)

let check_current_label lab = function
  | MPdot (_,l) -> assert (Label.equal lab l)
  | _ -> assert false

let check_struct = function
  | STRUCT (params,oldsenv) -> params, oldsenv
  | NONE | LIBRARY | SIG _ -> assert false

let check_sig = function
  | SIG (params,oldsenv) -> params, oldsenv
  | NONE | LIBRARY | STRUCT _ -> assert false

let check_current_library dir senv = match senv.modvariant with
  | LIBRARY -> assert (ModPath.equal senv.modpath (MPfile dir))
  | NONE | STRUCT _ | SIG _ -> assert false (* cf Lib.end_compilation *)

(** When operating on modules, we're normally outside sections *)

let check_empty_context senv =
  assert (Environ.empty_context senv.env)

(** When adding a parameter to the current module/modtype,
    it must have been freshly started *)

let check_empty_struct senv =
  assert (List.is_empty senv.revstruct
          && List.is_empty senv.loads)

(** When starting a library, the current environment should be initial
    i.e. only composed of Require's *)

let check_initial senv = assert (is_initial senv)

(** When loading a library, its dependencies should be already there,
    with the correct digests. *)

let check_required current_libs needed =
  let check (id,required) =
    try
      let actual = DPMap.find id current_libs in
      if not(digest_match ~actual ~required) then
        CErrors.user_err Pp.(pr_sequence str
          ["Inconsistent assumptions over module"; DirPath.to_string id; "."])
    with Not_found ->
      CErrors.user_err Pp.(pr_sequence str ["Reference to unknown module"; DirPath.to_string id; "."])
  in
  Array.iter check needed


(** {6 Insertion of section variables} *)

(** They are now typed before being added to the environment.
    Same as push_named, but check that the variable is not already
    there. Should *not* be done in Environ because tactics add temporary
    hypothesis many many times, and the check performed here would
    cost too much. *)

let safe_push_named d env =
  let id = NamedDecl.get_id d in
  let _ =
    try
      let _ = Environ.lookup_named id env in
      CErrors.user_err Pp.(pr_sequence str ["Identifier"; Id.to_string id; "already defined."])
    with Not_found -> () in
  Environ.push_named d env


let push_named_def (id,de) senv =
  let c, typ = Term_typing.translate_local_def senv.env id de in
  let env'' = safe_push_named (LocalDef (id, c, typ)) senv.env in
  { senv with env = env'' }

let push_named_assum ((id,t,poly),ctx) senv =
  let senv' = push_context_set poly ctx senv in
  let t = Term_typing.translate_local_assum senv'.env t in
  let env'' = safe_push_named (LocalAssum (id,t)) senv'.env in
    {senv' with env=env''}


(** {6 Insertion of new declarations to current environment } *)

let labels_of_mib mib =
  let add,get =
    let labels = ref Label.Set.empty in
    (fun id -> labels := Label.Set.add (Label.of_id id) !labels),
    (fun () -> !labels)
  in
  let visit_mip mip =
    add mip.mind_typename;
    Array.iter add mip.mind_consnames
  in
  Array.iter visit_mip mib.mind_packets;
  get ()

let globalize_constant_universes env cb =
  match cb.const_universes with
  | Monomorphic_const cstrs ->
    Now (false, cstrs) ::
    (match cb.const_body with
     | (Undef _ | Def _) -> []
     | OpaqueDef lc ->
       match Opaqueproof.get_constraints (Environ.opaque_tables env) lc with
       | None -> []
       | Some fc ->
            match Future.peek_val fc with
             | None -> [Later fc]
             | Some c -> [Now (false, c)])
  | Polymorphic_const _ ->
    [Now (true, Univ.ContextSet.empty)]
      
let globalize_mind_universes mb =
  match mb.mind_universes with
  | Monomorphic_ind ctx ->
    [Now (false, ctx)]
  | Polymorphic_ind _ -> [Now (true, Univ.ContextSet.empty)]
  | Cumulative_ind _ -> [Now (true, Univ.ContextSet.empty)]

let constraints_of_sfb env sfb = 
  match sfb with
  | SFBconst cb -> globalize_constant_universes env cb
  | SFBmind mib -> globalize_mind_universes mib
  | SFBmodtype mtb -> [Now (false, mtb.mod_constraints)]
  | SFBmodule mb -> [Now (false, mb.mod_constraints)]

(** A generic function for adding a new field in a same environment.
    It also performs the corresponding [add_constraints]. *)

type generic_name =
  | C of Constant.t
  | I of MutInd.t
  | M (** name already known, cf the mod_mp field *)
  | MT (** name already known, cf the mod_mp field *)

let add_field ((l,sfb) as field) gn senv =
  let mlabs,olabs = match sfb with
    | SFBmind mib ->
      let l = labels_of_mib mib in
      check_objlabels l senv; (Label.Set.empty,l)
    | SFBconst _ ->
      check_objlabel l senv; (Label.Set.empty, Label.Set.singleton l)
    | SFBmodule _ | SFBmodtype _ ->
      check_modlabel l senv; (Label.Set.singleton l, Label.Set.empty)
  in
  let cst = constraints_of_sfb senv.env sfb in
  let senv = add_constraints_list cst senv in
  let env' = match sfb, gn with
    | SFBconst cb, C con -> Environ.add_constant con cb senv.env
    | SFBmind mib, I mind -> Environ.add_mind mind mib senv.env
    | SFBmodtype mtb, MT -> Environ.add_modtype mtb senv.env
    | SFBmodule mb, M -> Modops.add_module mb senv.env
    | _ -> assert false
  in
  { senv with
    env = env';
    revstruct = field :: senv.revstruct;
    modlabels = Label.Set.union mlabs senv.modlabels;
    objlabels = Label.Set.union olabs senv.objlabels }

(** Applying a certain function to the resolver of a safe environment *)

let update_resolver f senv = { senv with modresolver = f senv.modresolver }

(** Insertion of constants and parameters in environment *)
type 'a effect_entry =
| EffectEntry : private_constants effect_entry
| PureEntry : unit effect_entry

type global_declaration =
  | ConstantEntry : 'a effect_entry * 'a Entries.constant_entry -> global_declaration
  | GlobalRecipe of Cooking.recipe

type exported_private_constant = 
  Constant.t * Entries.side_effect_role

let add_constant_aux no_section senv (kn, cb) =
  let l = pi3 (Constant.repr3 kn) in
  let cb, otab = match cb.const_body with
    | OpaqueDef lc when no_section ->
      (* In coqc, opaque constants outside sections will be stored
         indirectly in a specific table *)
      let od, otab =
        Opaqueproof.turn_indirect
          (library_dp_of_senv senv) lc (Environ.opaque_tables senv.env) in
      { cb with const_body = OpaqueDef od }, otab
    | _ -> cb, (Environ.opaque_tables senv.env)
  in
  let senv = { senv with env = Environ.set_opaque_tables senv.env otab } in
  let senv' = add_field (l,SFBconst cb) (C kn) senv in
  let senv'' = match cb.const_body with
    | Undef (Some lev) ->
      update_resolver
        (Mod_subst.add_inline_delta_resolver (Constant.user kn) (lev,None)) senv'
    | _ -> senv'
  in
  senv''

let export_private_constants ~in_section ce senv =
  let exported, ce = Term_typing.export_side_effects senv.revstruct senv.env ce in
  let bodies = List.map (fun (kn, cb, _) -> (kn, cb)) exported in
  let exported = List.map (fun (kn, _, r) -> (kn, r)) exported in
  let no_section = not in_section in
  let senv = List.fold_left (add_constant_aux no_section) senv bodies in
  (ce, exported), senv

let add_constant dir l decl senv =
  let kn = Constant.make3 senv.modpath dir l in
  let no_section = DirPath.is_empty dir in
  let senv =
    let cb = 
      match decl with
      | ConstantEntry (EffectEntry, ce) ->
        Term_typing.translate_constant (Term_typing.SideEffects senv.revstruct) senv.env kn ce
      | ConstantEntry (PureEntry, ce) ->
        Term_typing.translate_constant Term_typing.Pure senv.env kn ce
      | GlobalRecipe r ->
        let cb = Term_typing.translate_recipe senv.env kn r in
        if no_section then Declareops.hcons_const_body cb else cb in
    add_constant_aux no_section senv (kn, cb) in
  kn, senv

(** Insertion of inductive types *)

let check_mind mie lab =
  let open Entries in
  match mie.mind_entry_inds with
  | [] -> assert false (* empty inductive entry *)
  | oie::_ ->
    (* The label and the first inductive type name should match *)
    assert (Id.equal (Label.to_id lab) oie.mind_entry_typename)

let add_mind dir l mie senv =
  let () = check_mind mie l in
  let kn = MutInd.make3 senv.modpath dir l in
  let mib = Term_typing.translate_mind senv.env kn mie in
  let mib =
    match mib.mind_hyps with [] -> Declareops.hcons_mind mib | _ -> mib
  in
  kn, add_field (l,SFBmind mib) (I kn) senv

(** Insertion of module types *)

let add_modtype l params_mte inl senv =
  let mp = MPdot(senv.modpath, l) in
  let mtb = Mod_typing.translate_modtype senv.env mp inl params_mte  in
  let mtb = Declareops.hcons_module_type mtb in
  let senv' = add_field (l,SFBmodtype mtb) MT senv in
  mp, senv'

(** full_add_module adds module with universes and constraints *)

let full_add_module mb senv =
  let senv = add_constraints (Now (false, mb.mod_constraints)) senv in
  let dp = ModPath.dp mb.mod_mp in
  let linkinfo = Nativecode.link_info_of_dirpath dp in
  { senv with env = Modops.add_linked_module mb linkinfo senv.env }

let full_add_module_type mp mt senv =
  let senv = add_constraints (Now (false, mt.mod_constraints)) senv in
  { senv with env = Modops.add_module_type mp mt senv.env }

(** Insertion of modules *)

let add_module l me inl senv =
  let mp = MPdot(senv.modpath, l) in
  let mb = Mod_typing.translate_module senv.env mp inl me in
  let mb = Declareops.hcons_module_body mb in
  let senv' = add_field (l,SFBmodule mb) M senv in
  let senv'' =
    if Modops.is_functor mb.mod_type then senv'
    else update_resolver (Mod_subst.add_delta_resolver mb.mod_delta) senv'
  in
  (mp,mb.mod_delta),senv''


(** {6 Starting / ending interactive modules and module types } *)

let start_module l senv =
  let () = check_modlabel l senv in
  let () = check_empty_context senv in
  let mp = MPdot(senv.modpath, l) in
  mp,
  { empty_environment with
    env = senv.env;
    modpath = mp;
    modvariant = STRUCT ([],senv);
    required = senv.required }

let start_modtype l senv =
  let () = check_modlabel l senv in
  let () = check_empty_context senv in
  let mp = MPdot(senv.modpath, l) in
  mp,
  { empty_environment with
    env = senv.env;
    modpath = mp;
    modvariant = SIG ([], senv);
    required = senv.required }

(** Adding parameters to the current module or module type.
    This module should have been freshly started. *)

let add_module_parameter mbid mte inl senv =
  let () = check_empty_struct senv in
  let mp = MPbound mbid in
  let mtb = Mod_typing.translate_modtype senv.env mp inl ([],mte) in
  let senv = full_add_module_type mp mtb senv in
  let new_variant = match senv.modvariant with
    | STRUCT (params,oldenv) -> STRUCT ((mbid,mtb) :: params, oldenv)
    | SIG (params,oldenv) -> SIG ((mbid,mtb) :: params, oldenv)
    | _ -> assert false
  in
  let new_paramresolver =
    if Modops.is_functor mtb.mod_type then senv.paramresolver
    else Mod_subst.add_delta_resolver mtb.mod_delta senv.paramresolver
  in
  mtb.mod_delta,
  { senv with
    modvariant = new_variant;
    paramresolver = new_paramresolver }

let functorize params init =
  List.fold_left (fun e (mbid,mt) -> MoreFunctor(mbid,mt,e)) init params

let propagate_loads senv =
  List.fold_left
    (fun env (_,mb) -> full_add_module mb env)
    senv
    (List.rev senv.loads)

(** Build the module body of the current module, taking in account
    a possible return type (_:T) *)

let functorize_module params mb =
  let f x = functorize params x in
  { mb with
    mod_expr = Modops.implem_smartmap f f mb.mod_expr;
    mod_type = f mb.mod_type;
    mod_type_alg = Option.map f mb.mod_type_alg }

let build_module_body params restype senv =
  let struc = NoFunctor (List.rev senv.revstruct) in
  let restype' = Option.map (fun (ty,inl) -> (([],ty),inl)) restype in
  let mb =
    Mod_typing.finalize_module senv.env senv.modpath
      (struc,None,senv.modresolver,senv.univ) restype'
  in
  let mb' = functorize_module params mb in
  { mb' with mod_retroknowledge = ModBodyRK senv.local_retroknowledge }

(** Returning back to the old pre-interactive-module environment,
    with one extra component and some updated fields
    (constraints, required, etc) *)

let allow_delayed_constants = ref false

let propagate_senv newdef newenv newresolver senv oldsenv =
  let now_cst, later_cst = List.partition Future.is_val senv.future_cst in
  (* This asserts that after Paral-ITP, standard vo compilation is behaving
   * exctly as before: the same universe constraints are added to modules *)
  if not !allow_delayed_constants && later_cst <> [] then
    CErrors.anomaly ~label:"safe_typing"
      Pp.(str "True Future.t were created for opaque constants even if -async-proofs is off");
  { oldsenv with
    env = newenv;
    modresolver = newresolver;
    revstruct = newdef::oldsenv.revstruct;
    modlabels = Label.Set.add (fst newdef) oldsenv.modlabels;
    univ =
      List.fold_left (fun acc cst ->
        Univ.ContextSet.union acc (Future.force cst))
      (Univ.ContextSet.union senv.univ oldsenv.univ)
      now_cst;
    future_cst = later_cst @ oldsenv.future_cst;
    (* engagement is propagated to the upper level *)
    engagement = senv.engagement;
    required = senv.required;
    loads = senv.loads@oldsenv.loads;
    local_retroknowledge =
            senv.local_retroknowledge@oldsenv.local_retroknowledge;
    native_symbols = senv.native_symbols}

let end_module l restype senv =
  let mp = senv.modpath in
  let params, oldsenv = check_struct senv.modvariant in
  let () = check_current_label l mp in
  let () = check_empty_context senv in
  let mbids = List.rev_map fst params in
  let mb = build_module_body params restype senv in
  let newenv = Environ.set_opaque_tables oldsenv.env (Environ.opaque_tables senv.env) in
  let newenv = set_engagement_opt newenv senv.engagement in
  let senv'=
    propagate_loads { senv with
      env = newenv;
      univ = Univ.ContextSet.union senv.univ mb.mod_constraints} in
  let newenv = Environ.push_context_set ~strict:true mb.mod_constraints senv'.env in
  let newenv = Modops.add_module mb newenv in
  let newresolver =
    if Modops.is_functor mb.mod_type then oldsenv.modresolver
    else Mod_subst.add_delta_resolver mb.mod_delta oldsenv.modresolver
  in
  (mp,mbids,mb.mod_delta),
  propagate_senv (l,SFBmodule mb) newenv newresolver senv' oldsenv

let build_mtb mp sign cst delta =
  { mod_mp = mp;
    mod_expr = ();
    mod_type = sign;
    mod_type_alg = None;
    mod_constraints = cst;
    mod_delta = delta;
    mod_retroknowledge = ModTypeRK }

let end_modtype l senv =
  let mp = senv.modpath in
  let params, oldsenv = check_sig senv.modvariant in
  let () = check_current_label l mp in
  let () = check_empty_context senv in
  let mbids = List.rev_map fst params in
  let newenv = Environ.set_opaque_tables oldsenv.env (Environ.opaque_tables senv.env) in
  let newenv = Environ.push_context_set ~strict:true senv.univ newenv in
  let newenv = set_engagement_opt newenv senv.engagement in
  let senv' = propagate_loads {senv with env=newenv} in
  let auto_tb = functorize params (NoFunctor (List.rev senv.revstruct)) in
  let mtb = build_mtb mp auto_tb senv'.univ senv.modresolver in
  let newenv = Environ.add_modtype mtb senv'.env in
  let newresolver = oldsenv.modresolver in
  (mp,mbids),
  propagate_senv (l,SFBmodtype mtb) newenv newresolver senv' oldsenv

(** {6 Inclusion of module or module type } *)

let add_include me is_module inl senv =
  let open Mod_typing in
  let mp_sup = senv.modpath in
  let sign,(),resolver,cst =
    translate_mse_incl is_module senv.env mp_sup inl me
  in
  let senv = add_constraints (Now (false, cst)) senv in
  (* Include Self support  *)
  let rec compute_sign sign mb resolver senv =
    match sign with
    | MoreFunctor(mbid,mtb,str) ->
      let cst_sub = Subtyping.check_subtypes senv.env mb mtb in
      let senv =
	add_constraints
	  (Now (false, Univ.ContextSet.add_constraints cst_sub Univ.ContextSet.empty))
	  senv in
      let mpsup_delta =
	Modops.inline_delta_resolver senv.env inl mp_sup mbid mtb mb.mod_delta
      in
      let subst = Mod_subst.map_mbid mbid mp_sup mpsup_delta in
      let resolver = Mod_subst.subst_codom_delta_resolver subst resolver in
      compute_sign (Modops.subst_signature subst str) mb resolver senv
    | NoFunctor str -> resolver,str,senv
  in
  let resolver,str,senv =
    let struc = NoFunctor (List.rev senv.revstruct) in
    let mtb = build_mtb mp_sup struc Univ.ContextSet.empty senv.modresolver in
    compute_sign sign mtb resolver senv
  in
  let senv = update_resolver (Mod_subst.add_delta_resolver resolver) senv
  in
  let add senv ((l,elem) as field) =
    let new_name = match elem with
      | SFBconst _ ->
        C (Mod_subst.constant_of_delta_kn resolver (KerName.make2 mp_sup l))
      | SFBmind _ ->
	I (Mod_subst.mind_of_delta_kn resolver (KerName.make2 mp_sup l))
      | SFBmodule _ -> M
      | SFBmodtype _ -> MT
    in
    add_field field new_name senv
  in
  resolver, List.fold_left add senv str

(** {6 Libraries, i.e. compiled modules } *)

type compiled_library = {
  comp_name : DirPath.t;
  comp_mod : module_body;
  comp_deps : library_info array;
  comp_enga : engagement;
  comp_natsymbs : Nativecode.symbols
}

type native_library = Nativecode.global list

let get_library_native_symbols senv dir =
  try DPMap.find dir senv.native_symbols
  with Not_found -> CErrors.user_err ~hdr:"get_library_native_symbols"
                      Pp.((str "Linker error in the native compiler. Are you using Require inside a nested Module declaration?") ++ fnl () ++
                          (str "This use case is not supported, but disabling the native compiler may help."))

(** FIXME: MS: remove?*)
let current_modpath senv = senv.modpath
let current_dirpath senv = Names.ModPath.dp (current_modpath senv)

let start_library dir senv =
  check_initial senv;
  assert (not (DirPath.is_empty dir));
  let mp = MPfile dir in
  mp,
  { empty_environment with
    env = senv.env;
    modpath = mp;
    modvariant = LIBRARY;
    required = senv.required }

let export ?except senv dir =
  let senv =
    try join_safe_environment ?except senv
    with e ->
      let e = CErrors.push e in
      CErrors.user_err ~hdr:"export" (CErrors.iprint e)
  in
  assert(senv.future_cst = []);
  let () = check_current_library dir senv in
  let mp = senv.modpath in
  let str = NoFunctor (List.rev senv.revstruct) in
  let mb =
    { mod_mp = mp;
      mod_expr = FullStruct;
      mod_type = str;
      mod_type_alg = None;
      mod_constraints = senv.univ;
      mod_delta = senv.modresolver;
      mod_retroknowledge = ModBodyRK senv.local_retroknowledge
    }
  in
  let ast, symbols =
    if !Flags.output_native_objects then
      Nativelibrary.dump_library mp dir senv.env str
    else [], Nativecode.empty_symbols
  in
  let lib = {
    comp_name = dir;
    comp_mod = mb;
    comp_deps = Array.of_list (DPMap.bindings senv.required);
    comp_enga = Environ.engagement senv.env;
    comp_natsymbs = symbols }
  in
  mp, lib, ast

(* cst are the constraints that were computed by the vi2vo step and hence are
 * not part of the mb.mod_constraints field (but morally should be) *)
let import lib cst vodigest senv =
  check_required senv.required lib.comp_deps;
  check_engagement senv.env lib.comp_enga;
  if DirPath.equal (ModPath.dp senv.modpath) lib.comp_name then
    CErrors.user_err ~hdr:"Safe_typing.import"
     (Pp.strbrk "Cannot load a library with the same name as the current one.");
  let mp = MPfile lib.comp_name in
  let mb = lib.comp_mod in
  let env = Environ.push_context_set ~strict:true
				     (Univ.ContextSet.union mb.mod_constraints cst)
				     senv.env
  in
  mp,
  { senv with
    env =
      (let linkinfo =
	 Nativecode.link_info_of_dirpath lib.comp_name
       in
       Modops.add_linked_module mb linkinfo env);
    modresolver = Mod_subst.add_delta_resolver mb.mod_delta senv.modresolver;
    required = DPMap.add lib.comp_name vodigest senv.required;
    loads = (mp,mb)::senv.loads;
    native_symbols = DPMap.add lib.comp_name lib.comp_natsymbs senv.native_symbols }

(** {6 Safe typing } *)

type judgment = Environ.unsafe_judgment

let j_val j = j.Environ.uj_val
let j_type j = j.Environ.uj_type

let typing senv = Typeops.infer (env_of_senv senv)

(** {6 Retroknowledge / native compiler } *)

[@@@ocaml.warning "-3"]
(** universal lifting, used for the "get" operations mostly *)
let retroknowledge f senv =
  Environ.retroknowledge f (env_of_senv senv)
[@@@ocaml.warning "+3"]

let register field value by_clause senv =
  (* todo : value closed, by_clause safe, by_clause of the proper type*)
  (* spiwack : updates the safe_env with the information that the register
     action has to be performed (again) when the environment is imported *)
  { senv with
    env = Environ.register senv.env field value;
    local_retroknowledge =
      Retroknowledge.RKRegister (field,value)::senv.local_retroknowledge
  }

(* This function serves only for inlining constants in native compiler for now,
but it is meant to become a replacement for environ.register *)
let register_inline kn senv =
  let open Environ in
  if not (evaluable_constant kn senv.env) then
    CErrors.user_err Pp.(str "Register inline: an evaluable constant is expected");
  let env = senv.env in
  let cb = lookup_constant kn env in
  let cb = {cb with const_inline_code = true} in
  let env = add_constant kn cb env in { senv with env}

let add_constraints c =
  add_constraints
    (Now (false, Univ.ContextSet.add_constraints c Univ.ContextSet.empty))


(* NB: The next old comment probably refers to [propagate_loads] above.
   When a Require is done inside a module, we'll redo this require
   at the upper level after the module is ended, and so on.
   This is probably not a big deal anyway, since these Require's
   inside modules should be pretty rare. Maybe someday we could
   brutally forbid this tricky "feature"... *)

(* we have an inefficiency: Since loaded files are added to the
environment every time a module is closed, their components are
calculated many times. This could be avoided in several ways:

1 - for each file create a dummy environment containing only this
file's components, merge this environment with the global
environment, and store for the future (instead of just its type)

2 - create "persistent modules" environment table in Environ add put
loaded by side-effect once and for all (like it is done in OCaml).
Would this be correct with respect to undo's and stuff ?
*)

let set_strategy e k l = { e with env =
   (Environ.set_oracle e.env
      (Conv_oracle.set_strategy (Environ.oracle e.env) k l)) }

(** Register retroknowledge hooks *)

open Retroknowledge

(* the Environ.register function synchronizes the proactive and reactive
   retroknowledge. *)
let dispatch =

  (* subfunction used for static decompilation of int31 (after a vm_compute,
     see pretyping/vnorm.ml for more information) *)
  let constr_of_int31 =
    let nth_digit_plus_one i n = (* calculates the nth (starting with 0)
                                    digit of i and adds 1 to it
                                    (nth_digit_plus_one 1 3 = 2) *)
      if Int.equal (i land (1 lsl n)) 0 then
        1
      else
        2
    in
      fun ind -> fun digit_ind -> fun tag ->
        let array_of_int i =
          Array.init 31 (fun n -> Constr.mkConstruct
                           (digit_ind, nth_digit_plus_one i (30-n)))
        in
        (* We check that no bit above 31 is set to one. This assertion used to
        fail in the VM, and led to conversion tests failing at Qed. *)
        assert (Int.equal (tag lsr 31) 0);
        Constr.mkApp(Constr.mkConstruct(ind, 1), array_of_int tag)
  in

  (* subfunction which dispatches the compiling information of an
     int31 operation which has a specific vm instruction (associates
     it to the name of the coq definition in the reactive retroknowledge) *)
  let int31_op n op prim kn =
    { empty_reactive_info with
      vm_compiling = Some (Clambda.compile_prim n op kn);
      native_compiling = Some (Nativelambda.compile_prim prim (Univ.out_punivs kn));
    }
  in

fun rk value field ->
  (* subfunction which shortens the (very common) dispatch of operations *)
  let int31_op_from_const n op prim =
    match Constr.kind value with
      | Constr.Const kn ->  int31_op n op prim kn
      | _ -> anomaly ~label:"Environ.register" (Pp.str "should be a constant.")
  in
  let int31_binop_from_const op prim = int31_op_from_const 2 op prim in
  let int31_unop_from_const op prim = int31_op_from_const 1 op prim in
  match field with
    | KInt31 (grp, Int31Type) ->
        let int31bit =
          (* invariant : the type of bits is registered, otherwise the function
             would raise Not_found. The invariant is enforced in safe_typing.ml *)
          match field with
          | KInt31 (grp, Int31Type) -> Retroknowledge.find rk (KInt31 (grp,Int31Bits))
          | _ -> anomaly ~label:"Environ.register"
              (Pp.str "add_int31_decompilation_from_type called with an abnormal field.")
        in
        let i31bit_type =
          match Constr.kind int31bit with
          | Constr.Ind (i31bit_type,_) -> i31bit_type
          |  _ -> anomaly ~label:"Environ.register"
              (Pp.str "Int31Bits should be an inductive type.")
        in
        let int31_decompilation =
          match Constr.kind value with
          | Constr.Ind (i31t,_) ->
              constr_of_int31 i31t i31bit_type
          | _ -> anomaly ~label:"Environ.register"
              (Pp.str "should be an inductive type.")
        in
        { empty_reactive_info with
          vm_decompile_const = Some int31_decompilation;
          vm_before_match = Some Clambda.int31_escape_before_match;
          native_before_match = Some (Nativelambda.before_match_int31 i31bit_type);
        }
    | KInt31 (_, Int31Constructor) ->
        { empty_reactive_info with
          vm_constant_static = Some Clambda.compile_structured_int31;
          vm_constant_dynamic = Some Clambda.dynamic_int31_compilation;
          native_constant_static = Some Nativelambda.compile_static_int31;
          native_constant_dynamic = Some Nativelambda.compile_dynamic_int31;
        }
    | KInt31 (_, Int31Plus) -> int31_binop_from_const Cbytecodes.Kaddint31
                                                          CPrimitives.Int31add
    | KInt31 (_, Int31PlusC) -> int31_binop_from_const Cbytecodes.Kaddcint31
                                                           CPrimitives.Int31addc
    | KInt31 (_, Int31PlusCarryC) -> int31_binop_from_const Cbytecodes.Kaddcarrycint31
                                                                CPrimitives.Int31addcarryc
    | KInt31 (_, Int31Minus) -> int31_binop_from_const Cbytecodes.Ksubint31
                                                           CPrimitives.Int31sub
    | KInt31 (_, Int31MinusC) -> int31_binop_from_const Cbytecodes.Ksubcint31
                                                            CPrimitives.Int31subc
    | KInt31 (_, Int31MinusCarryC) -> int31_binop_from_const
                                        Cbytecodes.Ksubcarrycint31 CPrimitives.Int31subcarryc
    | KInt31 (_, Int31Times) -> int31_binop_from_const Cbytecodes.Kmulint31
                                                           CPrimitives.Int31mul
    | KInt31 (_, Int31TimesC) -> int31_binop_from_const Cbytecodes.Kmulcint31
                                                           CPrimitives.Int31mulc
    | KInt31 (_, Int31Div21) -> int31_op_from_const 3 Cbytecodes.Kdiv21int31
                                                           CPrimitives.Int31div21
    | KInt31 (_, Int31Diveucl) -> int31_binop_from_const Cbytecodes.Kdivint31
                                                         CPrimitives.Int31diveucl
    | KInt31 (_, Int31AddMulDiv) -> int31_op_from_const 3 Cbytecodes.Kaddmuldivint31
                                                         CPrimitives.Int31addmuldiv
    | KInt31 (_, Int31Compare) -> int31_binop_from_const Cbytecodes.Kcompareint31
                                                             CPrimitives.Int31compare
    | KInt31 (_, Int31Head0) -> int31_unop_from_const Cbytecodes.Khead0int31
                                                          CPrimitives.Int31head0
    | KInt31 (_, Int31Tail0) -> int31_unop_from_const Cbytecodes.Ktail0int31
                                                          CPrimitives.Int31tail0
    | KInt31 (_, Int31Lor) -> int31_binop_from_const Cbytecodes.Klorint31
                                                         CPrimitives.Int31lor
    | KInt31 (_, Int31Land) -> int31_binop_from_const Cbytecodes.Klandint31
                                                          CPrimitives.Int31land
    | KInt31 (_, Int31Lxor) -> int31_binop_from_const Cbytecodes.Klxorint31
                                                          CPrimitives.Int31lxor
    | _ -> empty_reactive_info

let _ = Hook.set Retroknowledge.dispatch_hook dispatch
