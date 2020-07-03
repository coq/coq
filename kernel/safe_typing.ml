(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

open Util
open Names
open Declarations
open Constr
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

type compiled_library = {
  comp_name : DirPath.t;
  comp_mod : module_body;
  comp_univs : Univ.ContextSet.t;
  comp_deps : library_info array;
  comp_enga : engagement;
  comp_natsymbs : Nativevalues.symbols
}

type reimport = compiled_library * Univ.ContextSet.t * vodigest

(** Part of the safe_env at a section opening time to be backtracked *)
type section_data = {
  rev_env : Environ.env;
  rev_univ : Univ.ContextSet.t;
  rev_objlabels : Label.Set.t;
  rev_reimport : reimport list;
}

type safe_environment =
  { env : Environ.env;
    sections : section_data Section.t option;
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
    required : vodigest DPmap.t;
    loads : (ModPath.t * module_body) list;
    local_retroknowledge : Retroknowledge.action list;
}

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
    sections = None;
    future_cst = [];
    univ = Univ.ContextSet.empty;
    engagement = None;
    required = DPmap.empty;
    loads = [];
    local_retroknowledge = [];
}

let is_initial senv =
  match senv.revstruct, senv.modvariant with
  | [], NONE -> ModPath.equal senv.modpath ModPath.initial
  | _ -> false

let sections_are_opened senv = not (Option.is_empty senv.sections)

let delta_of_senv senv = senv.modresolver,senv.paramresolver

let constant_of_delta_kn_senv senv kn =
  Mod_subst.constant_of_deltas_kn senv.paramresolver senv.modresolver kn

let mind_of_delta_kn_senv senv kn =
  Mod_subst.mind_of_deltas_kn senv.paramresolver senv.modresolver kn

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
  let env = Environ.set_typing_flags c senv.env in
  if env == senv.env then senv
  else { senv with env }

let set_check_guarded b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_guarded = b } senv

let set_check_sized b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_sized = b } senv

let set_check_positive b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_positive = b } senv

let set_check_universes b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_universes = b } senv

let set_indices_matter indices_matter senv =
  set_typing_flags { (Environ.typing_flags senv.env) with indices_matter } senv

let set_share_reduction b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with share_reduction = b } senv

let set_VM b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with enable_VM = b } senv

let set_native_compiler b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with enable_native_compiler = b } senv

let set_allow_sprop b senv = { senv with env = Environ.set_allow_sprop b senv.env }

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

module Certificate :
sig
  type t

  val make : safe_environment -> t

  val universes : t -> Univ.ContextSet.t

  (** Checks whether [dst] is a valid extension of [src] *)
  val check : src:t -> dst:t -> bool
end =
struct

type t = {
  certif_struc : Declarations.structure_body;
  certif_univs : Univ.ContextSet.t;
}

let make senv = {
  certif_struc = senv.revstruct;
  certif_univs = senv.univ;
}

let is_suffix l suf = match l with
| [] -> false
| _ :: l -> l == suf

let is_subset (s1, cst1) (s2, cst2) =
  Univ.LSet.subset s1 s2 && Univ.Constraint.subset cst1 cst2

let check ~src ~dst =
  is_suffix dst.certif_struc src.certif_struc &&
  is_subset src.certif_univs dst.certif_univs

let universes c = c.certif_univs

end

type side_effect = {
  seff_certif : Certificate.t CEphemeron.key;
  seff_constant : Constant.t;
  seff_body : Constr.t Declarations.constant_body;
}
(* Invariant: For any senv, if [Certificate.check senv seff_certif] then
  senv where univs := Certificate.universes seff_certif] +
  (c.seff_constant -> seff_body) is well-formed. *)

module SideEffects :
sig
  type t
  val repr : t -> side_effect list
  val empty : t
  val is_empty : t -> bool
  val add : side_effect -> t -> t
  val concat : t -> t -> t
end =
struct

module SeffOrd = struct
type t = side_effect
let compare e1 e2 =
  Constant.CanOrd.compare e1.seff_constant e2.seff_constant
end

module SeffSet = Set.Make(SeffOrd)

type t = { seff : side_effect list; elts : SeffSet.t }
(** Invariant: [seff] is a permutation of the elements of [elts] *)

let repr eff = eff.seff
let empty = { seff = []; elts = SeffSet.empty }
let is_empty { seff; elts } = List.is_empty seff && SeffSet.is_empty elts
let add x es =
  if SeffSet.mem x es.elts then es
  else { seff = x :: es.seff; elts = SeffSet.add x es.elts }
let concat xes yes =
  List.fold_right add xes.seff yes

end

type private_constants = SideEffects.t

let side_effects_of_private_constants l =
  List.rev (SideEffects.repr l)

(* Only used to push in an Environ.env. *)
let lift_constant c =
  let body = match c.const_body with
  | OpaqueDef _ -> Undef None
  | Def _ | Undef _ | Primitive _ as body -> body
  in
  { c with const_body = body }

let push_private_constants env eff =
  let eff = side_effects_of_private_constants eff in
  let add_if_undefined env eff =
    if Environ.mem_constant eff.seff_constant env then env
    else Environ.add_constant eff.seff_constant (lift_constant eff.seff_body) env
  in
  List.fold_left add_if_undefined env eff

let empty_private_constants = SideEffects.empty
let is_empty_private_constants c = SideEffects.is_empty c
let concat_private = SideEffects.concat

let universes_of_private eff =
  let fold acc eff =
    match eff.seff_body.const_universes with
    | Monomorphic ctx -> Univ.ContextSet.union ctx acc
    | Polymorphic _ -> acc
  in
  List.fold_left fold Univ.ContextSet.empty (side_effects_of_private_constants eff)

let env_of_safe_env senv = senv.env
let env_of_senv = env_of_safe_env

let structure_body_of_safe_env env = env.revstruct

let sections_of_safe_env senv = senv.sections

let get_section = function
  | None -> CErrors.user_err Pp.(str "No open section.")
  | Some s -> s

type constraints_addition =
  | Now of Univ.ContextSet.t
  | Later of Univ.ContextSet.t Future.computation

let push_context_set ~strict cst senv =
  if Univ.ContextSet.is_empty cst then senv
  else
    let sections = Option.map (Section.push_constraints cst) senv.sections
    in
    { senv with
      env = Environ.push_context_set ~strict cst senv.env;
      univ = Univ.ContextSet.union cst senv.univ;
      sections }

let add_constraints cst senv =
  match cst with
  | Later fc ->
    {senv with future_cst = fc :: senv.future_cst}
  | Now cst ->
    push_context_set ~strict:true cst senv

let add_constraints_list cst senv =
  List.fold_left (fun acc c -> add_constraints c acc) senv cst

let is_curmod_library senv =
  match senv.modvariant with LIBRARY -> true | _ -> false

let join_safe_environment ?(except=Future.UUIDSet.empty) e =
  Modops.join_structure except (Environ.opaque_tables e.env) e.revstruct;
  List.fold_left
    (fun e fc ->
       if Future.UUIDSet.mem (Future.uuid fc) except then e
       else add_constraints (Now (Future.join fc)) e)
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
  assert (Environ.empty_context senv.env && Option.is_empty senv.sections)

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
      let actual = DPmap.find id current_libs in
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
  let sections = get_section senv.sections in
  let sections = Section.push_local sections in
  let c, r, typ = Term_typing.translate_local_def senv.env id de in
  let x = Context.make_annot id r in
  let env'' = safe_push_named (LocalDef (x, c, typ)) senv.env in
  { senv with sections=Some sections; env = env'' }

let push_named_assum (x,t) senv =
  let sections = get_section senv.sections in
  let sections = Section.push_local sections in
  let t, r = Term_typing.translate_local_assum senv.env t in
  let x = Context.make_annot x r in
  let env'' = safe_push_named (LocalAssum (x,t)) senv.env in
  { senv with sections=Some sections; env = env'' }

let push_section_context (nas, ctx) senv =
  let sections = get_section senv.sections in
  let sections = Section.push_context (nas, ctx) sections in
  let senv = { senv with sections=Some sections } in
  let ctx = Univ.ContextSet.of_context ctx in
  (* We check that the universes are fresh. FIXME: This should be done
     implicitly, but we have to work around the API. *)
  let () = assert (Univ.LSet.for_all (fun u -> not (Univ.LSet.mem u (fst senv.univ))) (fst ctx)) in
  { senv with
    env = Environ.push_context_set ~strict:false ctx senv.env;
    univ = Univ.ContextSet.union ctx senv.univ }

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

let globalize_constant_universes cb =
  match cb.const_universes with
  | Monomorphic cstrs ->
    (* Constraints hidden in the opaque body are added by [add_constant_aux] *)
    [cstrs]
  | Polymorphic _ ->
    []

let globalize_mind_universes mb =
  match mb.mind_universes with
  | Monomorphic ctx ->
    [ctx]
  | Polymorphic _ -> []

let constraints_of_sfb sfb =
  match sfb with
  | SFBconst cb -> globalize_constant_universes cb
  | SFBmind mib -> globalize_mind_universes mib
  | SFBmodtype _ | SFBmodule _ -> []

let add_retroknowledge pttc senv =
  { senv with
    env = Primred.add_retroknowledge senv.env pttc;
    local_retroknowledge = pttc::senv.local_retroknowledge }

(** A generic function for adding a new field in a same environment.
    It also performs the corresponding [add_constraints]. *)

type generic_name =
  | C of Constant.t
  | I of MutInd.t
  | M (** name already known, cf the mod_mp field *)
  | MT (** name already known, cf the mod_mp field *)

let add_field ?(is_include=false) ((l,sfb) as field) gn senv =
  let mlabs,olabs = match sfb with
    | SFBmind mib ->
      let l = labels_of_mib mib in
      check_objlabels l senv; (Label.Set.empty,l)
    | SFBconst _ ->
      check_objlabel l senv; (Label.Set.empty, Label.Set.singleton l)
    | SFBmodule _ | SFBmodtype _ ->
      check_modlabel l senv; (Label.Set.singleton l, Label.Set.empty)
  in
  let senv =
    if is_include then
      (* Universes and constraints were added when the included module
         was defined eg in [Include F X.] (one of the trickier
         versions of Include) the constraints on the fields are
         exactly those of the fields of F which was defined
         separately. *)
      senv
    else
      (* Delayed constraints from opaque body are added by [add_constant_aux] *)
      let cst = constraints_of_sfb sfb in
      List.fold_left (fun senv cst -> push_context_set ~strict:true cst senv) senv cst
  in
  let env' = match sfb, gn with
    | SFBconst cb, C con -> Environ.add_constant con cb senv.env
    | SFBmind mib, I mind -> Environ.add_mind mind mib senv.env
    | SFBmodtype mtb, MT -> Environ.add_modtype mtb senv.env
    | SFBmodule mb, M -> Modops.add_module mb senv.env
    | _ -> assert false
  in
  let sections = match senv.sections with
    | None -> None
    | Some sections ->
      match sfb, gn with
      | SFBconst cb, C con ->
        let poly = Declareops.constant_is_polymorphic cb in
        Some (Section.push_constant ~poly con sections)
      | SFBmind mib, I mind ->
        let poly = Declareops.inductive_is_polymorphic mib in
        Some (Section.push_inductive ~poly mind sections)
      | _, (M | MT) -> Some sections
      | _ -> assert false
  in
  { senv with
    env = env';
    sections;
    revstruct = field :: senv.revstruct;
    modlabels = Label.Set.union mlabs senv.modlabels;
    objlabels = Label.Set.union olabs senv.objlabels }

(** Applying a certain function to the resolver of a safe environment *)

let update_resolver f senv = { senv with modresolver = f senv.modresolver }

type global_declaration =
| ConstantEntry : Entries.constant_entry -> global_declaration
| OpaqueEntry : private_constants Entries.const_entry_body Entries.opaque_entry -> global_declaration

type exported_private_constant = Constant.t

let add_constant_aux senv (kn, cb) =
  let l = Constant.label kn in
  (* This is the only place where we hashcons the contents of a constant body *)
  let cb = if sections_are_opened senv then cb else Declareops.hcons_const_body cb in
  let senv' = add_field (l,SFBconst cb) (C kn) senv in
  let senv'' = match cb.const_body with
    | Undef (Some lev) ->
      update_resolver
        (Mod_subst.add_inline_delta_resolver (Constant.user kn) (lev,None)) senv'
    | _ -> senv'
  in
  senv''

let mk_pure_proof c = (c, Univ.ContextSet.empty), SideEffects.empty

let inline_side_effects env body side_eff =
  let open Constr in
  (** First step: remove the constants that are still in the environment *)
  let filter e =
    let cb = (e.seff_constant, e.seff_body) in
    if Environ.mem_constant e.seff_constant env then None
    else Some (cb, e.seff_certif)
  in
  (* CAVEAT: we assure that most recent effects come first *)
  let side_eff = List.map_filter filter (SideEffects.repr side_eff) in
  let sigs = List.rev_map (fun (_, mb) -> mb) side_eff in
  let side_eff = List.fold_left (fun accu (cb, _) -> cb :: accu) [] side_eff in
  let side_eff = List.rev side_eff in
  (** Most recent side-effects first in side_eff *)
  if List.is_empty side_eff then (body, Univ.ContextSet.empty, sigs)
  else
    (** Second step: compute the lifts and substitutions to apply *)
    let cname c r = Context.make_annot (Name (Label.to_id (Constant.label c))) r in
    let fold (subst, var, ctx, args) (c, cb) =
      let (b, opaque) = match cb.const_body with
      | Def b -> (Mod_subst.force_constr b, false)
      | OpaqueDef b -> (b, true)
      | _ -> assert false
      in
      match cb.const_universes with
      | Monomorphic univs ->
        (** Abstract over the term at the top of the proof *)
        let ty = cb.const_type in
        let subst = Cmap_env.add c (Inr var) subst in
        let ctx = Univ.ContextSet.union ctx univs in
        (subst, var + 1, ctx, (cname c cb.const_relevance, b, ty, opaque) :: args)
      | Polymorphic _ ->
        (** Inline the term to emulate universe polymorphism *)
        let subst = Cmap_env.add c (Inl b) subst in
        (subst, var, ctx, args)
    in
    let (subst, len, ctx, args) = List.fold_left fold (Cmap_env.empty, 1, Univ.ContextSet.empty, []) side_eff in
    (** Third step: inline the definitions *)
    let rec subst_const i k t = match Constr.kind t with
    | Const (c, u) ->
      let data = try Some (Cmap_env.find c subst) with Not_found -> None in
      begin match data with
      | None -> t
      | Some (Inl b) ->
        (** [b] is closed but may refer to other constants *)
        subst_const i k (Vars.subst_instance_constr u b)
      | Some (Inr n) ->
        mkRel (k + n - i)
      end
    | Rel n ->
      (** Lift free rel variables *)
      if n <= k then t
      else mkRel (n + len - i - 1)
    | _ -> Constr.map_with_binders ((+) 1) (fun k t -> subst_const i k t) k t
    in
    let map_args i (na, b, ty, opaque) =
      (** Both the type and the body may mention other constants *)
      let ty = subst_const (len - i - 1) 0 ty in
      let b = subst_const (len - i - 1) 0 b in
      (na, b, ty, opaque)
    in
    let args = List.mapi map_args args in
    let body = subst_const 0 0 body in
    let fold_arg (na, b, ty, opaque) accu =
      if opaque then mkApp (mkLambda (na, ty, accu), [|b|])
      else mkLetIn (na, b, ty, accu)
    in
    let body = List.fold_right fold_arg args body in
    (body, ctx, sigs)

let inline_private_constants env ((body, ctx), side_eff) =
  let body, ctx',_ = inline_side_effects env body side_eff in
  let ctx' = Univ.ContextSet.union ctx ctx' in
  (body, ctx')

(* Given the list of signatures of side effects, checks if they match.
 * I.e. if they are ordered descendants of the current revstruct.
   Returns the number of effects that can be trusted. *)
let check_signatures senv sl =
  let curmb = Certificate.make senv in
  let is_direct_ancestor accu mb =
    match accu with
    | None -> None
    | Some curmb ->
        try
          let mb = CEphemeron.get mb in
          if Certificate.check ~src:curmb ~dst:mb
          then Some mb
          else None
        with CEphemeron.InvalidKey -> None in
  let sl = List.fold_left is_direct_ancestor (Some curmb) sl in
  match sl with
  | None -> None
  | Some mb ->
    let univs = Certificate.universes mb in
    Some (Univ.ContextSet.diff univs senv.univ)

type side_effect_declaration =
| DefinitionEff : Entries.definition_entry -> side_effect_declaration
| OpaqueEff : Constr.constr Entries.opaque_entry -> side_effect_declaration

let constant_entry_of_side_effect eff =
  let cb = eff.seff_body in
  let open Entries in
  let univs =
    match cb.const_universes with
    | Monomorphic uctx ->
      Monomorphic_entry uctx
    | Polymorphic auctx ->
      Polymorphic_entry (Univ.AUContext.names auctx, Univ.AUContext.repr auctx)
  in
  let p =
    match cb.const_body with
    | OpaqueDef b -> b
    | Def b -> Mod_subst.force_constr b
    | _ -> assert false in
  if Declareops.is_opaque cb then
  OpaqueEff {
    opaque_entry_body = p;
    opaque_entry_secctx = Context.Named.to_vars cb.const_hyps;
    opaque_entry_feedback = None;
    opaque_entry_type = cb.const_type;
    opaque_entry_universes = univs;
  }
  else
  DefinitionEff {
    const_entry_body = p;
    const_entry_secctx = Some (Context.Named.to_vars cb.const_hyps);
    const_entry_feedback = None;
    const_entry_type = Some cb.const_type;
    const_entry_universes = univs;
    const_entry_inline_code = cb.const_inline_code }

let export_eff eff =
  (eff.seff_constant, eff.seff_body)

let is_empty_private = function
| Opaqueproof.PrivateMonomorphic ctx -> Univ.ContextSet.is_empty ctx
| Opaqueproof.PrivatePolymorphic (_, ctx) -> Univ.ContextSet.is_empty ctx

let empty_private univs = match univs with
| Monomorphic _ -> Opaqueproof.PrivateMonomorphic Univ.ContextSet.empty
| Polymorphic auctx -> Opaqueproof.PrivatePolymorphic (Univ.AUContext.size auctx, Univ.ContextSet.empty)

(* Special function to call when the body of an opaque definition is provided.
  It performs the type-checking of the body immediately. *)
let translate_direct_opaque env kn ce =
  let cb, ctx = Term_typing.translate_opaque env kn ce in
  let body = ce.Entries.opaque_entry_body, Univ.ContextSet.empty in
  let handle _env c () = (c, Univ.ContextSet.empty, 0) in
  let (c, u) = Term_typing.check_delayed handle ctx (body, ()) in
  (* No constraints can be generated, we set it empty everywhere *)
  let () = assert (is_empty_private u) in
  { cb with const_body = OpaqueDef c }

let export_side_effects senv eff =
  let env = senv.env in
      let not_exists e = not (Environ.mem_constant e.seff_constant env) in
      let aux (acc,sl) e =
        if not (not_exists e) then acc, sl
        else e :: acc, e.seff_certif :: sl in
      let seff, signatures = List.fold_left aux ([],[]) (SideEffects.repr eff) in
      let trusted = check_signatures senv signatures in
      let push_seff env eff =
        let { seff_constant = kn; seff_body = cb ; _ } = eff in
        let env = Environ.add_constant kn (lift_constant cb) env in
        match cb.const_universes with
        | Polymorphic _ -> env
        | Monomorphic ctx ->
          Environ.push_context_set ~strict:true ctx env
      in
    match trusted with
    | Some univs ->
      univs, List.map export_eff seff
    | None ->
      let rec recheck_seff seff acc env = match seff with
      | [] -> List.rev acc
      | eff :: rest ->
        let env, cb =
          let kn = eff.seff_constant in
          let ce = constant_entry_of_side_effect eff in
          let open Entries in
          let cb = match ce with
          | DefinitionEff ce ->
            Term_typing.translate_constant env kn (DefinitionEntry ce)
          | OpaqueEff ce ->
            translate_direct_opaque env kn ce
          in
            let eff = { eff with seff_body = cb } in
            (push_seff env eff, export_eff eff)
        in
        recheck_seff rest (cb :: acc) env
      in
      Univ.ContextSet.empty, recheck_seff seff [] env

let push_opaque_proof pf senv =
  let o, otab = Opaqueproof.create (library_dp_of_senv senv) pf (Environ.opaque_tables senv.env) in
  let senv = { senv with env = Environ.set_opaque_tables senv.env otab } in
  senv, o

let export_private_constants eff senv =
  let uctx, exported = export_side_effects senv eff in
  let senv = push_context_set ~strict:true uctx senv in
  let map senv (kn, c) = match c.const_body with
  | OpaqueDef p ->
    let local = empty_private c.const_universes in
    let senv, o = push_opaque_proof (Future.from_val (p, local)) senv in
    senv, (kn, { c with const_body = OpaqueDef o })
  | Def _ | Undef _ | Primitive _ as body ->
    senv, (kn, { c with const_body = body })
  in
  let senv, bodies = List.fold_left_map map senv exported in
  let exported = List.map (fun (kn, _) -> kn) exported in
  (* No delayed constants to declare *)
  let senv = List.fold_left add_constant_aux senv bodies in
  exported, senv

let add_constant l decl senv =
  let kn = Constant.make2 senv.modpath l in
    let cb =
      match decl with
      | OpaqueEntry ce ->
        let handle env body eff =
          let body, uctx, signatures = inline_side_effects env body eff in
          let trusted = check_signatures senv signatures in
          let trusted, uctx = match trusted with
          | None -> 0, uctx
          | Some univs -> List.length signatures, Univ.ContextSet.union univs uctx
          in
          body, uctx, trusted
        in
        let cb, ctx = Term_typing.translate_opaque senv.env kn ce in
        let map pf = Term_typing.check_delayed handle ctx pf in
        let pf = Future.chain ce.Entries.opaque_entry_body map in
        { cb with const_body = OpaqueDef pf }
      | ConstantEntry ce ->
        Term_typing.translate_constant senv.env kn ce
    in
  let senv =
    let senv, cb, delayed_cst = match cb.const_body with
    | OpaqueDef fc ->
      let senv, o = push_opaque_proof fc senv in
      let delayed_cst =
        if not (Declareops.constant_is_polymorphic cb) then
          let map (_, u) = match u with
          | Opaqueproof.PrivateMonomorphic ctx -> ctx
          | Opaqueproof.PrivatePolymorphic _ -> assert false
          in
          let fc = Future.chain fc map in
          match Future.peek_val fc with
          | None -> [Later fc]
          | Some c -> [Now c]
        else []
      in
      senv, { cb with const_body = OpaqueDef o }, delayed_cst
    | Undef _ | Def _ | Primitive _ as body ->
      senv, { cb with const_body = body }, []
    in
    let senv = add_constant_aux senv (kn, cb) in
    add_constraints_list delayed_cst senv
  in

  let senv =
    match decl with
    | ConstantEntry (Entries.PrimitiveEntry { Entries.prim_entry_content = CPrimitives.OT_type t; _ }) ->
      if sections_are_opened senv then CErrors.anomaly (Pp.str "Primitive type not allowed in sections");
      add_retroknowledge (Retroknowledge.Register_type(t,kn)) senv
    | _ -> senv
  in
  kn, senv

let add_private_constant l decl senv : (Constant.t * private_constants) * safe_environment =
  let kn = Constant.make2 senv.modpath l in
    let cb =
      match decl with
      | OpaqueEff ce ->
        translate_direct_opaque senv.env kn ce
      | DefinitionEff ce ->
        Term_typing.translate_constant senv.env kn (Entries.DefinitionEntry ce)
    in
  let senv, dcb = match cb.const_body with
  | Def _ as const_body -> senv, { cb with const_body }
  | OpaqueDef c ->
    let local = empty_private cb.const_universes in
    let senv, o = push_opaque_proof (Future.from_val (c, local)) senv in
    senv, { cb with const_body = OpaqueDef o }
  | Undef _ | Primitive _ -> assert false
  in
  let senv = add_constant_aux senv (kn, dcb) in
  let eff =
    let from_env = CEphemeron.create (Certificate.make senv) in
    let eff = {
      seff_certif = from_env;
      seff_constant = kn;
      seff_body = cb;
    } in
    SideEffects.add eff empty_private_constants
  in
  (kn, eff), senv

(** Insertion of inductive types *)

let check_mind mie lab =
  let open Entries in
  match mie.mind_entry_inds with
  | [] -> assert false (* empty inductive entry *)
  | oie::_ ->
    (* The label and the first inductive type name should match *)
    assert (Id.equal (Label.to_id lab) oie.mind_entry_typename)

let add_checked_mind kn mib senv =
  let mib =
    match mib.mind_hyps with [] -> Declareops.hcons_mind mib | _ -> mib
  in
  add_field (MutInd.label kn,SFBmind mib) (I kn) senv

let add_mind l mie senv =
  let () = check_mind mie l in
  let kn = MutInd.make2 senv.modpath l in
  let sec_univs = Option.map Section.all_poly_univs  senv.sections
  in
  let mib = Indtypes.check_inductive senv.env ~sec_univs kn mie in
  kn, add_checked_mind kn mib senv

(** Insertion of module types *)

let add_modtype l params_mte inl senv =
  let mp = MPdot(senv.modpath, l) in
  let mtb, cst = Mod_typing.translate_modtype senv.env mp inl params_mte  in
  let senv = push_context_set ~strict:true (Univ.LSet.empty,cst) senv in
  let mtb = Declareops.hcons_module_type mtb in
  let senv = add_field (l,SFBmodtype mtb) MT senv in
  mp, senv

(** full_add_module adds module with universes and constraints *)

let full_add_module mb senv =
  let dp = ModPath.dp mb.mod_mp in
  let linkinfo = Nativecode.link_info_of_dirpath dp in
  { senv with env = Modops.add_linked_module mb linkinfo senv.env }

let full_add_module_type mp mt senv =
  { senv with env = Modops.add_module_type mp mt senv.env }

(** Insertion of modules *)

let add_module l me inl senv =
  let mp = MPdot(senv.modpath, l) in
  let mb, cst = Mod_typing.translate_module senv.env mp inl me in
  let senv = push_context_set ~strict:true (Univ.LSet.empty,cst) senv in
  let mb = Declareops.hcons_module_body mb in
  let senv = add_field (l,SFBmodule mb) M senv in
  let senv =
    if Modops.is_functor mb.mod_type then senv
    else update_resolver (Mod_subst.add_delta_resolver mb.mod_delta) senv
  in
  (mp,mb.mod_delta),senv

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
  let mtb, cst = Mod_typing.translate_modtype senv.env mp inl ([],mte) in
  let senv = push_context_set ~strict:true (Univ.LSet.empty,cst) senv in
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
  let mb, cst =
    Mod_typing.finalize_module senv.env senv.modpath
      (struc,None,senv.modresolver,Univ.Constraint.empty) restype'
  in
  let mb' = functorize_module params mb in
  { mb' with mod_retroknowledge = ModBodyRK senv.local_retroknowledge }, cst

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
  }

let end_module l restype senv =
  let mp = senv.modpath in
  let params, oldsenv = check_struct senv.modvariant in
  let () = check_current_label l mp in
  let () = check_empty_context senv in
  let mbids = List.rev_map fst params in
  let mb, cst = build_module_body params restype senv in
  let senv = push_context_set ~strict:true (Univ.LSet.empty,cst) senv in
  let newenv = Environ.set_opaque_tables oldsenv.env (Environ.opaque_tables senv.env) in
  let newenv = Environ.set_native_symbols newenv senv.env.Environ.native_symbols in
  let newenv = set_engagement_opt newenv senv.engagement in
  let newenv = Environ.set_universes (Environ.universes senv.env) newenv in
  let senv' = propagate_loads { senv with env = newenv } in
  let newenv = Modops.add_module mb newenv in
  let newresolver =
    if Modops.is_functor mb.mod_type then oldsenv.modresolver
    else Mod_subst.add_delta_resolver mb.mod_delta oldsenv.modresolver
  in
  (mp,mbids,mb.mod_delta),
  propagate_senv (l,SFBmodule mb) newenv newresolver senv' oldsenv

let build_mtb mp sign delta =
  { mod_mp = mp;
    mod_expr = ();
    mod_type = sign;
    mod_type_alg = None;
    mod_delta = delta;
    mod_retroknowledge = ModTypeRK }

let end_modtype l senv =
  let mp = senv.modpath in
  let params, oldsenv = check_sig senv.modvariant in
  let () = check_current_label l mp in
  let () = check_empty_context senv in
  let mbids = List.rev_map fst params in
  let newenv = Environ.set_opaque_tables oldsenv.env (Environ.opaque_tables senv.env) in
  let newenv = Environ.set_native_symbols newenv senv.env.Environ.native_symbols in
  let newenv = set_engagement_opt newenv senv.engagement in
  let newenv = Environ.set_universes (Environ.universes senv.env) newenv in
  let senv' = propagate_loads {senv with env=newenv} in
  let auto_tb = functorize params (NoFunctor (List.rev senv.revstruct)) in
  let mtb = build_mtb mp auto_tb senv.modresolver in
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
  let senv = push_context_set ~strict:true (Univ.LSet.empty,cst) senv in
  (* Include Self support  *)
  let rec compute_sign sign mb resolver senv =
    match sign with
    | MoreFunctor(mbid,mtb,str) ->
      let cst_sub = Subtyping.check_subtypes senv.env mb mtb in
      let senv =
        add_constraints
          (Now (Univ.ContextSet.add_constraints cst_sub Univ.ContextSet.empty))
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
    let mtb = build_mtb mp_sup struc senv.modresolver in
    compute_sign sign mtb resolver senv
  in
  let senv = update_resolver (Mod_subst.add_delta_resolver resolver) senv
  in
  let add senv ((l,elem) as field) =
    let new_name = match elem with
      | SFBconst _ ->
        C (Mod_subst.constant_of_delta_kn resolver (KerName.make mp_sup l))
      | SFBmind _ ->
        I (Mod_subst.mind_of_delta_kn resolver (KerName.make mp_sup l))
      | SFBmodule _ -> M
      | SFBmodtype _ -> MT
    in
    add_field ~is_include:true field new_name senv
  in
  resolver, List.fold_left add senv str

(** {6 Libraries, i.e. compiled modules } *)

let module_of_library lib = lib.comp_mod

let univs_of_library lib = lib.comp_univs

type native_library = Nativecode.global list

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

let export ?except ~output_native_objects senv dir =
  let senv = join_safe_environment ?except senv in
  assert(senv.future_cst = []);
  let () = check_current_library dir senv in
  let mp = senv.modpath in
  let str = NoFunctor (List.rev senv.revstruct) in
  let mb =
    { mod_mp = mp;
      mod_expr = FullStruct;
      mod_type = str;
      mod_type_alg = None;
      mod_delta = senv.modresolver;
      mod_retroknowledge = ModBodyRK senv.local_retroknowledge
    }
  in
  let ast, symbols =
    if output_native_objects then
      Nativelibrary.dump_library mp dir senv.env str
    else [], Nativevalues.empty_symbols
  in
  let lib = {
    comp_name = dir;
    comp_mod = mb;
    comp_univs = senv.univ;
    comp_deps = Array.of_list (DPmap.bindings senv.required);
    comp_enga = Environ.engagement senv.env;
    comp_natsymbs = symbols }
  in
  mp, lib, ast

(* cst are the constraints that were computed by the vi2vo step and hence are
 * not part of the [lib.comp_univs] field (but morally should be) *)
let import lib cst vodigest senv =
  check_required senv.required lib.comp_deps;
  check_engagement senv.env lib.comp_enga;
  if DirPath.equal (ModPath.dp senv.modpath) lib.comp_name then
    CErrors.user_err ~hdr:"Safe_typing.import"
     (Pp.strbrk "Cannot load a library with the same name as the current one.");
  let mp = MPfile lib.comp_name in
  let mb = lib.comp_mod in
  let env = Environ.push_context_set ~strict:true
      (Univ.ContextSet.union lib.comp_univs cst)
      senv.env
  in
  let env =
    let linkinfo = Nativecode.link_info_of_dirpath lib.comp_name in
    Modops.add_linked_module mb linkinfo env
  in
  let env = Environ.add_native_symbols lib.comp_name lib.comp_natsymbs env in
  let sections =
    Option.map (Section.map_custom (fun custom ->
        {custom with rev_reimport = (lib,cst,vodigest) :: custom.rev_reimport}))
      senv.sections
  in
  mp,
  { senv with
    env;
    modresolver = Mod_subst.add_delta_resolver mb.mod_delta senv.modresolver;
    required = DPmap.add lib.comp_name vodigest senv.required;
    loads = (mp,mb)::senv.loads;
    sections;
  }

(** {6 Interactive sections *)

let open_section senv =
  let custom = {
    rev_env = senv.env;
    rev_univ = senv.univ;
    rev_objlabels = senv.objlabels;
    rev_reimport = [];
  } in
  let sections = Section.open_section ~custom senv.sections in
  { senv with sections=Some sections }

let close_section senv =
  let open Section in
  let sections0 = get_section senv.sections in
  let env0 = senv.env in
  (* First phase: revert the declarations added in the section *)
  let sections, entries, cstrs, revert = Section.close_section sections0 in
  let rec pop_revstruct accu entries revstruct = match entries, revstruct with
  | [], revstruct -> accu, revstruct
  | _ :: _, [] ->
    CErrors.anomaly (Pp.str "Unmatched section data")
  | entry :: entries, (lbl, leaf) :: revstruct ->
    let data = match entry, leaf with
    | SecDefinition kn, SFBconst cb ->
      let () = assert (Label.equal lbl (Constant.label kn)) in
      `Definition (kn, cb)
    | SecInductive ind, SFBmind mib ->
      let () = assert (Label.equal lbl (MutInd.label ind)) in
      `Inductive (ind, mib)
    | (SecDefinition _ | SecInductive _), (SFBconst _ | SFBmind _) ->
      CErrors.anomaly (Pp.str "Section content mismatch")
    | (SecDefinition _ | SecInductive _), (SFBmodule _ | SFBmodtype _) ->
      CErrors.anomaly (Pp.str "Module inside a section")
    in
    pop_revstruct (data :: accu) entries revstruct
  in
  let redo, revstruct = pop_revstruct [] entries senv.revstruct in
  (* Don't revert the delayed constraints. If some delayed constraints were
     forced inside the section, they have been turned into global monomorphic
     that are going to be replayed. Those that are not forced are not readded
     by {!add_constant_aux}. *)
  let { rev_env = env; rev_univ = univ; rev_objlabels = objlabels; rev_reimport } = revert in
  (* Do not revert the opaque table, the discharged opaque constants are
     referring to it. *)
  let env = Environ.set_opaque_tables env (Environ.opaque_tables senv.env) in
  let senv = { senv with env; revstruct; sections; univ; objlabels; } in
  (* Second phase: replay Requires *)
  let senv = List.fold_left (fun senv (lib,cst,vodigest) -> snd (import lib cst vodigest senv))
      senv (List.rev rev_reimport)
  in
  (* Third phase: replay the discharged section contents *)
  let senv = push_context_set ~strict:true cstrs senv in
  let modlist = Section.replacement_context env0 sections0 in
  let cooking_info seg =
    let { abstr_ctx; abstr_subst; abstr_uctx } = seg in
    let abstract = (abstr_ctx, abstr_subst, abstr_uctx) in
    { Opaqueproof.modlist; abstract }
  in
  let fold senv = function
  | `Definition (kn, cb) ->
    let info = cooking_info (Section.segment_of_constant env0 kn sections0) in
    let r = { Cooking.from = cb; info } in
    let cb = Term_typing.translate_recipe senv.env kn r in
    (* Delayed constants are already in the global environment *)
    add_constant_aux senv (kn, cb)
  | `Inductive (ind, mib) ->
    let info = cooking_info (Section.segment_of_inductive env0 ind sections0) in
    let mib = Cooking.cook_inductive info mib in
    add_checked_mind ind mib senv
  in
  List.fold_left fold senv redo

(** {6 Safe typing } *)

type judgment = Environ.unsafe_judgment

let j_val j = j.Environ.uj_val
let j_type j = j.Environ.uj_type

let typing senv = Typeops.infer (env_of_senv senv)

(** {6 Retroknowledge / native compiler } *)

let register_inline kn senv =
  let open Environ in
  if not (evaluable_constant kn senv.env) then
    CErrors.user_err Pp.(str "Register inline: an evaluable constant is expected");
  let env = senv.env in
  let cb = lookup_constant kn env in
  let cb = {cb with const_inline_code = true} in
  let env = add_constant kn cb env in { senv with env}

let check_register_ind (type t) ind (r : t CPrimitives.prim_ind) env =
  let (mb,ob as spec) = Inductive.lookup_mind_specif env ind in
  let check_if b msg =
    if not b then
      CErrors.user_err ~hdr:"check_register_ind" msg in
  check_if (Int.equal (Array.length mb.mind_packets) 1) Pp.(str "A non mutual inductive is expected");
  let is_monomorphic = function Monomorphic _ -> true | Polymorphic _ -> false in
  check_if (is_monomorphic mb.mind_universes) Pp.(str "A universe monomorphic inductive type is expected");
  check_if (not @@ Inductive.is_private spec) Pp.(str "A non-private inductive type is expected");
  let check_nparams n =
    check_if (Int.equal mb.mind_nparams n) Pp.(str "An inductive type with " ++ int n ++ str " parameters is expected")
  in
  let check_nconstr n =
    check_if (Int.equal (Array.length ob.mind_consnames) n)
      Pp.(str "an inductive type with " ++ int n ++ str " constructors is expected")
  in
  let check_name pos s =
    check_if (Id.equal ob.mind_consnames.(pos) (Id.of_string s))
      Pp.(str"the " ++ int (pos + 1) ++ str
       "th constructor does not have the expected name: " ++ str s) in
  let check_type pos t =
    check_if (Constr.equal t ob.mind_user_lc.(pos))
      Pp.(str"the " ++ int (pos + 1) ++ str
       "th constructor does not have the expected type") in
  let check_type_cte pos = check_type pos (Constr.mkRel 1) in
  match r with
  | CPrimitives.PIT_bool ->
    check_nparams 0;
    check_nconstr 2;
    check_name 0 "true";
    check_type_cte 0;
    check_name 1 "false";
    check_type_cte 1
  | CPrimitives.PIT_carry ->
    check_nparams 1;
    check_nconstr 2;
    let test_type pos =
      let c = ob.mind_user_lc.(pos) in
      let s = Pp.(str"the " ++ int (pos + 1) ++ str
              "th constructor does not have the expected type") in
      check_if (Constr.isProd c) s;
      let (_,d,cd) = Constr.destProd c in
      check_if (Constr.is_Type d) s;
      check_if
        (Constr.equal
                (mkProd (Context.anonR,mkRel 1, mkApp (mkRel 3,[|mkRel 2|])))
                cd)
        s in
    check_name 0 "C0";
    test_type 0;
    check_name 1 "C1";
    test_type 1;
  | CPrimitives.PIT_pair ->
    check_nparams 2;
    check_nconstr 1;
    check_name 0 "pair";
    let c = ob.mind_user_lc.(0) in
    let s =  Pp.str "the constructor does not have the expected type" in
    begin match Term.decompose_prod c with
      | ([_,b;_,a;_,_B;_,_A], codom) ->
        check_if (is_Type _A) s;
        check_if (is_Type _B) s;
        check_if (Constr.equal a (mkRel 2)) s;
        check_if (Constr.equal b (mkRel 2)) s;
        check_if (Constr.equal codom (mkApp (mkRel 5,[|mkRel 4; mkRel 3|]))) s
      | _ -> check_if false s
    end
  | CPrimitives.PIT_cmp ->
    check_nparams 0;
    check_nconstr 3;
    check_name 0 "Eq";
    check_type_cte 0;
    check_name 1 "Lt";
    check_type_cte 1;
    check_name 2 "Gt";
    check_type_cte 2
  | CPrimitives.PIT_f_cmp ->
    check_nconstr 4;
    check_name 0 "FEq";
    check_type_cte 0;
    check_name 1 "FLt";
    check_type_cte 1;
    check_name 2 "FGt";
    check_type_cte 2;
    check_name 3 "FNotComparable";
    check_type_cte 3
  | CPrimitives.PIT_f_class ->
    check_nconstr 9;
    check_name 0 "PNormal";
    check_type_cte 0;
    check_name 1 "NNormal";
    check_type_cte 1;
    check_name 2 "PSubn";
    check_type_cte 2;
    check_name 3 "NSubn";
    check_type_cte 3;
    check_name 4 "PZero";
    check_type_cte 4;
    check_name 5 "NZero";
    check_type_cte 5;
    check_name 6 "PInf";
    check_type_cte 6;
    check_name 7 "NInf";
    check_type_cte 7;
    check_name 8 "NaN";
    check_type_cte 8

let register_inductive ind prim senv =
  check_register_ind ind prim senv.env;
  let action = Retroknowledge.Register_ind(prim,ind) in
  add_retroknowledge action senv

let add_constraints c =
  add_constraints
    (Now (Univ.ContextSet.add_constraints c Univ.ContextSet.empty))


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

let set_strategy k l e = { e with env =
   (Environ.set_oracle e.env
      (Conv_oracle.set_strategy (Environ.oracle e.env) k l)) }
