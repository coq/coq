(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ

(** We introduce here the global environment of the system,
    and we declare it as a synchronized table. *)

let global_env_summary_name = "Global environment"

module GlobalSafeEnv : sig

  val safe_env : unit -> Safe_typing.safe_environment
  val set_safe_env : Safe_typing.safe_environment -> unit
  val join_safe_environment : ?except:Future.UUIDSet.t -> unit -> unit
  val is_joined_environment : unit -> bool
  val global_env_summary_tag : Safe_typing.safe_environment Summary.Dyn.tag

end = struct

let global_env = ref Safe_typing.empty_environment

let join_safe_environment ?except () =
  global_env := Safe_typing.join_safe_environment ?except !global_env

let is_joined_environment () =
  Safe_typing.is_joined_environment !global_env

let global_env_summary_tag =
  Summary.declare_summary_tag global_env_summary_name
    { Summary.freeze_function = (function
        | `Yes -> join_safe_environment (); !global_env
        | `No -> !global_env
        | `Shallow -> !global_env);
      unfreeze_function = (fun fr -> global_env := fr);
      init_function = (fun () -> global_env := Safe_typing.empty_environment) }

let assert_not_parsing () =
  if !Flags.we_are_parsing then
    CErrors.anomaly (
      Pp.strbrk"The global environment cannot be accessed during parsing.")

let safe_env () = assert_not_parsing(); !global_env

let set_safe_env e = global_env := e

end

let global_env_summary_tag = GlobalSafeEnv.global_env_summary_tag

let safe_env = GlobalSafeEnv.safe_env
let join_safe_environment ?except () =
  GlobalSafeEnv.join_safe_environment ?except ()
let is_joined_environment = GlobalSafeEnv.is_joined_environment

let env () = Safe_typing.env_of_safe_env (safe_env ())

let env_is_initial () = Safe_typing.is_initial (safe_env ())

(** Turn ops over the safe_environment state monad to ops on the global env *)

let globalize0 f = GlobalSafeEnv.set_safe_env (f (safe_env ()))

let globalize f =
  let res,env = f (safe_env ()) in GlobalSafeEnv.set_safe_env env; res

let globalize_with_summary fs f =
  let res,env = f (safe_env ()) in
  Summary.unfreeze_summaries fs;
  GlobalSafeEnv.set_safe_env env;
  res

(** [Safe_typing] operations, now operating on the global environment *)

let i2l = Label.of_id

let push_named_assum a = globalize0 (Safe_typing.push_named_assum a)
let push_named_def d = globalize0 (Safe_typing.push_named_def d)
let add_constraints c = globalize0 (Safe_typing.add_constraints c)
let push_context_set b c = globalize0 (Safe_typing.push_context_set b c)
let push_context b c = globalize0 (Safe_typing.push_context b c)

let set_engagement c = globalize0 (Safe_typing.set_engagement c)
let set_typing_flags c = globalize0 (Safe_typing.set_typing_flags c)
let typing_flags () = Environ.typing_flags (env ())
let export_private_constants ~in_section cd = globalize (Safe_typing.export_private_constants ~in_section cd)
let add_constant dir id d = globalize (Safe_typing.add_constant dir (i2l id) d)
let add_mind dir id mie = globalize (Safe_typing.add_mind dir (i2l id) mie)
let add_modtype id me inl = globalize (Safe_typing.add_modtype (i2l id) me inl)
let add_module id me inl = globalize (Safe_typing.add_module (i2l id) me inl)
let add_include me ismod inl = globalize (Safe_typing.add_include me ismod inl)

let start_module id = globalize (Safe_typing.start_module (i2l id))
let start_modtype id = globalize (Safe_typing.start_modtype (i2l id))

let end_module fs id mtyo =
  globalize_with_summary fs (Safe_typing.end_module (i2l id) mtyo)

let end_modtype fs id =
  globalize_with_summary fs (Safe_typing.end_modtype (i2l id))

let add_module_parameter mbid mte inl =
  globalize (Safe_typing.add_module_parameter mbid mte inl)

(** Queries on the global environment *)

let universes () = universes (env())
let named_context () = named_context (env())
let named_context_val () = named_context_val (env())

let lookup_named id = lookup_named id (env())
let lookup_constant kn = lookup_constant kn (env())
let lookup_inductive ind = Inductive.lookup_mind_specif (env()) ind
let lookup_pinductive (ind,_) = Inductive.lookup_mind_specif (env()) ind
let lookup_mind kn = lookup_mind kn (env())

let lookup_module mp = lookup_module mp (env())
let lookup_modtype kn = lookup_modtype kn (env())

let exists_objlabel id = Safe_typing.exists_objlabel id (safe_env ())

let opaque_tables () = Environ.opaque_tables (env ())

let instantiate cb c =
  let open Declarations in
  match cb.const_universes with
  | Monomorphic_const _ -> c, Univ.AUContext.empty
  | Polymorphic_const ctx -> c, ctx

let body_of_constant_body cb =
  let open Declarations in
  let otab = opaque_tables () in
  match cb.const_body with
  | Undef _ -> None
  | Def c -> Some (instantiate cb (Mod_subst.force_constr c))
  | OpaqueDef o -> Some (instantiate cb (Opaqueproof.force_proof otab o))

let body_of_constant cst = body_of_constant_body (lookup_constant cst)

(** Operations on kernel names *)

let constant_of_delta_kn kn =
  let resolver,resolver_param = Safe_typing.delta_of_senv (safe_env ())
  in
  (* TODO : are resolver and resolver_param orthogonal ?
     the effect of resolver is lost if resolver_param isn't
     trivial at that spot. *)
  Mod_subst.constant_of_deltas_kn resolver_param resolver kn

let mind_of_delta_kn kn =
  let resolver,resolver_param = Safe_typing.delta_of_senv (safe_env ())
  in
  (* TODO idem *)
  Mod_subst.mind_of_deltas_kn resolver_param resolver kn

(** Operations on libraries *)

let start_library dir = globalize (Safe_typing.start_library dir)
let export ?except s = Safe_typing.export ?except (safe_env ()) s
let import c u d = globalize (Safe_typing.import c u d)


(** Function to get an environment from the constants part of the global
    environment and a given context. *)

let env_of_context hyps =
  reset_with_named_context hyps (env())

open Globnames

(** Build a fresh instance for a given context, its associated substitution and 
    the instantiated constraints. *)

let constr_of_global_in_context env r =
  let open Constr in
  match r with
  | VarRef id -> mkVar id, Univ.AUContext.empty
  | ConstRef c ->
    let cb = Environ.lookup_constant c env in
    let univs = Declareops.constant_polymorphic_context cb in
    mkConstU (c, Univ.make_abstract_instance univs), univs
  | IndRef ind ->
    let (mib, oib as specif) = Inductive.lookup_mind_specif env ind in
    let univs = Declareops.inductive_polymorphic_context mib in
    mkIndU (ind, Univ.make_abstract_instance univs), univs
  | ConstructRef cstr ->
    let (mib,oib as specif) =
      Inductive.lookup_mind_specif env (inductive_of_constructor cstr)
    in
    let univs = Declareops.inductive_polymorphic_context mib in
    mkConstructU (cstr, Univ.make_abstract_instance univs), univs

let type_of_global_in_context env r = 
  match r with
  | VarRef id -> Environ.named_type id env, Univ.AUContext.empty
  | ConstRef c -> 
    let cb = Environ.lookup_constant c env in 
    let univs = Declareops.constant_polymorphic_context cb in
    cb.Declarations.const_type, univs
  | IndRef ind ->
    let (mib, oib as specif) = Inductive.lookup_mind_specif env ind in
    let univs = Declareops.inductive_polymorphic_context mib in
    let inst = Univ.make_abstract_instance univs in
    let env = Environ.push_context ~strict:false (Univ.AUContext.repr univs) env in
    Inductive.type_of_inductive env (specif, inst), univs
  | ConstructRef cstr ->
    let (mib,oib as specif) =
      Inductive.lookup_mind_specif env (inductive_of_constructor cstr) 
    in
    let univs = Declareops.inductive_polymorphic_context mib in
    let inst = Univ.make_abstract_instance univs in
    Inductive.type_of_constructor (cstr,inst) specif, univs

let universes_of_global env r = 
    match r with
    | VarRef id -> Univ.AUContext.empty
    | ConstRef c -> 
      let cb = Environ.lookup_constant c env in 
      Declareops.constant_polymorphic_context cb
    | IndRef ind ->
      let (mib, oib) = Inductive.lookup_mind_specif env ind in
      Declareops.inductive_polymorphic_context mib
    | ConstructRef cstr ->
      let (mib,oib) = 
        Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
      Declareops.inductive_polymorphic_context mib

let universes_of_global gr = 
  universes_of_global (env ()) gr

let is_polymorphic r =
  let env = env() in 
  match r with
  | VarRef id -> false
  | ConstRef c -> Environ.polymorphic_constant c env
  | IndRef ind -> Environ.polymorphic_ind ind env
  | ConstructRef cstr -> Environ.polymorphic_ind (inductive_of_constructor cstr) env

let is_template_polymorphic r = 
  let env = env() in 
  match r with
  | VarRef id -> false
  | ConstRef c -> false
  | IndRef ind -> Environ.template_polymorphic_ind ind env
  | ConstructRef cstr -> Environ.template_polymorphic_ind (inductive_of_constructor cstr) env

let is_type_in_type r =
  let env = env() in
  match r with
  | VarRef id -> false
  | ConstRef c -> Environ.type_in_type_constant c env
  | IndRef ind -> Environ.type_in_type_ind ind env
  | ConstructRef cstr -> Environ.type_in_type_ind (inductive_of_constructor cstr) env

let current_modpath () =
  Safe_typing.current_modpath (safe_env ())

let current_dirpath () = 
  Safe_typing.current_dirpath (safe_env ())

let with_global f = 
  let (a, ctx) = f (env ()) (current_dirpath ()) in
    push_context_set false ctx; a

(* spiwack: register/unregister functions for retroknowledge *)
let register field value by_clause =
  globalize0 (Safe_typing.register field value by_clause)

let register_inline c = globalize0 (Safe_typing.register_inline c)

let set_strategy k l =
  GlobalSafeEnv.set_safe_env (Safe_typing.set_strategy (safe_env ()) k l)

let set_reduction_sharing b =
  let env = safe_env () in
  let flags = Environ.typing_flags (Safe_typing.env_of_safe_env env) in
  let flags = { flags with Declarations.share_reduction = b } in
  let env = Safe_typing.set_typing_flags flags env in
  GlobalSafeEnv.set_safe_env env
