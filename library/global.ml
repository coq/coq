(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  val is_joined_environment : unit -> bool
  val global_env_summary_tag : Safe_typing.safe_environment Summary.Dyn.tag

end = struct

let global_env, global_env_summary_tag =
  Summary.ref_tag ~name:global_env_summary_name Safe_typing.empty_environment

let is_joined_environment () =
  Safe_typing.is_joined_environment !global_env

let assert_not_parsing () =
  if !Flags.we_are_parsing then
    CErrors.anomaly (
      Pp.strbrk"The global environment cannot be accessed during parsing.")

let safe_env () = assert_not_parsing(); !global_env

let set_safe_env e = global_env := e

end

let global_env_summary_tag = GlobalSafeEnv.global_env_summary_tag

let safe_env = GlobalSafeEnv.safe_env
let is_joined_environment = GlobalSafeEnv.is_joined_environment

let env () = Safe_typing.env_of_safe_env (safe_env ())

let env_is_initial () = Safe_typing.is_initial (safe_env ())

(** Turn ops over the safe_environment state monad to ops on the global env *)

let globalize0 f = GlobalSafeEnv.set_safe_env (f (safe_env ()))

let globalize f =
  let res,env = f (safe_env ()) in GlobalSafeEnv.set_safe_env env; res

let globalize0_with_summary fs f =
  let env = f (safe_env ()) in
  Summary.unfreeze_summaries fs;
  GlobalSafeEnv.set_safe_env env

let globalize_with_summary fs f =
  let res,env = f (safe_env ()) in
  Summary.unfreeze_summaries fs;
  GlobalSafeEnv.set_safe_env env;
  res

(** [Safe_typing] operations, now operating on the global environment *)

let i2l = Label.of_id

let push_named_assum a = globalize0 (Safe_typing.push_named_assum a)
let push_named_def d = globalize0 (Safe_typing.push_named_def d)
let push_section_context c = globalize0 (Safe_typing.push_section_context c)
let add_constraints c = globalize0 (Safe_typing.add_constraints c)
let push_context_set ~strict c = globalize0 (Safe_typing.push_context_set ~strict c)

let set_impredicative_set c = globalize0 (Safe_typing.set_impredicative_set c)
let set_indices_matter b = globalize0 (Safe_typing.set_indices_matter b)
let set_typing_flags c = globalize0 (Safe_typing.set_typing_flags c)
let set_check_guarded c = globalize0 (Safe_typing.set_check_guarded c)
let set_check_positive c = globalize0 (Safe_typing.set_check_positive c)
let set_check_universes c = globalize0 (Safe_typing.set_check_universes c)
let typing_flags () = Environ.typing_flags (env ())
let set_cumulative_sprop b =
  set_typing_flags {(typing_flags()) with Declarations.cumulative_sprop = b}
let is_cumulative_sprop () = (typing_flags()).Declarations.cumulative_sprop
let set_allow_sprop b = globalize0 (Safe_typing.set_allow_sprop b)
let sprop_allowed () = Environ.sprop_allowed (env())
let export_private_constants cd = globalize (Safe_typing.export_private_constants cd)
let add_constant ?typing_flags id d = globalize (Safe_typing.add_constant ?typing_flags (i2l id) d)
let add_private_constant id u d = globalize (Safe_typing.add_private_constant (i2l id) u d)
let fill_opaque c = globalize0 (Safe_typing.fill_opaque c)
let add_mind ?typing_flags id mie = globalize (Safe_typing.add_mind ?typing_flags (i2l id) mie)
let add_modtype id me inl = globalize (Safe_typing.add_modtype (i2l id) me inl)
let add_module id me inl = globalize (Safe_typing.add_module (i2l id) me inl)
let add_include me ismod inl = globalize (Safe_typing.add_include me ismod inl)

let open_section () = globalize0 Safe_typing.open_section
let close_section fs = globalize0_with_summary fs Safe_typing.close_section
let sections_are_opened () = Safe_typing.sections_are_opened (safe_env())

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
let universes_lbound () = universes_lbound (env())
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

type indirect_accessor = {
  access_proof : Opaqueproof.opaque -> (Constr.t * unit Opaqueproof.delayed_universes) option;
}

let force_proof access o = match access.access_proof o with
| None -> CErrors.user_err Pp.(str "Cannot access opaque delayed proof")
| Some (c, u) -> (c, u)

let body_of_constant_body access env cb =
  let open Declarations in
  match cb.const_body with
  | Undef _ | Primitive _ ->
     None
  | Def c ->
    let u = match cb.const_universes with
    | Monomorphic -> Opaqueproof.PrivateMonomorphic ()
    | Polymorphic auctx -> Opaqueproof.PrivatePolymorphic Univ.ContextSet.empty
    in
    Some (c, u, Declareops.constant_polymorphic_context cb)
  | OpaqueDef o ->
    let c, u = force_proof access o in
    Some (c, u, Declareops.constant_polymorphic_context cb)

let body_of_constant_body access ce = body_of_constant_body access (env ()) ce

let body_of_constant access cst = body_of_constant_body access (lookup_constant cst)

(** Operations on kernel names *)

let constant_of_delta_kn kn =
  Safe_typing.constant_of_delta_kn_senv (safe_env ()) kn

let mind_of_delta_kn kn =
  Safe_typing.mind_of_delta_kn_senv (safe_env ()) kn

(** Operations on libraries *)

let start_library dir = globalize (Safe_typing.start_library dir)
let export ~output_native_objects s =
  Safe_typing.export ~output_native_objects (safe_env ()) s
let import c u d = globalize (Safe_typing.import c u d)


(** Function to get an environment from the constants part of the global
    environment and a given context. *)

let env_of_context hyps =
  reset_with_named_context hyps (env())

let is_polymorphic r = Environ.is_polymorphic (env()) r

let is_template_polymorphic r = is_template_polymorphic (env ()) r

let get_template_polymorphic_variables r = get_template_polymorphic_variables (env ()) r

let is_type_in_type r = is_type_in_type (env ()) r

let current_modpath () =
  Safe_typing.current_modpath (safe_env ())

let current_dirpath () =
  Safe_typing.current_dirpath (safe_env ())

let with_global f =
  let (a, ctx) = f (env ()) (current_dirpath ()) in
  push_context_set ~strict:true ctx; a

let register_inline c = globalize0 (Safe_typing.register_inline c)
let register_inductive c r = globalize0 (Safe_typing.register_inductive c r)

let set_strategy k l =
  globalize0 (Safe_typing.set_strategy k l)

let set_share_reduction b =
  globalize0 (Safe_typing.set_share_reduction b)

let set_VM b = globalize0 (Safe_typing.set_VM b)
let set_native_compiler b = globalize0 (Safe_typing.set_native_compiler b)
