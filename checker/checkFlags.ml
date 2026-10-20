(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations

let axiom_free = ref false

let flags_are_safe flags =
  flags.check_guarded && flags.check_positive && flags.check_universes &&
  flags.check_eliminations && not flags.allow_uip

let set_local_flags flags env =
  if !axiom_free && not (flags_are_safe flags) then
    CErrors.user_err Pp.(str "Axioms or unsafe features found (-axiom-free).");
  (* Explicitly ignored flags are set to not change *)
  let envflags = Environ.typing_flags env in
  let flags = {
    (* These flags may be overridden *)
    check_guarded = flags.check_guarded;
    check_positive = flags.check_positive;
    check_universes = flags.check_universes;
    check_eliminations = flags.check_eliminations;
    conv_oracle = flags.conv_oracle;
    share_reduction = flags.share_reduction;
    unfold_dep_heuristic = flags.unfold_dep_heuristic;
    unfold_height_heuristic = flags.unfold_height_heuristic;
    allow_uip = flags.allow_uip;
    (* These flags may not *)
    enable_VM = envflags.enable_VM;
    enable_native_compiler = envflags.enable_native_compiler;
    indices_matter = envflags.indices_matter;
    impredicative_set = envflags.impredicative_set;
    sprop_allowed = envflags.sprop_allowed;
  }
  in
  Environ.set_typing_flags flags env

(* Set from the -bytecode-compiler command line option. The checker consults
   this rather than the environment's flag when deciding whether to recompile
   the VM bytecode of a library. *)
let enable_vm = ref false

let is_axiom_free env opac =
  let open Environ in
  let safe_constants = fold_constants (fun _ cb safe ->
    safe && flags_are_safe cb.const_typing_flags) env true in
  let safe_inductives = fold_inductives (fun _ mib safe ->
    safe && flags_are_safe mib.mind_typing_flags)
    env true in
  let primitive c =
    is_primitive_type env c || match lookup_constant_opt c env with
    | Some { const_body = Primitive _; _ } -> true
    | Some _ | None -> false
  in
  List.for_all primitive opac &&
  safe_constants && safe_inductives &&
  not (rewrite_rules_allowed env)
