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

let set_local_flags flags env =
  (* Explicitly ignored flags are set to not change *)
  let envflags = Environ.typing_flags env in
  let flags = {
    (* These flags may be overridden, but only downwards: the env may already
       be recording checks that the enclosing module operation skipped, and a
       declaration cannot ask for those back. *)
    check_guarded = flags.check_guarded && envflags.check_guarded;
    check_positive = flags.check_positive && envflags.check_positive;
    check_universes = flags.check_universes && envflags.check_universes;
    check_eliminations = flags.check_eliminations && envflags.check_eliminations;
    conv_oracle = flags.conv_oracle;
    share_reduction = flags.share_reduction;
    unfold_dep_heuristic = flags.unfold_dep_heuristic;
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

(* Modules record the checks their own operation performed, not the flags some
   declaration was written under, so only the checks are taken from them: the
   oracle, sharing and allow_uip belong to the declarations. *)
let weaken_checks flags env =
  let envflags = Environ.typing_flags env in
  Environ.set_typing_flags (Declareops.weaken_checks ~weak:flags envflags) env
