(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations

let set_local_flags flags env =
  (* Explicitly ignored flags have been commented out *)
  let flags =
    { (Environ.typing_flags env) with
      check_guarded = flags.check_guarded;
      check_positive = flags.check_positive;
      check_universes = flags.check_universes;
      conv_oracle = flags.conv_oracle;
      share_reduction = flags.share_reduction;
      enable_VM = flags.enable_VM;
      (* enable_native_compiler = flags.enable_native_compiler; *)
      (* indices_matter = flags.indices_matter; *)
      (* impredicative_set = flags.impredicative_set; *)
      (* sprop_allowed = flags.sprop_allowed; *)
      cumulative_sprop = flags.cumulative_sprop;
      allow_uip = flags.allow_uip;
    }
  in
  Environ.set_typing_flags flags env
