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
  let flags =
    { (Environ.typing_flags env) with
      check_guarded = flags.check_guarded;
      check_positive = flags.check_positive;
      check_universes = flags.check_universes;
      conv_oracle = flags.conv_oracle;
      cumulative_sprop = flags.cumulative_sprop;
    }
  in
  Environ.set_typing_flags flags env
