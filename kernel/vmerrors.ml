(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp

type error =
  | TooLargeInductive of Names.Id.t
  | TooLargeCode


exception CompileError of error

let too_large_code () = raise (CompileError TooLargeCode)

(* Limit needed to make SWITCH work. The specific limit is
   arbitrary but nobody needs more than 0x1000000 constructors. *)

let max_nb_const = 0x1000000
let max_nb_block = 0x1000000 + Obj.last_non_constant_constructor_tag - 1

let str_max_constructors =
  Format.sprintf
    " which has more than %i constant constructors or more than %i non-constant constructors" max_nb_const max_nb_block

(* NB: Declarations depends on Vmemitcodes which depends on
   too_large_code so we can't use Declarations.one_inductive_body
   here. Instead we pass the needed fields. *)
let check_compilable_ind ~name ~mind_nb_args ~mind_nb_constant =
  if not (mind_nb_args <= max_nb_block && mind_nb_constant <= max_nb_const) then
    raise (CompileError (TooLargeInductive name))

let pr_error = function
  | TooLargeCode -> str "Cannot compile code for virtual machine as it exceeds string size limits."
  | TooLargeInductive name ->
    str "Cannot compile code for virtual machine as it uses inductive " ++
    Names.Id.print name ++ str str_max_constructors

let () = CErrors.register_handler (function
    | CompileError e -> Some (pr_error e)
    | _ -> None)
