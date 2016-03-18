(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

(** *******************************************************************)
(** Grammar entry for binding a constant to the printing hook         *)
(** *******************************************************************)

(** Checks whether the candidate printing function
    both is a constant and has (at least) two arguments
 *)
let check_valid_print_ref x =
  (* First check if it has enough arguments *)
  let (typ_x,_) = Universes.type_of_global x in
  let env = Global.env () in
  let (list_prods,_) = Reductionops.splay_prod env Evd.empty typ_x in
  if List.length list_prods < 2 then
    Errors.errorlabstrm "" (Pp.strbrk "Printing function should have at least two arguments (it will print the second).");
  (* Then check if it is a constant*)
  if not(Globnames.isConstRef x) then
    Errors.errorlabstrm "" (Pp.strbrk "Printing function should be a constant.")

let declare_printing_effects print_ref =
  let print_ref = Smartlocate.global_with_alias print_ref in
  check_valid_print_ref print_ref;
  Print_hook.set_print_ref print_ref

VERNAC COMMAND EXTEND PrintingEffect CLASSIFIED AS SIDEFF
| [ "Declare" "Printing" "Effect" global(print_ref) ] ->
    [ declare_printing_effects print_ref ]
END
