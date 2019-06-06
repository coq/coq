(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Declarations
open Environ

let memory_stat = ref false

let print_memory_stat () =
  if !memory_stat then begin
    Format.printf "total heap size = %d kbytes\n" (CObj.heap_size_kb ());
    Format.print_newline();
    Format.print_flush()
  end

let output_context = ref false

let pr_engagement env =
  begin
    match engagement env with
    | ImpredicativeSet -> str "Theory: Set is impredicative"
    | PredicativeSet -> str "Theory: Set is predicative"
  end

let is_ax _ cb = not (Declareops.constant_has_body cb)

let pr_ax env =
  let axs = fold_constants (fun c ce acc -> if is_ax c ce then c::acc else acc) env [] in
  if axs = [] then
    str "Axioms: <none>"
  else
    hv 2 (str "Axioms:" ++ fnl() ++ prlist_with_sep fnl Constant.print axs)

let print_context env =
  if !output_context then begin
    Feedback.msg_notice
      (hov 0
      (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
      str"===============" ++ fnl() ++ fnl() ++
      str "* " ++ hov 0 (pr_engagement env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_ax env)));
  end

let stats env =
  print_context env;
  print_memory_stat ()
