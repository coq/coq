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


let pr_assumptions ass axs =
  if axs = [] then
    str ass ++ str ": <none>"
  else
    hv 2 (str ass ++ str ":" ++ fnl() ++ prlist_with_sep fnl str axs)

let pr_axioms env =
  let csts = fold_constants (fun c cb acc -> if not (Declareops.constant_has_body cb) then Constant.to_string c :: acc else acc) env [] in
  pr_assumptions "Axioms" csts

let pr_type_in_type env =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_universes then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_universes then MutInd.to_string c :: acc else acc) env csts in
  pr_assumptions "Constants/Inductives relying on type-in-type" csts

let pr_unguarded env =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_guarded then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_guarded then MutInd.to_string c :: acc else acc) env csts in
  pr_assumptions "Constants/Inductives relying on unsafe (co)fixpoints" csts

let pr_nonpositive env =
  let inds = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_positive then MutInd.to_string c :: acc else acc) env [] in
  pr_assumptions "Inductives whose positivity is assumed" inds


let print_context env =
  if !output_context then begin
    Feedback.msg_notice
      (hov 0
      (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
      str"===============" ++ fnl() ++ fnl() ++
      str "* " ++ hov 0 (pr_engagement env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_axioms env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_type_in_type env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_unguarded env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_nonpositive env)))
  end

let stats env =
  print_context env;
  print_memory_stat ()
