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

let pr_impredicative_set env =
  if is_impredicative_set env then str "Theory: Set is impredicative"
  else str "Theory: Set is predicative"

let pr_rewrite_rules env =
  if rewrite_rules_allowed env then str "Theory: Rewrite rules are allowed (consistency, subject reduction, confluence and normalization might be broken)"
  else str "Theory: Rewrite rules are not allowed"

let pr_assumptions ass axs =
  if axs = [] then
    str ass ++ str ": <none>"
  else
    hv 2 (str ass ++ str ":" ++ fnl() ++ prlist_with_sep fnl str axs)

let pr_axioms env opac =
  let add c cb acc =
    if Declareops.constant_has_body cb then acc else
      match Cmap.find_opt c opac with
      | None -> Cset.add c acc
      | Some s -> Cset.union s acc in
  let csts = fold_constants add env Cset.empty in
  let csts = Cset.fold (fun c acc -> Constant.to_string c :: acc) csts [] in
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

let print_context env opac =
  if !output_context then begin
    Feedback.msg_notice
      (hov 0
      (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
      str"===============" ++ fnl() ++ fnl() ++
      str "* " ++ hov 0 (pr_impredicative_set env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_rewrite_rules env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_axioms env opac ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_type_in_type env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_unguarded env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_nonpositive env ++ fnl()))
      )
  end

let stats env opac =
  print_context env opac;
  print_memory_stat ()
