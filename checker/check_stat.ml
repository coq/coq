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
  let csts = List.map Constant.to_string opac in
  pr_assumptions "Axioms" csts

(* A module operation records the checks it skipped on the module it produced,
   because they belong to no declaration: the constant an inlined body came
   from is gone, and a subtyping check is not a declaration at all. So the
   flags a declaration is subject to are its own, weakened by those of every
   module it sits in (#12155, #16646). *)
let effective_flags env =
  let cache = ref ModPath.Map.empty in
  let rec modpath_flags mp =
    match ModPath.Map.find_opt mp !cache with
    | Some flags -> flags
    | None ->
      let flags = match mp with
      | MPfile _ | MPbound _ -> Declareops.safe_flags Conv_oracle.empty
      | MPdot (mp', _) ->
        let outer = modpath_flags mp' in
        match Environ.lookup_module mp env with
        | mb -> Declareops.weaken_checks ~weak:(Mod_declarations.mod_typing_flags mb) outer
        | exception Not_found -> outer
      in
      let () = cache := ModPath.Map.add mp flags !cache in
      flags
  in
  fun mp flags -> Declareops.weaken_checks ~weak:(modpath_flags mp) flags

let fold_flagged env f acc =
  let eff = effective_flags env in
  let acc =
    fold_constants (fun c cb acc ->
        f (Constant.to_string c) (eff (Constant.modpath c) cb.const_typing_flags) acc)
      env acc
  in
  fold_inductives (fun c cb acc ->
      f (MutInd.to_string c) (eff (MutInd.modpath c) cb.mind_typing_flags) acc)
    env acc

let pr_flagged env name test =
  pr_assumptions name
    (fold_flagged env (fun s flags acc -> if test flags then s :: acc else acc) [])

let pr_type_in_type env =
  pr_flagged env "Constants/Inductives relying on type-in-type"
    (fun flags -> not flags.check_universes)

let pr_unguarded env =
  pr_flagged env "Constants/Inductives relying on unsafe (co)fixpoints"
    (fun flags -> not flags.check_guarded)

let pr_nonpositive env =
  let eff = effective_flags env in
  let inds =
    fold_inductives (fun c cb acc ->
        if not (eff (MutInd.modpath c) cb.mind_typing_flags).check_positive
        then MutInd.to_string c :: acc else acc)
      env []
  in
  pr_assumptions "Inductives whose positivity is assumed" inds

let pr_indices_matter env =
  let inds = fold_inductives (fun c cb acc ->
    if cb.mind_typing_flags.indices_matter then acc
    else if Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) cb.mind_packets
    then MutInd.to_string c :: acc
    else acc) env [] in
  pr_assumptions "Inductives relying on indices not mattering" inds

let print_context env opac = match opac with
| None -> ()
| Some opac ->
  Feedback.msg_notice
    (hov 0
    (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
    str"===============" ++ fnl() ++ fnl() ++
    str "* " ++ hov 0 (pr_impredicative_set env ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_rewrite_rules env ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_axioms env opac ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_type_in_type env ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_unguarded env ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_nonpositive env ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_indices_matter env ++ fnl()))
    )

let stats env opac =
  print_context env opac;
  print_memory_stat ()
