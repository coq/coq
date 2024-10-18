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
open CErrors
open Notation

(* Register the grammar of notation for parsing and printing
   (also register the parsing rule if not onlyprinting) *)

let notation_grammar_map = Summary.ref ~stage:Summary.Stage.Synterp ~name:"notation_grammar_map" NotationMap.empty

let declare_notation_grammar ntn rule =
  try
    let _ = NotationMap.find ntn !notation_grammar_map in
    anomaly (str "Notation " ++ pr_notation ntn ++ str " is already assigned a grammar.")
  with Not_found ->
  notation_grammar_map := NotationMap.add ntn rule !notation_grammar_map

let grammar_of_notation ntn =
  NotationMap.find ntn !notation_grammar_map

let list_prefixes ntn =
  let rec aux inrec = function
    | [] -> []
    | s :: symbols ->
       let nt, inrec = match s with
         | NonTerminal _ -> (if inrec then 0 else 1), false
         | Terminal s when String.equal s (Names.Id.to_string Notation_ops.ldots_var) -> 0, true
           (* the above is horribly hackish but we plan to rewrite recursive notations soon anyway *)
         | Terminal _ | SProdList _ | Break _ -> 0, inrec in
       ([s], nt) :: List.map (fun (l, k) -> s :: l, k + nt) (aux inrec symbols) in
  let entry, symbols = decompose_notation_key ntn in
  let symbols = match symbols with
    (* don't consider notations "{ _ ..." that have a special treatment *)
    | Terminal "{" :: NonTerminal _ :: _ -> [] | _ -> symbols in
  aux false symbols
  (* considering "_" as a prefix would make all infix notations incompatible *)
  |> List.filter (function [NonTerminal _], _ -> false | _ -> true)
  |> List.map (fun (l, k) -> make_notation_key entry l, k)

let prefixes_map = Summary.ref ~stage:Summary.Stage.Synterp ~name:"notation_prefixes_map" NotationMap.empty

let declare_prefixes ntn =
  let register_prefix (pref, _) =
    if not (NotationMap.mem pref !prefixes_map) then
      prefixes_map := NotationMap.add pref ntn !prefixes_map in
  List.iter register_prefix (list_prefixes ntn)

let notation_non_terminals_map = Summary.ref ~stage:Summary.Stage.Synterp ~name:"notation_non_terminals_map" NotationMap.empty

let declare_notation_non_terminals ntn entries =
  try
    let _ = NotationMap.find ntn !notation_grammar_map in
    anomaly (str "Notation " ++ pr_notation ntn ++ str " is already assigned a grammar.")
  with Not_found ->
  notation_non_terminals_map := NotationMap.add ntn entries !notation_non_terminals_map;
  declare_prefixes ntn

let non_terminals_of_notation ntn =
  NotationMap.find ntn !notation_non_terminals_map

let longest_common_prefix ntn =
  CList.find_map
    (fun (pref, k) ->
      NotationMap.find_opt pref !prefixes_map
      |> Option.map (fun ntn -> ntn, k))
    (List.rev (list_prefixes ntn))

let get_defined_notations () =
  NotationSet.elements @@ NotationMap.domain !notation_grammar_map
