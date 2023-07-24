(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

let notation_non_terminals_map = Summary.ref ~stage:Summary.Stage.Synterp ~name:"notation_non_terminals_map" NotationMap.empty

let declare_notation_non_terminals ntn entries =
  try
    let _ = NotationMap.find ntn !notation_grammar_map in
    anomaly (str "Notation " ++ pr_notation ntn ++ str " is already assigned a grammar.")
  with Not_found ->
  notation_non_terminals_map := NotationMap.add ntn entries !notation_non_terminals_map

let non_terminals_of_notation ntn =
  NotationMap.find ntn !notation_non_terminals_map

let get_defined_notations () =
  NotationSet.elements @@ NotationMap.domain !notation_grammar_map
