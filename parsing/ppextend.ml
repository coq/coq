(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors
open Notation
open Notation_gram

(*s Pretty-print. *)

type ppbox =
  | PpHB of int
  | PpHOVB of int
  | PpHVB of int
  | PpVB of int

type ppcut =
  | PpBrk of int * int
  | PpFnl

let ppcmd_of_box = function
  | PpHB n -> h n
  | PpHOVB n -> hov n
  | PpHVB n -> hv n
  | PpVB n -> v n

let ppcmd_of_cut = function
  | PpFnl -> fnl ()
  | PpBrk(n1,n2) -> brk(n1,n2)

type unparsing =
  | UnpMetaVar of int * parenRelation
  | UnpBinderMetaVar of int * parenRelation
  | UnpListMetaVar of int * parenRelation * unparsing list
  | UnpBinderListMetaVar of int * bool * unparsing list
  | UnpTerminal of string
  | UnpBox of ppbox * unparsing Loc.located list
  | UnpCut of ppcut

type unparsing_rule = unparsing list * precedence
type extra_unparsing_rules = (string * string) list
(* Concrete syntax for symbolic-extension table *)
let notation_rules =
  Summary.ref ~name:"notation-rules" (NotationMap.empty : (unparsing_rule * extra_unparsing_rules * notation_grammar) NotationMap.t)

let declare_notation_rule ntn ~extra unpl gram =
  notation_rules := NotationMap.add ntn (unpl,extra,gram) !notation_rules

let find_notation_printing_rule ntn =
  try pi1 (NotationMap.find ntn !notation_rules)
  with Not_found -> anomaly (str "No printing rule found for " ++ pr_notation ntn ++ str ".")
let find_notation_extra_printing_rules ntn =
  try pi2 (NotationMap.find ntn !notation_rules)
  with Not_found -> []
let find_notation_parsing_rules ntn =
  try pi3 (NotationMap.find ntn !notation_rules)
  with Not_found -> anomaly (str "No parsing rule found for " ++ pr_notation ntn ++ str ".")

let get_defined_notations () =
  NotationSet.elements @@ NotationMap.domain !notation_rules

let add_notation_extra_printing_rule ntn k v =
  try
    notation_rules :=
      let p, pp, gr = NotationMap.find ntn !notation_rules in
      NotationMap.add ntn (p, (k,v) :: pp, gr) !notation_rules
  with Not_found ->
    user_err ~hdr:"add_notation_extra_printing_rule"
      (str "No such Notation.")
