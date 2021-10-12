(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors
open Notation
open Constrexpr

(*s Pretty-print. *)

type ppbox =
  | PpHB
  | PpHOVB of int
  | PpHVB of int
  | PpVB of int

type ppcut =
  | PpBrk of int * int
  | PpFnl

let ppcmd_of_box = function
  | PpHB -> h
  | PpHOVB n -> hov n
  | PpHVB n -> hv n
  | PpVB n -> v n

let ppcmd_of_cut = function
  | PpFnl -> fnl ()
  | PpBrk(n1,n2) -> brk(n1,n2)

type pattern_quote_style = QuotedPattern | NotQuotedPattern

type unparsing =
  | UnpMetaVar of entry_relative_level * Extend.side option
  | UnpBinderMetaVar of entry_relative_level * pattern_quote_style
  | UnpListMetaVar of entry_relative_level * unparsing list * Extend.side option
  | UnpBinderListMetaVar of bool * unparsing list
  | UnpTerminal of string
  | UnpBox of ppbox * unparsing Loc.located list
  | UnpCut of ppcut

type unparsing_rule = unparsing list
type extra_unparsing_rules = (string * string) list

let rec unparsing_eq unp1 unp2 = match (unp1,unp2) with
  | UnpMetaVar (p1,s1), UnpMetaVar (p2,s2) -> entry_relative_level_eq p1 p2 && s1 = s2
  | UnpBinderMetaVar (p1,s1), UnpBinderMetaVar (p2,s2) -> entry_relative_level_eq p1 p2 && s1 = s2
  | UnpListMetaVar (p1,l1,s1), UnpListMetaVar (p2,l2,s2) -> entry_relative_level_eq p1 p2 && List.for_all2eq unparsing_eq l1 l2 && s1 = s2
  | UnpBinderListMetaVar (b1,l1), UnpBinderListMetaVar (b2,l2) -> b1 = b2 && List.for_all2eq unparsing_eq l1 l2
  | UnpTerminal s1, UnpTerminal s2 -> String.equal s1 s2
  | UnpBox (b1,l1), UnpBox (b2,l2) -> b1 = b2 && List.for_all2eq unparsing_eq (List.map snd l1) (List.map snd l2)
  | UnpCut p1, UnpCut p2 -> p1 = p2
  | (UnpMetaVar _ | UnpBinderMetaVar _ | UnpListMetaVar _ |
     UnpBinderListMetaVar _ | UnpTerminal _ | UnpBox _ | UnpCut _), _ -> false

(* Register generic and specific printing rules *)

type notation_printing_rules = {
  notation_printing_unparsing : unparsing_rule;
  notation_printing_level : entry_level;
  notation_printing_extra : extra_unparsing_rules;
}

type generic_notation_printing_rules = {
  notation_printing_reserved : bool;
  notation_printing_rules : notation_printing_rules;
}

let generic_notation_printing_rules =
  Summary.ref ~name:"generic-notation-printing-rules" (NotationMap.empty : generic_notation_printing_rules NotationMap.t)

let specific_notation_printing_rules =
  Summary.ref ~name:"specific-notation-printing-rules" (SpecificNotationMap.empty : notation_printing_rules SpecificNotationMap.t)

let declare_generic_notation_printing_rules ntn rules =
  generic_notation_printing_rules := NotationMap.add ntn rules !generic_notation_printing_rules
let declare_specific_notation_printing_rules specific_ntn rules =
  specific_notation_printing_rules := SpecificNotationMap.add specific_ntn rules !specific_notation_printing_rules

let has_generic_notation_printing_rule ntn =
  try (NotationMap.find ntn !generic_notation_printing_rules).notation_printing_reserved
  with Not_found -> false

let find_generic_notation_printing_rule ntn =
  NotationMap.find ntn !generic_notation_printing_rules

let find_specific_notation_printing_rule specific_ntn =
  SpecificNotationMap.find specific_ntn !specific_notation_printing_rules

let find_notation_printing_rule which ntn =
  try match which with
  | None -> raise Not_found (* Normally not the case *)
  | Some which -> (find_specific_notation_printing_rule (which,ntn))
  with Not_found -> (find_generic_notation_printing_rule ntn).notation_printing_rules

let find_notation_extra_printing_rules which ntn =
  try match which with
  | None -> raise Not_found
  | Some which -> (find_specific_notation_printing_rule (which,ntn)).notation_printing_extra
  with Not_found -> (find_generic_notation_printing_rule ntn).notation_printing_rules.notation_printing_extra

let add_notation_extra_printing_rule ntn k v =
  try
    generic_notation_printing_rules :=
      let { notation_printing_reserved; notation_printing_rules } = NotationMap.find ntn !generic_notation_printing_rules in
      let rules = {
          notation_printing_reserved;
          notation_printing_rules = {
              notation_printing_rules with
              notation_printing_extra = (k,v) :: notation_printing_rules.notation_printing_extra
            }
        } in
      NotationMap.add ntn rules !generic_notation_printing_rules
  with Not_found ->
    user_err
      (str "No such Notation.")
