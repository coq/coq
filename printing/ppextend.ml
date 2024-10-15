(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open Notationextern
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
  | UnpMetaVar of notation_entry_relative_level
  | UnpBinderMetaVar of notation_entry_relative_level * pattern_quote_style
  | UnpListMetaVar of notation_entry_relative_level * unparsing list
  | UnpBinderListMetaVar of
      bool (* true if open binder *) *
      bool (* true if printed with a quote *) *
      unparsing list
  | UnpTerminal of string
  | UnpBox of ppbox * unparsing Loc.located list
  | UnpCut of ppcut

type unparsing_rule = unparsing list

let rec unparsing_eq unp1 unp2 = match (unp1,unp2) with
  | UnpMetaVar subentry1, UnpMetaVar subentry2 -> notation_entry_relative_level_eq subentry1 subentry2
  | UnpBinderMetaVar (subentry1,s1), UnpBinderMetaVar (subentry2,s2) -> notation_entry_relative_level_eq subentry1 subentry2 && s1 = s2
  | UnpListMetaVar (subentry1,l1), UnpListMetaVar (subentry2,l2) -> notation_entry_relative_level_eq subentry1 subentry2 && List.for_all2eq unparsing_eq l1 l2
  | UnpBinderListMetaVar (b1,q1,l1), UnpBinderListMetaVar (b2,q2,l2) -> b1 = b2 && q1 = q2 && List.for_all2eq unparsing_eq l1 l2
  | UnpTerminal s1, UnpTerminal s2 -> String.equal s1 s2
  | UnpBox (b1,l1), UnpBox (b2,l2) -> b1 = b2 && List.for_all2eq unparsing_eq (List.map snd l1) (List.map snd l2)
  | UnpCut p1, UnpCut p2 -> p1 = p2
  | (UnpMetaVar _ | UnpBinderMetaVar _ | UnpListMetaVar _ |
     UnpBinderListMetaVar _ | UnpTerminal _ | UnpBox _ | UnpCut _), _ -> false

(* Register generic and specific printing rules *)

type notation_printing_rules = {
  notation_printing_unparsing : unparsing_rule;
  notation_printing_level : entry_level;
}

type generic_notation_printing_rules = {
  notation_printing_reserved : bool;
  notation_printing_rules : notation_printing_rules;
}

let generic_notation_printing_rules =
  Summary.ref ~stage:Synterp ~name:"generic-notation-printing-rules" (NotationMap.empty : generic_notation_printing_rules NotationMap.t)

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
