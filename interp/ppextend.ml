(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Notation_term

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
