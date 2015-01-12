(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp

(*s Pretty-print. *)

(* Dealing with precedences *)

type precedence = int

type parenRelation = L | E | Any | Prec of precedence

type tolerability = precedence * parenRelation

type ppbox =
  | PpHB of int
  | PpHOVB of int
  | PpHVB of int
  | PpVB of int
  | PpTB

type ppcut =
  | PpBrk of int * int
  | PpTbrk of int * int
  | PpTab
  | PpFnl

let ppcmd_of_box = function
  | PpHB n -> h n
  | PpHOVB n -> hov n
  | PpHVB n -> hv n
  | PpVB n -> v n
  | PpTB   -> t

let ppcmd_of_cut = function
  | PpTab -> tab ()
  | PpFnl -> fnl ()
  | PpBrk(n1,n2) -> brk(n1,n2)
  | PpTbrk(n1,n2) -> tbrk(n1,n2)

type unparsing =
  | UnpMetaVar of int * parenRelation
  | UnpListMetaVar of int * parenRelation * unparsing list
  | UnpBinderListMetaVar of int * bool * unparsing list
  | UnpTerminal of string
  | UnpBox of ppbox * unparsing list
  | UnpCut of ppcut
