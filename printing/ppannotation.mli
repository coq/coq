(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines the annotations that are attached to
    semi-structured pretty-printing of Coq syntactic objects. *)

open Ppextend
open Constrexpr
open Vernacexpr
open Tacexpr

type t =
  | AKeyword
  | AUnparsing            of unparsing
  | AConstrExpr           of constr_expr
  | AVernac               of vernac_expr
  | AGlobTacticExpr       of glob_tactic_expr
  | AGlobAtomicTacticExpr of glob_atomic_tactic_expr
  | ARawTacticExpr        of raw_tactic_expr
  | ARawAtomicTacticExpr  of raw_atomic_tactic_expr
  | ATacticExpr           of tactic_expr
  | AAtomicTacticExpr     of atomic_tactic_expr

val tag_of_annotation : t -> string

val attributes_of_annotation : t -> (string * string) list

val tag : t Pp.Tag.key
