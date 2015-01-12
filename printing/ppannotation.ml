(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

let tag_of_annotation = function
  | AKeyword                -> "keyword"
  | AUnparsing _            -> "unparsing"
  | AConstrExpr _           -> "constr_expr"
  | AVernac _               -> "vernac_expr"
  | AGlobTacticExpr _       -> "glob_tactic_expr"
  | AGlobAtomicTacticExpr _ -> "glob_atomic_tactic_expr"
  | ARawTacticExpr _        -> "raw_tactic_expr"
  | ARawAtomicTacticExpr _  -> "raw_atomic_tactic_expr"
  | ATacticExpr _           -> "tactic_expr"
  | AAtomicTacticExpr _     -> "atomic_tactic_expr"

let attributes_of_annotation a =
  []

let tag = Pp.Tag.create "ppannotation"
