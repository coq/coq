(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ppextend
open Constrexpr
open Vernacexpr
open Genarg

type t =
  | AKeyword
  | AUnparsing            of unparsing
  | AConstrExpr           of constr_expr
  | AVernac               of vernac_expr
  | AGlbGenArg            of glob_generic_argument
  | ARawGenArg            of raw_generic_argument

let tag_of_annotation = function
  | AKeyword                -> "keyword"
  | AUnparsing _            -> "unparsing"
  | AConstrExpr _           -> "constr_expr"
  | AVernac _               -> "vernac_expr"
  | AGlbGenArg _            -> "glob_generic_argument"
  | ARawGenArg _            -> "raw_generic_argument"

let attributes_of_annotation a =
  []

let tag = Pp.Tag.create "ppannotation"
