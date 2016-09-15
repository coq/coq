(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines the annotations that are attached to
    semi-structured pretty-printing of Coq syntactic objects. *)

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

val tag_of_annotation : t -> string

val attributes_of_annotation : t -> (string * string) list

val tag : t Pp.Tag.key
