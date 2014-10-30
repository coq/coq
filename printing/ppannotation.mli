(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines the annotations that are attached to
    semi-structured pretty-printing of Coq syntactic objects. *)

open Ppextend
open Constrexpr
open Vernacexpr

type t =
  | AUnparsing  of unparsing
  | AConstrExpr of constr_expr
  | AVernac     of vernac_expr
