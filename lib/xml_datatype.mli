(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** ['a gxml] is the type for semi-structured documents. They generalize
    XML by allowing any kind of tags and attributes. *)
type ('a, 'b) gxml =
  | Element of ('a * 'b * ('a, 'b) gxml list)
  | PCData of string

(** [xml] is a semi-structured documents where tags are strings and attributes
    are association lists from string to string. *)
type xml = (string, (string * string) list) gxml
