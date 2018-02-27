(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** ['a gxml] is the type for semi-structured documents. They generalize
    XML by allowing any kind of attributes. *)
type 'a gxml =
  | Element of (string * 'a * 'a gxml list)
  | PCData of string

(** [xml] is a semi-structured documents where attributes are association
    lists from string to string. *)
type xml = (string * string) list gxml


