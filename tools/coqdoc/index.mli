(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Cdglobals

type loc = int

type entry_type =
  | Library
  | Module
  | Definition
  | Inductive
  | Constructor
  | Lemma
  | Record
  | Projection
  | Instance
  | Class
  | Method
  | Variable
  | Axiom
  | TacticDefinition
  | Abbreviation
  | Notation
  | Section

val type_name : entry_type -> string

type index_entry =
  | Def of string * entry_type
  | Ref of coq_module * string * entry_type

(* Find what symbol coqtop said is located at loc in the source file *)
val find : coq_module -> loc -> index_entry

(* Find what data is referred to by some string in some coq module *)
val find_string : string -> index_entry

val add_module : coq_module -> unit

type module_kind = Local | External of coq_module | Unknown

val find_module : coq_module -> module_kind

val init_coqlib_library : unit -> unit

val add_external_library : string -> coq_module -> unit

(*s Read globalizations from a file (produced by coqc -dump-glob) *)

val read_glob : Digest.t option -> string -> unit

(*s Indexes *)

type 'a index = {
  idx_name : string;
  idx_entries : (char * (string * 'a) list) list;
  idx_size : int }

val current_library : string ref

val display_letter : char -> string

val prepare_entry : string -> entry_type -> string

val all_entries : unit ->
      (coq_module * entry_type) index *
      (entry_type * coq_module index) list

val map : (string -> 'a -> 'b) -> 'a index -> 'b index

