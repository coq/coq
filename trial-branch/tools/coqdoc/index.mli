(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Cdglobals

type loc = int

type entry_type = 
  | Library
  | Module
  | Definition
  | Inductive
  | Constructor
  | Lemma
  | Variable
  | Axiom
  | TacticDefinition

type index_entry = 
  | Def of string * entry_type
  | Ref of coq_module * string
  | Mod of coq_module * string

val find : coq_module -> loc -> index_entry

val add_module : coq_module -> unit

type module_kind = Local | Coqlib | Unknown

val find_module : coq_module -> module_kind

(*s Scan identifiers introductions from a file *)

val scan_file : string -> coq_module -> unit

(*s Read globalizations from a file (produced by coqc -dump-glob) *)

val read_glob : string -> unit

(*s Indexes *)

type 'a index = { 
  idx_name : string;
  idx_entries : (char * (string * 'a) list) list;
  idx_size : int }

val all_entries : unit -> 
      (coq_module * entry_type) index *
      (entry_type * coq_module index) list

val map : (string -> 'a -> 'b) -> 'a index -> 'b index

