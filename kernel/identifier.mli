(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id: i*)

(*i*)
open Pp
(*i*)

(*s \textbf{Identifiers} are isomorphic to strings (composed of correct
   characters), and there is a renaming facility (by adding numbers at
   the end).
   
   They are used as variable names (in proofs and sections) and in 
   visible bound variables. *)

type identifier

(* Constructor of an identifier;
   [make_ident] builds an identifier from a string and an optional index; 
   if the index is present and the string ends by a digit, 
   a ["_"] is inserted *)
val make_ident : string -> int option -> identifier

(* Some destructors of an identifier *)
val atompart_of_id : identifier -> string
val first_char : identifier -> string
val index_of_id : identifier -> int option

(* Parsing and printing of identifiers *)
val string_of_id : identifier -> string
val id_of_string : string -> identifier
val pr_id : identifier -> std_ppcmds

(* These checks the validity of an identifier; [check_ident] fails
   with error if invalid. These functions may be used to check validity of    labels and uniq_idents as well*)
val check_ident : string -> unit
val is_ident : string -> bool

(* Identifiers sets and maps *)
module Idset : Set.S with type elt = identifier
module Idmap : Map.S with type key = identifier

val lift_ident : identifier -> identifier
val next_ident_away_from : identifier -> identifier list -> identifier
val next_ident_away : identifier -> identifier list -> identifier

val add_prefix : string -> identifier -> identifier
val add_suffix : identifier -> string -> identifier

(* The "_" identifier *)
val wildcard : identifier

(*s \textbf{Names} are used for bound variables. *)

type name = Name of identifier | Anonymous

val next_name_away : name -> identifier list -> identifier
val next_name_away_with_default : 
  string -> name -> identifier list -> identifier

val out_name : name -> identifier

(*s \textbf{Labels} are used after dot in paths. Unlike identifiers
    there are no renamings on labels *)

type label

val string_of_label : label -> string
val label_of_string : string -> label
val pr_label : label -> std_ppcmds

val ident_of_label : label -> identifier
val label_of_ident : identifier -> label

module Labset : Set.S with type elt=label
module Labmap : Map.S with type key=label

(*s \textbf{Unique identifiers} are used as bound module names and as
    internal structure and signature names in paths *) 

type uniq_ident

(* [unique s] generates a unique identifier whose name part is [s] *)
val unique : string -> uniq_ident

(* [rename uid] creates a new identifier with the same name part 
   as [uid] *)
val rename : uniq_ident -> uniq_ident

(* these two functions give only the name part *)
val string_of_uid : uniq_ident -> string
val pr_uid : uniq_ident -> std_ppcmds

(* this function gives everything *)
val debug_print_uid : uniq_ident -> string
