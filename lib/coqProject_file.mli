(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type target =
  | ML of string (* ML file : foo.ml -> (ML "foo.ml") *)
  | MLI of string (* MLI file : foo.mli -> (MLI "foo.mli") *)
  | ML4 of string (* ML4 file : foo.ml4 -> (ML4 "foo.ml4") *)
  | MLLIB of string (* MLLIB file : foo.mllib -> (MLLIB "foo.mllib") *)
  | MLPACK of string (* MLLIB file : foo.mlpack -> (MLLIB "foo.mlpack") *)
  | V of string  (* V file : foo.v -> (V "foo") *)
  | Arg of string
  | Special of string * string * bool * string
    (* file, dependencies, is_phony, command *)
  | Subdir of string
  | Def of string * string (* X=foo -> Def ("X","foo") *)
  | MLInclude of string (* -I physicalpath *)
  | Include of string * string (* -Q physicalpath logicalpath *)
  | RInclude of string * string (* -R physicalpath logicalpath *)

type install =
  | NoInstall
  | TraditionalInstall
  | UserInstall
  | UnspecInstall

exception Parsing_error

val args_from_project : 
           string ->
           (string *
            ('a *
             (('b * string) list * ('c * string * string) list *
              ('d * string * string) list) *
             (string list * 'e)))
           list -> string -> string * string list

val read_project_file :
           string ->
           (string list *
            (string list * string list * string list * string list *
             string list) *
            (string * string * bool * string) list * string list) *
           ((string * string) list * (string * string * string) list *
            (string * string * string) list) *
           (string list * (string * string) list)

val process_cmd_line :
           string ->
           string option * string option * install * bool ->
           target list ->
           string list ->
           (string option * string option * install * bool) * target list

val split_arguments :
           target list ->
           (string list *
            (string list * string list * string list * string list *
             string list) *
            (string * string * bool * string) list * string list) *
           ((string * string) list * (string * string * string) list *
            (string * string * string) list) *
           (string list * (string * string) list)

