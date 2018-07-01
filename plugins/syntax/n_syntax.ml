(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Names
open Bigint
open Positive_syntax_plugin.Positive_syntax

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "n_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(**********************************************************************)
(* Parsing N via scopes                                               *)
(**********************************************************************)

open Globnames
open Glob_term

let binnums = ["Coq";"Numbers";"BinNums"]

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

(* TODO: temporary hack *)
let make_kn dir id = Globnames.encode_mind dir id

let n_kn = make_kn (make_dir binnums) (Id.of_string "N")
let glob_n = IndRef (n_kn,0)
let path_of_N0 = ((n_kn,0),1)
let path_of_Npos = ((n_kn,0),2)
let glob_N0 = ConstructRef path_of_N0
let glob_Npos = ConstructRef path_of_Npos

let n_path = make_path binnums "N"

let n_of_binnat ?loc pos_or_neg n = DAst.make ?loc @@
  if not (Bigint.equal n zero) then
    GApp(DAst.make @@ GRef (glob_Npos,None), [pos_of_bignat ?loc n])
  else
    GRef(glob_N0, None)

let error_negative ?loc =
  user_err ?loc ~hdr:"interp_N" (str "No negative numbers in type \"N\".")

let n_of_int ?loc n =
  if is_pos_or_zero n then n_of_binnat ?loc true n
  else error_negative ?loc

(**********************************************************************)
(* Printing N via scopes                                              *)
(**********************************************************************)

let bignat_of_n n = DAst.with_val (function
  | GApp (r, [a]) when is_gr r glob_Npos -> bignat_of_pos a
  | GRef (a,_) when GlobRef.equal a glob_N0 -> Bigint.zero
  | _ -> raise Non_closed_number
  ) n

let uninterp_n (AnyGlobConstr p) =
  try Some (bignat_of_n p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for N *)

let _ = Notation.declare_numeral_interpreter "N_scope"
  (n_path,binnums)
  n_of_int
  ([DAst.make @@ GRef (glob_N0, None);
    DAst.make @@ GRef (glob_Npos, None)],
  uninterp_n,
  true)
