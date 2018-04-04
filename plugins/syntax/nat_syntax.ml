(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "nat_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(* This file defines the printer for natural numbers in [nat] *)

(*i*)
open Pp
open CErrors
open Names
open Glob_term
open Bigint
open Coqlib
(*i*)

(**********************************************************************)
(* Parsing via scopes *)
(* For example, (nat_of_string "3") is <<(S (S (S O)))>> *)

let threshold = of_int 5000

let warn_large_nat =
  CWarnings.create ~name:"large-nat" ~category:"numbers"
    (fun () -> strbrk "Stack overflow or segmentation fault happens when " ++
                 strbrk "working with large numbers in nat (observed threshold " ++
                 strbrk "may vary from 5000 to 70000 depending on your system " ++
                 strbrk "limits and on the command executed).")

let nat_of_int ?loc n =
  if is_pos_or_zero n then begin
      if less_than threshold n then warn_large_nat ();
      let ref_O = DAst.make ?loc @@ GRef (glob_O, None) in
      let ref_S = DAst.make ?loc @@ GRef (glob_S, None) in
      let rec mk_nat acc n =
	if n <> zero then
	  mk_nat (DAst.make ?loc @@ GApp (ref_S, [acc])) (sub_1 n)
	else
	  acc
      in
      mk_nat ref_O n
    end
  else
      user_err ?loc ~hdr:"nat_of_int"
       (str "Cannot interpret a negative number as a number of type nat")

(************************************************************************)
(* Printing via scopes *)

exception Non_closed_number

let rec int_of_nat x = DAst.with_val (function
  | GApp (r, [a]) ->
    begin match DAst.get r with
    | GRef (s,_) when GlobRef.equal s glob_S -> add_1 (int_of_nat a)
    | _ -> raise Non_closed_number
    end
  | GRef (z,_) when GlobRef.equal z glob_O -> zero
  | _ -> raise Non_closed_number
  ) x

let uninterp_nat (AnyGlobConstr p) =
  try
    Some (int_of_nat p)
  with
    Non_closed_number -> None

(************************************************************************)
(* Declare the primitive parsers and printers *)

open Notation

let nat_scope = "nat_scope"

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

let _ =
  register_bignumeral_interpretation nat_scope (nat_of_int,uninterp_nat);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_scope = nat_scope;
      pt_uid = nat_scope;
      pt_required = (nat_path,datatypes_module_name);
      pt_refs = [glob_S; glob_O];
      pt_in_match = true }
