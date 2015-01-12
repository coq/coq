(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file defines the printer for natural numbers in [nat] *)

(*i*)
open Glob_term
open Bigint
open Coqlib
open Pp
open Errors
(*i*)

(**********************************************************************)
(* Parsing via scopes *)
(* For example, (nat_of_string "3") is <<(S (S (S O)))>> *)

let threshold = of_int 5000

let nat_of_int dloc n =
  if is_pos_or_zero n then begin
      if less_than threshold n then
	msg_warning
	  (strbrk "Stack overflow or segmentation fault happens when " ++
	   strbrk "working with large numbers in nat (observed threshold " ++
	   strbrk "may vary from 5000 to 70000 depending on your system " ++
	   strbrk "limits and on the command executed).");
      let ref_O = GRef (dloc, glob_O, None) in
      let ref_S = GRef (dloc, glob_S, None) in
      let rec mk_nat acc n =
	if n <> zero then
	  mk_nat (GApp (dloc,ref_S, [acc])) (sub_1 n)
	else
	  acc
      in
      mk_nat ref_O n
    end
  else
      user_err_loc (dloc, "nat_of_int",
        str "Cannot interpret a negative number as a number of type nat")

(************************************************************************)
(* Printing via scopes *)

exception Non_closed_number

let rec int_of_nat = function
  | GApp (_,GRef (_,s,_),[a]) when Globnames.eq_gr s glob_S -> add_1 (int_of_nat a)
  | GRef (_,z,_) when Globnames.eq_gr z glob_O -> zero
  | _ -> raise Non_closed_number

let uninterp_nat p =
  try
    Some (int_of_nat p)
  with
    Non_closed_number -> None

(************************************************************************)
(* Declare the primitive parsers and printers *)

let _ =
  Notation.declare_numeral_interpreter "nat_scope"
    (nat_path,datatypes_module_name)
    nat_of_int
    ([GRef (Loc.ghost,glob_S,None); GRef (Loc.ghost,glob_O,None)], uninterp_nat, true)
