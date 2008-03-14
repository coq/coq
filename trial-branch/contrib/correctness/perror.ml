(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Himsg

open Ptype
open Past

let is_mutable = function Ref _ | Array _ -> true | _ -> false
let is_pure = function TypePure _ -> true | _ -> false

let raise_with_loc = function
  | None -> raise
  | Some loc -> Stdpp.raise_with_loc loc 

let unbound_variable id loc =
  raise_with_loc loc
    (UserError ("Perror.unbound_variable",
    (hov 0 (str"Unbound variable" ++ spc () ++ pr_id id ++ fnl ()))))

let unbound_reference id loc =
  raise_with_loc loc
    (UserError ("Perror.unbound_reference",
    (hov 0 (str"Unbound reference" ++ spc () ++ pr_id id ++ fnl ()))))

let clash id loc =
  raise_with_loc loc
    (UserError ("Perror.clash",
    (hov 0 (str"Clash with previous constant" ++ spc () ++
    str(string_of_id id) ++ fnl ()))))

let not_defined id =
  raise
    (UserError ("Perror.not_defined",
	       	(hov 0 (str"The object" ++ spc () ++ pr_id id ++ spc () ++
			  str"is not defined" ++ fnl ()))))

let check_for_reference loc id = function
    Ref _ -> ()
  | _ -> Stdpp.raise_with_loc loc 
	(UserError ("Perror.check_for_reference",
		    hov 0 (pr_id id ++ spc () ++ 
			     str"is not a reference")))

let check_for_array loc id = function
    Array _ -> ()
  | _ -> Stdpp.raise_with_loc loc 
	(UserError ("Perror.check_for_array",
		    hov 0 (pr_id id ++ spc () ++ 
			     str"is not an array")))

let is_constant_type s = function
    TypePure c ->
      let id = id_of_string s in
      let c' = Constrintern.global_reference id in
      Reductionops.is_conv (Global.env()) Evd.empty c c'
  | _ -> false 

let check_for_index_type loc v =
  let is_index = is_constant_type "Z" v in
  if not is_index then
    Stdpp.raise_with_loc loc 
      (UserError ("Perror.check_for_index",
		  hov 0 (str"This expression is an index" ++ spc () ++ 
			   str"and should have type int (Z)")))

let check_no_effect loc ef =
  if not (Peffect.get_writes ef = []) then
    Stdpp.raise_with_loc loc 
      (UserError ("Perror.check_no_effect",
		  hov 0 (str"A boolean should not have side effects"
)))

let should_be_boolean loc =
  Stdpp.raise_with_loc loc 
    (UserError ("Perror.should_be_boolean",
		hov 0 (str"This expression is a test:" ++ spc () ++
			 str"it should have type bool")))

let test_should_be_annotated loc =
  Stdpp.raise_with_loc loc 
    (UserError ("Perror.test_should_be_annotated",
		hov 0 (str"This test should be annotated")))

let if_branches loc =
  Stdpp.raise_with_loc loc 
    (UserError ("Perror.if_branches",
		hov 0 (str"The two branches of an `if' expression" ++ spc () ++
			 str"should have the same type")))

let check_for_not_mutable loc v =
  if is_mutable v then
    Stdpp.raise_with_loc loc 
      (UserError ("Perror.check_for_not_mutable",
		  hov 0 (str"This expression cannot be a mutable")))

let check_for_pure_type loc v =
  if not (is_pure v) then
    Stdpp.raise_with_loc loc 
      (UserError ("Perror.check_for_pure_type",
		  hov 0 (str"This expression must be pure" ++ spc () ++
			   str"(neither a mutable nor a function)")))

let check_for_let_ref loc v =
  if not (is_pure v) then
    Stdpp.raise_with_loc loc 
      (UserError ("Perror.check_for_let_ref",
		  hov 0 (str"References can only be bound in pure terms")))

let informative loc s =
  Stdpp.raise_with_loc loc 
  (UserError ("Perror.variant_informative",
	      hov 0 (str s ++ spc () ++ str"must be informative")))

let variant_informative loc = informative loc "Variant"
let should_be_informative loc = informative loc "This term"

let app_of_non_function loc =
  Stdpp.raise_with_loc loc 
  (UserError ("Perror.app_of_non_function",
	      hov 0 (str"This term cannot be applied" ++ spc () ++
		       str"(either it is not a function" ++ spc () ++
		       str"or it is applied to non pure arguments)")))
  
let partial_app loc =
  Stdpp.raise_with_loc loc 
  (UserError ("Perror.partial_app",
	      hov 0 (str"This function does not have" ++
		       spc () ++ str"the right number of arguments")))
  
let expected_type loc s =
  Stdpp.raise_with_loc loc 
  (UserError ("Perror.expected_type",
	      hov 0 (str"Argument is expected to have type" ++ spc () ++ s)))

let expects_a_type id loc =
  Stdpp.raise_with_loc loc 
  (UserError ("Perror.expects_a_type",
	      hov 0 (str"The argument " ++ pr_id id ++ spc () ++
		       str"in this application is supposed to be a type")))

let expects_a_term id =
  raise
  (UserError ("Perror.expects_a_type",
	      hov 0 (str"The argument " ++ pr_id id ++ spc () ++
		       str"in this application is supposed to be a term")))

let should_be_a_variable loc =
  Stdpp.raise_with_loc loc 
  (UserError ("Perror.should_be_a_variable",
	      hov 0 (str"Argument should be a variable")))
   
let should_be_a_reference loc =
  Stdpp.raise_with_loc loc 
  (UserError ("Perror.should_be_a_reference",
	      hov 0 (str"Argument of function should be a reference")))

   
