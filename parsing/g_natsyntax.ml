(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* This file to allow writing (3) for (S (S (S O))) 
   and still write (S y) for (S y) *)

open Pcoq
open Pp
open Util
open Names
open Coqast
open Ast
open Coqlib
open Termast
open Extend

exception Non_closed_number

let ast_O = ast_of_ref glob_O
let ast_S = ast_of_ref glob_S
  
(* For example, (nat_of_string "3") is <<(S (S (S O)))>> *)
let nat_of_int n dloc =
  let ast_O = set_loc dloc ast_O in
  let ast_S = set_loc dloc ast_S in
  let rec mk_nat n =
    if n <= 0 then 
      ast_O
    else 
      Node(dloc,"APPLIST", [ast_S; mk_nat (n-1)])
  in 
  mk_nat n

let pat_nat_of_int n dloc =
  let ast_O = set_loc dloc ast_O in
  let ast_S = set_loc dloc ast_S in
  let rec mk_nat n =
    if n <= 0 then 
      ast_O
    else 
      Node(dloc,"PATTCONSTRUCT", [ast_S; mk_nat (n-1)])
  in 
  mk_nat n

let nat_of_string s dloc = 
  nat_of_int (int_of_string s) dloc

let pat_nat_of_string s dloc = 
  pat_nat_of_int (int_of_string s) dloc
    
let rec int_of_nat_rec astS astO p =
  match p with
    | Node (_,"APPLIST", [b; a]) when alpha_eq(b,astS) ->
	(int_of_nat_rec astS astO a)+1
    | a when alpha_eq(a,astO) -> 1  
          (***** YES, 1, non 0 ... to print the successor of p *)
    | _ -> raise Non_closed_number
	  
let int_of_nat p =
  try 
    Some (int_of_nat_rec ast_S ast_O p)
  with
    Non_closed_number -> None

let pr_S a = hov 0 (str "S" ++ brk (1,1) ++ a)

let rec pr_external_S std_pr = function
  | Node (l,"APPLIST", [b; a]) when b = ast_S ->
      str"(" ++ pr_S (pr_external_S std_pr a) ++ str")"
  | p -> std_pr p

(* Declare the primitive printer *)

(* Prints not p, but the SUCCESSOR of p !!!!! *)
let nat_printer std_pr p =
  match (int_of_nat p) with
    | Some i -> str (string_of_int i)
    | None -> pr_S (pr_external_S std_pr p)

let _ = Esyntax.Ppprim.add ("nat_printer", nat_printer)

(* Declare the primitive parser *)

let unat = create_univ_if_new "nat"

let number = create_constr_entry unat "number" 
let pat_number = create_constr_entry unat "pat_number"
 
let _ = 
  Gram.extend number None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action nat_of_string]]

let _ = 
  Gram.extend pat_number None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action pat_nat_of_string]]
