
(* $Id$ *)

open Util
open Names
open Generic
open Term

type abstraction_body = { 
  abs_kind : path_kind;
  abs_arity : int array;
  abs_rhs : constr }

let rec count_dlam = function
  | DLAM (_,c) -> 1 + (count_dlam c)
  | _ -> 0

let sAPP c n =
  match c with 
    | DLAM(na,m) -> subst1 n m
    | _ -> invalid_arg "SAPP"
	  
let contract_abstraction ab args =
  if array_for_all2 (fun c i -> (count_dlam c) = i) args ab.abs_arity then
    Sosub.soexecute (Array.fold_left sAPP ab.abs_rhs args)
  else 
    failwith "contract_abstraction"
