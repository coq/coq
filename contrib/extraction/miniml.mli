
(*i $Id$ i*)

open Names

(* identifiers of type are either parameters or type names. *)

type ml_typeid = 
  | Tparam of identifier
  | Tname  of identifier

(* ML type expressions. *)

type ml_type = 
  | Tvar  of ml_typeid
  | Tapp  of ml_type list
  | Tarr  of ml_type * ml_type
  | Tglob of identifier
      
(* ML inductive types. *)

type ml_ind = identifier list * identifier * (identifier * ml_type list) list

(* ML terms. *)

type ml_ast = 
  | MLrel   of int
  | MLapp   of ml_ast * ml_ast list
  | MLlam   of identifier * ml_ast
  | MLglob  of identifier
  | MLcons  of int * identifier * ml_ast list
  | MLcase  of ml_ast * (identifier * identifier list * ml_ast) array
  | MLfix   of int * bool * (identifier list) * (ml_ast list)
  | MLexn   of identifier
  | MLcast  of ml_ast * ml_type
  | MLmagic of ml_ast

(* ML declarations. *)

type ml_decl = 
  | Dtype   of ml_ind list
  | Dabbrev of identifier * (identifier list) * ml_type
  | Dglob   of identifier * ml_ast

