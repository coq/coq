
(*i $Id$ i*)

open Pp
open Names
open Term

(*s Target language for extraction: a core ML called MiniML. *)

(*s Identifiers of type are either parameters or type names. *)

type ml_typeid = identifier

(*s ML type expressions. *)

type ml_type = 
  | Tvar  of ml_typeid
  | Tapp  of ml_type list
  | Tarr  of ml_type * ml_type
  | Tglob of global_reference
  | Tprop
      
(*s ML inductive types. *)

type ml_ind = identifier list * identifier * (identifier * ml_type list) list

(*s ML terms. *)

type ml_ast = 
  | MLrel   of int
  | MLapp   of ml_ast * ml_ast list
  | MLlam   of identifier * ml_ast
  | MLglob  of global_reference
  | MLcons  of int * identifier * ml_ast list
  | MLcase  of ml_ast * (identifier * identifier list * ml_ast) array
  | MLfix   of int * bool * (identifier list) * (ml_ast list)
  | MLexn   of identifier
  | MLcast  of ml_ast * ml_type
  | MLmagic of ml_ast

(*s ML declarations. *)

type ml_decl = 
  | Dtype   of ml_ind list
  | Dabbrev of identifier * (identifier list) * ml_type
  | Dglob   of identifier * ml_ast

(*s Pretty-printing of MiniML in a given concrete syntax is parameterized
    by a function [pp_global] that pretty-prints global references. 
    The resulting pretty-printer is a module of type [Mlpp] providing
    functions to print types, terms and declarations. *)

module type Mlpp_param = sig
  val pp_global : global_reference -> std_ppcmds
end

module type Mlpp = sig
  val pp_type : ml_type -> std_ppcmds
  val pp_ast : ml_ast -> std_ppcmds
  val pp_decl : ml_decl -> std_ppcmds
end

