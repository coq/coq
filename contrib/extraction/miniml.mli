(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Target language for extraction: a core ML called MiniML. *)

open Pp
open Util
open Names
open Libnames

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)
   
(* Convention: outmost lambda/product gives the head of the list, 
   and [true] means that the argument is to be kept. *)

type signature = bool list

(*s ML type expressions. *)

type ml_type = 
  | Tarr    of ml_type * ml_type
  | Tglob   of global_reference * ml_type list 
  | Tvar    of int
  | Tvar'   of int (* same as Tvar, used to avoid clash *)
  | Tmeta   of ml_meta (* used during ML type reconstruction *)
  | Tdummy
  | Tunknown
  | Tcustom of string

and ml_meta = { id : int; mutable contents : ml_type option }

(* ML type schema. 
   The integer is the number of variable in the schema. *)

type ml_schema = int * ml_type 

(*s ML inductive types. *)

type inductive_info = Record | Singleton | Coinductive | Standard

(* A [ml_ind_packet] is the miniml counterpart of a [one_inductive_body]. 
   If the inductive is logical ([ip_logical = false]), then all other fields
   are unused. Otherwise, 
   [ip_sign] is a signature concerning the arguments of the inductive, 
   [ip_vars] contains the names of the type variables surviving in ML, 
   [ip_types] contains the ML types of all constructors.    
*)

type ml_ind_packet = { 
  ip_logical : bool;
  ip_sign : signature; 
  ip_vars : identifier list; 
  ip_types : (ml_type list) array }  

(* [ip_nparams] contains the number of parameters. *)

type ml_ind = {
  ind_info : inductive_info;
  ind_nparams : int; 	       
  ind_packets : ml_ind_packet array }

(*s ML terms. *)

type ml_ast = 
  | MLrel    of int
  | MLapp    of ml_ast * ml_ast list
  | MLlam    of identifier * ml_ast
  | MLletin  of identifier * ml_ast * ml_ast
  | MLglob   of global_reference
  | MLcons   of global_reference * ml_ast list
  | MLcase   of ml_ast * (global_reference * identifier list * ml_ast) array
  | MLfix    of int * identifier array * ml_ast array
  | MLexn    of string
  | MLdummy
  | MLcast   of ml_ast * ml_type
  | MLmagic  of ml_ast
  | MLcustom of string

(*s ML declarations. *)

type ml_decl = 
  | Dind  of kernel_name * ml_ind
  | Dtype of global_reference * identifier list * ml_type
  | Dterm   of global_reference * ml_ast * ml_type
  | DcustomTerm of global_reference * string
  | DcustomType of global_reference * string
  | Dfix    of global_reference array * ml_ast array * ml_type array

type ml_specif = 
  | Sval of ml_type
  | Stype of ml_type option 
  | Smind of ml_ind
  | Smodule of ml_module_type  (* et un module_path option ?? *) 
  | Smodtype of ml_module_type

and ml_module_sig = (label * ml_specif) list

and ml_module_type = 
  | MTident of kernel_name
  | MTfunsig of mod_bound_id * ml_module_type * ml_module_type
  | MTsig of mod_self_id * ml_module_sig

and ml_module_expr =
  | MEident of module_path
  | MEfunctor of mod_bound_id * ml_module_type * ml_module_expr 
  | MEstruct of mod_self_id * ml_module_structure
  | MEapply of ml_module_expr * ml_module_expr

and ml_structure_elem = 
  | SEind of ml_ind
  | SEtype of identifier list * ml_type
  | SEterm of ml_ast * ml_type
  | SEfix of global_reference array * ml_ast array * ml_type array
  | SEmodule of ml_module (* pourquoi pas plutot ml_module_expr *)
  | SEmodtype of ml_module_type

and ml_module_structure = (label * ml_structure_elem) list

and ml_module = 
    { ml_mod_expr : ml_module_expr option; 
      ml_mod_type : ml_module_type }


(*s Pretty-printing of MiniML in a given concrete syntax is parameterized
    by a function [pp_global] that pretty-prints global references. 
    The resulting pretty-printer is a module of type [Mlpp] providing
    functions to print types, terms and declarations. *)

type extraction_params =  
  { modular : bool; 
    mod_name : identifier; 
    to_appear : global_reference list }

module type Mlpp_param = sig
  val globals : unit -> Idset.t
  val pp_global : global_reference -> std_ppcmds
end

module type Mlpp = sig
  val pp_decl : ml_decl -> std_ppcmds
end

