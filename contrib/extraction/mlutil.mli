(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Names
open Term
open Libnames
open Miniml
open Util

(*s Special identifiers. [dummy_name] is to be used for dead code
    and will be printed as [_] in concrete (Caml) code. *)

val anonymous : identifier
val dummy_name : identifier
val id_of_name : name -> identifier

(*s [collect_lambda MLlam(id1,...MLlam(idn,t)...)] returns
    the list [idn;...;id1] and the term [t]. *)

val collect_lams : ml_ast -> identifier list * ml_ast
val collect_n_lams : int -> ml_ast -> identifier list * ml_ast
val nb_lams : ml_ast -> int

(*s [anonym_lams a n] creates [n] anonymous [MLlam] in front of [a] *)

val anonym_lams : ml_ast -> int -> ml_ast
val dummy_lams : ml_ast -> int -> ml_ast
val named_lams : identifier list -> ml_ast -> ml_ast
val anonym_or_dummy_lams : ml_ast -> bool list -> ml_ast

val eta_args_sign : int -> bool list -> ml_ast list 

(*s Utility functions over ML types with meta. *)

val reset_meta_count : unit -> unit
val new_meta : 'a -> ml_type

val instantiation : ml_schema -> ml_type

val needs_magic : ml_type * ml_type -> bool
val put_magic_if : bool -> ml_ast -> ml_ast
val put_magic : ml_type * ml_type -> ml_ast -> ml_ast

(*s ML type environment. *)

module Mlenv : sig 
  type t 
  val empty : t
    
  (* get the n-th more recently entered schema and instantiate it. *) 
  val get : t -> int -> ml_type

  (* Adding a type in an environment, after generalizing free meta *)
  val push_gen : t -> ml_type -> t

  (* Adding a type with no [Tvar] *)
  val push_type : t -> ml_type -> t
     
  (* Adding a type with no [Tvar] nor [Tmeta] *)
  val push_std_type : t -> ml_type -> t
end

(*s Utility functions over ML types without meta *)

val kn_of_r : global_reference -> kernel_name

val type_mem_kn : kernel_name -> ml_type -> bool

val type_maxvar : ml_type -> int

val type_decomp : ml_type -> ml_type list * ml_type
val type_recomp : ml_type list * ml_type -> ml_type

val var2var' : ml_type -> ml_type 

val type_subst : int -> ml_type -> ml_type -> ml_type
val type_subst_all : ml_type list -> ml_type -> ml_type 

type abbrev_map = global_reference -> ml_type option

val type_expand : abbrev_map -> ml_type -> ml_type 
val type_eq : abbrev_map -> ml_type -> ml_type -> bool
val type_neq : abbrev_map -> ml_type -> ml_type -> bool
val type_to_sign : abbrev_map -> ml_type -> bool list
val type_expunge : abbrev_map -> ml_type -> ml_type


(*s Utility functions over ML terms. [ast_occurs n t] checks whether [Rel
    n] occurs (freely) in [t]. [ml_lift] is de Bruijn
    lifting. *)

val ast_iter : (ml_ast -> unit) -> ml_ast -> unit 
val ast_occurs : int -> ml_ast -> bool
val ast_lift : int -> ml_ast -> ml_ast
val ast_subst : ml_ast -> ml_ast -> ml_ast
val ast_pop : ml_ast -> ml_ast

(*s Some transformations of ML terms. [optimize] simplify
    all beta redexes (when the argument does not occur, it is just
    thrown away; when it occurs exactly once it is substituted; otherwise
    a let-in redex is created for clarity) and iota redexes, plus some other
    optimizations. *)

val optimize : 
  extraction_params -> ml_decl list -> ml_decl list

(* Misc. *)

val decl_search : ml_ast -> ml_decl list -> bool
val decl_type_search : ml_type -> ml_decl list -> bool

val add_ml_decls : 
  extraction_params -> ml_decl list -> ml_decl list

val kill_some_lams : 
  bool list -> identifier list * ml_ast -> identifier list * ml_ast





