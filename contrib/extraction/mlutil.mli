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

(*s Utility functions over ML types. [update_args sp vl t] puts [vl]
   as arguments behind every inductive types [(sp,_)]. *)

val kn_of_r : global_reference -> kernel_name

val type_mem_kn : kernel_name -> ml_type -> bool

(*s Utility functions over ML terms. [occurs n t] checks whether [Rel
    n] occurs (freely) in [t]. [ml_lift] is de Bruijn
    lifting. *)

val ast_iter : (ml_ast -> unit) -> ml_ast -> unit 

val occurs : int -> ml_ast -> bool

val ml_lift : int -> ml_ast -> ml_ast

val ml_subst : ml_ast -> ml_ast -> ml_ast

val ml_pop : ml_ast -> ml_ast

(*s Some transformations of ML terms. [optimize] simplify
    all beta redexes (when the argument does not occur, it is just
    thrown away; when it occurs exactly once it is substituted; otherwise
    a let-in redex is created for clarity) and iota redexes, plus some other
    optimizations. *)

val optimize : 
  extraction_params -> ml_decl list -> ml_decl list

(* Misc. *)

val decl_search : ml_ast -> ml_decl list -> bool

val add_ml_decls : 
  extraction_params -> ml_decl list -> ml_decl list

val kill_some_lams : 
  bool list -> identifier list * ml_ast -> identifier list * ml_ast





