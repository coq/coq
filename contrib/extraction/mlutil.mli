
open Names
open Term
open Miniml

(*s Special identifiers. [prop_name] is to be used for propositions
    and will be printed as [_] in concrete (Caml) code. *)

val anonymous : identifier
val prop_name : identifier

(*s Utility functions over ML terms. *)

val occurs : int -> ml_ast -> bool

val ml_lift : int -> ml_ast -> ml_ast

(* [ml_subst e t] substitutes [e] for [Rel 1] in [t] *)
val ml_subst : ml_ast -> ml_ast -> ml_ast

val betared_ast : ml_ast -> ml_ast
val betared_decl : ml_decl -> ml_decl

val uncurrify_ast : ml_ast -> ml_ast
val uncurrify_decl : ml_decl -> ml_decl

(*s Table for the extraction to ML values. *)

module Refset : Set.S with type elt = global_reference

val find_ml_extraction : global_reference -> string

val ml_extractions : unit -> Refset.t
