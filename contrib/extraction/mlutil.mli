
open Miniml

val anonymous : Names.identifier
val prop_name : Names.identifier

val occurs : int -> ml_ast -> bool

val ml_lift : int -> ml_ast -> ml_ast

(* [ml_subst e t] substitutes [e] for [Rel 1] in [t] *)
val ml_subst : ml_ast -> ml_ast -> ml_ast

val betared_ast : ml_ast -> ml_ast
val betared_decl : ml_decl -> ml_decl

val uncurrify_ast : ml_ast -> ml_ast
val uncurrify_decl : ml_decl -> ml_decl
