
open Miniml

val occurs : int -> ml_ast -> bool

val ml_lift : int -> ml_ast -> ml_ast

val uncurrify_ast : ml_ast -> ml_ast
val uncurrify_decl : ml_decl -> ml_decl
