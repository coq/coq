
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Rawterm
(*i*)

(* Translation of pattern, rawterm and term into syntax trees for printing *)

val ast_of_pattern : pattern -> Coqast.t
val ast_of_rawconstr : rawconstr -> Coqast.t
val bdize : bool -> unit assumptions -> constr -> Coqast.t

(*i C'est bdize qui sait maintenant s'il faut afficher les casts ou pas
val bdize_no_casts : bool -> unit assumptions -> constr -> Coqast.t
i*)

val ast_of_constant     : constant -> Coqast.t
val ast_of_existential  : existential -> Coqast.t
val ast_of_constructor  : constructor -> Coqast.t
val ast_of_inductive    : inductive -> Coqast.t

(* For debugging *)
val print_implicits : bool ref
val print_casts : bool ref
val print_arguments : bool ref
val print_coercions : bool ref

val with_casts : ('a -> 'b) -> 'a -> 'b
val with_implicits : ('a -> 'b) -> 'a -> 'b
val with_arguments : ('a -> 'b) -> 'a -> 'b
val with_coercions : ('a -> 'b) -> 'a -> 'b
