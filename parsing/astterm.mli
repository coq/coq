
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Evd
open Environ
open Rawterm
(*i*)

(* Translation from AST to terms. *)

val interp_rawconstr     : 'a evar_map -> env -> Coqast.t -> rawconstr
val interp_constr        : 'a evar_map -> env -> Coqast.t -> constr
val interp_casted_constr : 'a evar_map -> env -> Coqast.t -> constr -> constr
val interp_type          : 'a evar_map -> env -> Coqast.t -> constr
val typed_type_of_com    : 'a evar_map -> env -> Coqast.t -> typed_type
val judgment_of_com      : 'a evar_map -> env -> Coqast.t -> unsafe_judgment

val interp_constrpattern : 
  'a evar_map -> env -> Coqast.t -> int list * constr_pattern

val redexp_of_ast : 
  'a evar_map -> env -> string * Coqast.t list -> Tacred.red_expr

(* Translation rules from V6 to V7:

constr_of_com_casted -> interp_casted_constr
constr_of_com_sort   -> interp_type
constr_of_com        -> interp_constr
rawconstr_of_com     -> interp_rawconstr  [+ env instead of sign]
type_of_com          -> typed_type_of_com Evd.empty
constr_of_com1 true  -> interp_type
*)

(*i For debug (or obsolete)
val dbize_op : CoqAst.loc -> string -> CoqAst.t list -> constr list -> constr
val dbize    : unit assumptions -> CoqAst.t -> constr

val dbize_cci      : 'c evar_map -> unit assumptions -> Coqast.t -> rawconstr
val absolutize_cci : 'c evar_map -> unit assumptions -> constr -> constr

val dbize_fw       : 'c evar_map -> unit assumptions -> Coqast.t -> rawconstr
val absolutize_fw  : 'c evar_map -> unit assumptions -> constr -> constr
val raw_fconstr_of_com :
  'c evar_map -> 'a assumptions -> Coqast.t -> rawconstr
val fconstr_of_com : 'a evar_map -> env -> Coqast.t -> constr
val fconstr_of_com_sort : 'a evar_map -> env -> Coqast.t -> constr

val raw_constr_of_compattern :
  'c evar_map -> 'a assumptions -> Coqast.t -> rawconstr

*)
val globalize_command : Coqast.t -> Coqast.t
(*
val globalize_ast     : Coqast.t -> Coqast.t

(* Typing with Trad, and re-checking with Mach *)
val fconstruct :'c evar_map -> context -> Coqast.t -> unsafe_judgment
val fconstruct_type : 'c evar_map -> context -> Coqast.t -> typed_type

(* Typing, re-checking with universes constraints *)
val fconstruct_with_univ :
  'a evar_map -> context -> Coqast.t -> unsafe_judgment

i*)

