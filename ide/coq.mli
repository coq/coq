open Names
open Term
open Environ
open Evd

val version : unit -> string

val init : unit -> string list 
val interp : string -> Util.loc * Vernacexpr.vernac_expr
val interp_last : Util.loc * Vernacexpr.vernac_expr -> unit

val is_tactic : Vernacexpr.vernac_expr -> bool

(* type hyp = (identifier * constr option * constr) * string *)

type hyp = env * evar_map * 
           ((identifier*string) * constr option * constr) * (string * string)
type concl = env * evar_map * constr * string
type goal = hyp list * concl

val get_current_goals : unit -> goal list

val print_no_goal : unit -> string

val process_exn : exn -> string*((int*int) option)

type word_class = Normal | Kwd | Reserved

val word_class : string -> word_class

type reset_info = NoReset | Reset of Names.identifier * bool ref

val compute_reset_info : Vernacexpr.vernac_expr -> reset_info
val reset_initial : unit -> unit
val reset_to : identifier -> unit
val reset_to_mod : identifier -> unit

val hyp_menu : hyp -> (string * string) list
val concl_menu : concl -> (string * string) list

val is_in_coq_lib : string -> bool

