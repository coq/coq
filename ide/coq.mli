open Names
open Term


val init : unit -> unit 
val interp : string -> Vernacexpr.vernac_expr

(* type hyp = (identifier * constr option * constr) * string *)

type hyp = ((identifier*string) * constr option * constr) * (string * string)
type concl = constr * string
type goal = hyp list * concl

val get_curent_goals : unit -> goal list

val print_no_goal : unit -> string

val process_exn : exn -> string*((int*int) option)

type word_class = Normal | Kwd | Reserved

val word_class : string -> word_class
