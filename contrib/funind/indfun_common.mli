open Names
open Pp

val mk_rel_id : identifier -> identifier

val msgnl : std_ppcmds -> unit

val invalid_argument : string -> 'a

val fresh_id : identifier list -> string -> identifier
val fresh_name : identifier list -> string -> name 
val get_name : identifier list -> ?default:string -> name -> name 

val array_get_start : 'a array -> 'a array

val id_of_name : name -> identifier

val locate_ind : Libnames.reference -> inductive
val locate_constant : Libnames.reference -> constant
val locate_with_msg :
  Pp.std_ppcmds -> (Libnames.reference -> 'a) ->
  Libnames.reference -> 'a

val filter_map : ('a -> bool) -> ('a -> 'b) -> 'a list -> 'b list
val list_union_eq :
  ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
val list_add_set_eq :
  ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list

val chop_rlambda_n : int -> Rawterm.rawconstr ->
  (name*Rawterm.rawconstr) list * Rawterm.rawconstr

val chop_rprod_n : int -> Rawterm.rawconstr ->
  (name*Rawterm.rawconstr) list * Rawterm.rawconstr

val def_of_const : Term.constr -> Term.constr
val eq : Term.constr Lazy.t
val refl_equal : Term.constr Lazy.t
val const_of_id: identifier -> constant
