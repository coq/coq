
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Environ
(*i*)


(* Base operations of the typing machine. *)

val make_judge : constr -> typed_type -> unsafe_judgment

val j_val_only : unsafe_judgment -> constr

(* If [j] is the judgement $c:t:s$, then [typed_type_of_judgment env j]
   constructs the typed type $t:s$, while [assumption_of_judgement env j]
   cosntructs the type type $c:t$, checking that $t$ is a sort. *)

val typed_type_of_judgment : unsafe_env -> unsafe_judgment -> typed_type
val assumption_of_judgment : unsafe_env -> unsafe_judgment -> typed_type

val relative : unsafe_env -> int -> unsafe_judgment

val type_of_constant : unsafe_env -> constr -> typed_type

val type_of_inductive : unsafe_env -> constr -> typed_type

val type_of_constructor : unsafe_env -> constr -> constr

val type_of_case : unsafe_env -> unsafe_judgment -> unsafe_judgment 
  -> unsafe_judgment array -> unsafe_judgment

val type_case_branches :
  unsafe_env -> constr -> constr -> constr -> constr 
    -> constr * constr array * constr 

val type_of_prop_or_set : contents -> unsafe_judgment

val type_of_type : universe -> unsafe_judgment * constraints

val abs_rel : 
  unsafe_env -> name -> typed_type -> unsafe_judgment 
    -> unsafe_judgment * constraints

val gen_rel :
  unsafe_env -> name -> typed_type -> unsafe_judgment 
    -> unsafe_judgment * constraints

val cast_rel : 
  unsafe_env -> unsafe_judgment -> unsafe_judgment -> unsafe_judgment

val apply_rel_list : 
  unsafe_env -> bool -> unsafe_judgment list -> unsafe_judgment
    -> unsafe_judgment * constraints

val check_fix : unsafe_env -> Spset.t -> constr -> unit
val check_cofix : unsafe_env -> Spset.t -> constr -> unit

val type_fixpoint : unsafe_env -> name list -> typed_type array 
    -> unsafe_judgment array -> constraints
