
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

val typed_type_of_judgment : 'a unsafe_env -> unsafe_judgment -> typed_type
val assumption_of_judgment : 'a unsafe_env -> unsafe_judgment -> typed_type

val relative : 'a unsafe_env -> int -> unsafe_judgment

val type_of_constant_or_existential : 'a unsafe_env -> constr -> typed_type

val type_of_inductive : 'a unsafe_env -> constr -> typed_type

val type_of_constructor : 'a unsafe_env -> constr -> constr

val type_of_case : 'a unsafe_env -> unsafe_judgment -> unsafe_judgment 
  -> unsafe_judgment array -> unsafe_judgment

val type_of_prop_or_set : contents -> unsafe_judgment

val type_of_type : universe -> universes -> unsafe_judgment * universes

val abs_rel : 
  'a unsafe_env -> name -> typed_type -> unsafe_judgment 
    -> unsafe_judgment * universes

val gen_rel :
  'a unsafe_env -> name -> typed_type -> unsafe_judgment 
    -> unsafe_judgment * universes

val cast_rel : 
  'a unsafe_env -> unsafe_judgment -> unsafe_judgment -> unsafe_judgment

val apply_rel_list : 
  'a unsafe_env -> bool -> unsafe_judgment list -> unsafe_judgment
    -> unsafe_judgment * universes

val check_fix : 'a unsafe_env -> constr -> unit
val check_cofix : 'a unsafe_env -> constr -> unit

val type_fixpoint : 'a unsafe_env -> name list -> typed_type array 
    -> unsafe_judgment array -> universes


