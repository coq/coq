
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Environ
(*i*)

(* Typing judgments. *)

type unsafe_judgment = { 
  uj_val : constr;
  uj_type : constr;
  uj_kind : constr }

type information = Logic | Inf of unsafe_judgment

val make_judge : constr -> typed_type -> unsafe_judgment

val j_val_only : unsafe_judgment -> constr


(* Base operations of the typing machine. *)

val relative : 'a unsafe_env -> int -> unsafe_judgment

val type_of_const : 'a unsafe_env -> constr -> typed_type

val type_of_mind : 'a unsafe_env -> constr -> typed_type

val type_of_mconstr : 'a unsafe_env -> constr -> typed_type

val type_of_case : 'a unsafe_env -> unsafe_judgment -> unsafe_judgment 
  -> unsafe_judgment array -> unsafe_judgment

val type_of_proposition : contents -> unsafe_judgment

val type_of_type : universe -> universes -> unsafe_judgment * universes

val assumption_of_judgement : 'a unsafe_env -> unsafe_judgment -> typed_type

val abs_rel : 
  'a unsafe_env -> name -> typed_type -> unsafe_judgment -> unsafe_judgment

val gen_rel :
  'a unsafe_env -> name -> typed_type -> unsafe_judgment -> unsafe_judgment

val cast_rel : 
  'a unsafe_env -> unsafe_judgment -> unsafe_judgment -> unsafe_judgment

val apply_rel_list : 
  'a unsafe_env -> bool -> unsafe_judgment list -> unsafe_judgment
    -> unsafe_judgment * universes

val check_fix : 'a unsafe_env -> constr -> unit
val check_cofix : 'a unsafe_env -> constr -> unit

val type_fixpoint : 'a unsafe_env -> name list -> typed_type array 
    -> unsafe_judgment array -> universes


