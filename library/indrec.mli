
(* $Id$ *)

(*i*)
open Names
open Term
open Inductive
open Environ
open Evd
(*i*)

(* Eliminations. *)

val make_case_dep : unsafe_env -> 'a evar_map -> constr -> sorts -> constr
val make_case_nodep : unsafe_env -> 'a evar_map -> constr -> sorts -> constr
val make_case_gen : unsafe_env -> 'a evar_map -> constr -> sorts -> constr

val make_indrec : unsafe_env -> 'a evar_map -> 
  (mind_specif * bool * sorts) list -> constr -> constr array

val mis_make_indrec : unsafe_env -> 'a evar_map -> 
  (mind_specif * bool * sorts) list -> mind_specif -> constr array

val instanciate_indrec_scheme : sorts -> int -> constr -> constr

val build_indrec : 
  unsafe_env -> 'a evar_map -> (constr * bool * sorts) list -> constr array

val type_rec_branches : bool -> unsafe_env -> 'c evar_map -> constr 
  -> constr -> constr -> constr -> constr * constr array * constr

val make_rec_branch_arg : 
  unsafe_env -> 'a evar_map ->
    constr array * ('b * constr) option array * int ->
    constr -> constr -> recarg list -> constr

(*i Info pour JCF : déplacé dans pretyping, sert à Program
val transform_rec : unsafe_env -> 'c evar_map -> (constr array) 
  -> (constr * constr) -> constr
i*)

val is_mutind : unsafe_env -> 'a evar_map -> constr -> bool 

val branch_scheme : 
  unsafe_env -> 'a evar_map -> bool -> int -> constr -> constr

val pred_case_ml : unsafe_env -> 'c evar_map -> bool -> (constr * constr) 
  ->  constr array -> (int*constr)  ->constr

val pred_case_ml_onebranch : unsafe_env ->'c evar_map -> bool ->
  constr * constr ->int * constr * constr -> constr 

val make_case_ml :
  bool -> constr -> constr -> case_info -> constr array -> constr
