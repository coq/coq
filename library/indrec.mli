
(* $Id$ *)

(*i*)
open Names
open Term
open Inductive
open Environ
open Evd
(*i*)

(* Eliminations. *)

val make_case_dep : env -> 'a evar_map -> inductive -> sorts -> constr
val make_case_nodep : env -> 'a evar_map -> inductive -> sorts -> constr
val make_case_gen : env -> 'a evar_map -> inductive -> sorts -> constr

val mis_make_indrec : env -> 'a evar_map -> 
  (mind_specif * bool * sorts) list -> mind_specif -> constr array

val instanciate_indrec_scheme : sorts -> int -> constr -> constr

val build_indrec : 
  env -> 'a evar_map -> (inductive * bool * sorts) list -> constr array

val type_rec_branches : bool -> env -> 'c evar_map -> constr 
  -> constr -> constr -> constr -> constr * constr array * constr

val make_rec_branch_arg : 
  env -> 'a evar_map ->
    constr array * ('b * constr) option array * int ->
    constr -> constr -> recarg list -> constr

(*i Info pour JCF : déplacé dans pretyping, sert à Program
val transform_rec : env -> 'c evar_map -> (constr array) 
  -> (constr * constr) -> constr
i*)

(*
val is_mutind : env -> 'a evar_map -> constr -> bool 
*)
(* Inutilisé
val pred_case_ml : env -> 'c evar_map -> bool ->
  constr * (inductive * constr list * constr list)
  ->  constr array -> int * constr  ->constr
*)

(* In [inductive * constr list * constr list], the second argument is
   the list of global parameters and the third the list of real args *)
val pred_case_ml_onebranch : env ->'c evar_map -> bool ->
  constr * (inductive * constr list * constr list)
  -> int * constr * constr -> constr 

(* Obsolète ?
val make_case_ml :
  bool -> constr -> constr -> case_info -> constr array -> constr
*)

