
(* $Id$ *)

(*i*)
open Names
open Term
open Constant
open Inductive
open Environ
open Evd
(*i*)

(* Eliminations. *)

(* These functions build elimination predicate for Case tactic *)

val make_case_dep : env -> 'a evar_map -> inductive -> sorts -> constr
val make_case_nodep : env -> 'a evar_map -> inductive -> sorts -> constr
val make_case_gen : env -> 'a evar_map -> inductive -> sorts -> constr

(* This builds elimination scheme associated to inductive types *)

val mis_make_indrec : env -> 'a evar_map -> 
  (mind_specif * bool * sorts) list -> mind_specif -> constr array
val instanciate_indrec_scheme : sorts -> int -> constr -> constr

(* This builds complex [Scheme] *)

val build_indrec : 
  env -> 'a evar_map -> (inductive * bool * sorts) list -> constr array

(* These are for old Case/Match typing *)

val type_rec_branches : bool -> env -> 'c evar_map -> inductive_type
  -> constr -> constr -> constr -> constr array * constr
val make_rec_branch_arg : 
  env -> 'a evar_map ->
    int * ('b * constr) option array * int ->
    constr -> constructor_summary -> recarg list -> constr

val pred_case_ml_onebranch : env -> 'c evar_map -> bool ->
  inductive_type -> int * constr * constr -> constr 

(*i Info pour JCF : déplacé dans pretyping, sert à Program
val transform_rec : env -> 'c evar_map -> (constr array) 
  -> (constr * constr) -> constr
i*)

(*i Utilisés dans Program
val pred_case_ml : env -> 'c evar_map -> bool ->
  constr * (inductive * constr list * constr list)
  ->  constr array -> int * constr  ->constr
val make_case_ml :
  bool -> constr -> constr -> case_info -> constr array -> constr
i*)

