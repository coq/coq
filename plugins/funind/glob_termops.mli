open Names
open Glob_term
open Misctypes

(* [get_pattern_id pat] returns a list of all the variable appearing in [pat] *)
val get_pattern_id : cases_pattern -> Id.t list

(* [pattern_to_term pat] returns a glob_constr corresponding to [pat].
   [pat] must not contain occurrences of anonymous pattern
*)
val pattern_to_term : cases_pattern -> glob_constr

(*
   Some basic functions to rebuild glob_constr
   In each of them the location is Util.Loc.ghost
*)
val mkGRef : Globnames.global_reference -> glob_constr
val mkGVar : Id.t -> glob_constr
val mkGApp  : glob_constr*(glob_constr list) -> glob_constr
val mkGLambda : Name.t * glob_constr * glob_constr -> glob_constr
val mkGProd : Name.t * glob_constr * glob_constr -> glob_constr
val mkGLetIn : Name.t * glob_constr * glob_constr option * glob_constr -> glob_constr
val mkGCases : glob_constr option * tomatch_tuples * cases_clauses -> glob_constr
val mkGSort : glob_sort -> glob_constr
val mkGHole : unit -> glob_constr (* we only build Evd.BinderType Anonymous holes *)
val mkGCast : glob_constr* glob_constr -> glob_constr
(*
  Some basic functions to decompose glob_constrs
  These are analogous to the ones constrs
*)
val glob_decompose_prod : glob_constr -> (Name.t*glob_constr) list * glob_constr
val glob_decompose_prod_or_letin :
  glob_constr -> (Name.t*glob_constr option*glob_constr option) list * glob_constr
val glob_decompose_prod_n : int -> glob_constr -> (Name.t*glob_constr) list * glob_constr
val glob_decompose_prod_or_letin_n : int -> glob_constr ->
  (Name.t*glob_constr option*glob_constr option) list * glob_constr
val glob_compose_prod : glob_constr -> (Name.t*glob_constr) list  ->  glob_constr
val glob_compose_prod_or_letin: glob_constr ->
  (Name.t*glob_constr option*glob_constr option) list  ->  glob_constr
val glob_decompose_app : glob_constr -> glob_constr*(glob_constr list)


(* [glob_make_eq t1 t2] build the glob_constr corresponding to [t2 = t1] *)
val  glob_make_eq : ?typ:glob_constr -> glob_constr -> glob_constr -> glob_constr
(* [glob_make_neq t1 t2] build the glob_constr corresponding to [t1 <> t2] *)
val  glob_make_neq : glob_constr -> glob_constr -> glob_constr
(* [glob_make_or P1 P2] build the glob_constr corresponding to [P1 \/ P2] *)
val  glob_make_or : glob_constr -> glob_constr -> glob_constr

(* [glob_make_or_list [P1;...;Pn]] build the glob_constr corresponding
   to [P1 \/ ( .... \/ Pn)]
*)
val  glob_make_or_list : glob_constr list -> glob_constr


(* alpha_conversion functions *)



(* Replace the var mapped in the glob_constr/context *)
val change_vars : Id.t Id.Map.t -> glob_constr -> glob_constr



(* [alpha_pat avoid pat] rename all the variables present in [pat] s.t.
   the result does not share variables with [avoid]. This function create
   a fresh variable for each occurrence of the anonymous pattern.

   Also returns a mapping  from old variables to new ones and the concatenation of
   [avoid] with the variables appearing in the result.
*)
  val alpha_pat :
    Id.Map.key list ->
    Glob_term.cases_pattern ->
    Glob_term.cases_pattern * Id.Map.key list *
      Id.t Id.Map.t

(* [alpha_rt avoid rt] alpha convert [rt] s.t. the result repects barendregt
   conventions and  does not share bound variables with avoid
*)
val alpha_rt : Id.t list -> glob_constr -> glob_constr

(* same as alpha_rt but for case branches *)
val alpha_br : Id.t list ->
    Loc.t * Id.t list * Glob_term.cases_pattern list *
    Glob_term.glob_constr ->
    Loc.t * Id.t list * Glob_term.cases_pattern list *
    Glob_term.glob_constr


(* Reduction function *)
val replace_var_by_term  :
  Id.t ->
  Glob_term.glob_constr -> Glob_term.glob_constr -> Glob_term.glob_constr



(*
   [is_free_in id rt] checks if [id] is a free variable in [rt]
*)
val is_free_in : Id.t -> glob_constr -> bool


val are_unifiable : cases_pattern -> cases_pattern -> bool
val eq_cases_pattern : cases_pattern -> cases_pattern -> bool



(*
   ids_of_pat : cases_pattern -> Id.Set.t
   returns the set of variables appearing in a pattern
*)
val   ids_of_pat : cases_pattern -> Id.Set.t

(* TODO: finish this function (Fix not treated) *)
val ids_of_glob_constr: glob_constr -> Id.Set.t

(*
   removing let_in construction in a glob_constr
*)
val zeta_normalize : Glob_term.glob_constr -> Glob_term.glob_constr


val expand_as : glob_constr -> glob_constr
