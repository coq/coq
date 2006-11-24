open Rawterm

(* Ocaml 3.06 Map.S does not handle is_empty *)
val idmap_is_empty : 'a Names.Idmap.t -> bool


(* [get_pattern_id pat] returns a list of all the variable appearing in [pat] *)
val get_pattern_id : cases_pattern -> Names.identifier list

(* [pattern_to_term pat] returns a rawconstr corresponding to [pat]. 
   [pat] must not contain occurences of anonymous pattern 
*)
val pattern_to_term : cases_pattern -> rawconstr 

(* 
   Some basic functions to rebuild rawconstr
   In each of them the location is Util.dummy_loc
*)
val mkRRef : Libnames.global_reference -> rawconstr
val mkRVar : Names.identifier -> rawconstr
val mkRApp  : rawconstr*(rawconstr list) -> rawconstr
val mkRLambda : Names.name*rawconstr*rawconstr -> rawconstr
val mkRProd : Names.name*rawconstr*rawconstr -> rawconstr
val mkRLetIn : Names.name*rawconstr*rawconstr -> rawconstr
val mkRCases : rawconstr option * tomatch_tuple * cases_clauses -> rawconstr
val mkRSort : rawsort -> rawconstr 
val mkRHole : unit -> rawconstr (* we only build Evd.BinderType Anonymous holes *)
val mkRCast : rawconstr* rawconstr -> rawconstr 
(*
  Some basic functions to decompose rawconstrs
  These are analogous to the ones constrs
*)
val raw_decompose_prod : rawconstr -> (Names.name*rawconstr) list * rawconstr
val raw_decompose_prod_or_letin : 
  rawconstr -> (Names.name*rawconstr option*rawconstr option) list * rawconstr
val raw_decompose_prod_n : int -> rawconstr -> (Names.name*rawconstr) list * rawconstr
val raw_decompose_prod_or_letin_n : int -> rawconstr -> 
  (Names.name*rawconstr option*rawconstr option) list * rawconstr
val raw_compose_prod : rawconstr -> (Names.name*rawconstr) list  ->  rawconstr 
val raw_compose_prod_or_letin: rawconstr -> 
  (Names.name*rawconstr option*rawconstr option) list  ->  rawconstr
val raw_decompose_app : rawconstr -> rawconstr*(rawconstr list)


(* [raw_make_eq t1 t2] build the rawconstr corresponding to [t2 = t1] *) 
val  raw_make_eq : ?typ:rawconstr -> rawconstr -> rawconstr -> rawconstr
(* [raw_make_neq t1 t2] build the rawconstr corresponding to [t1 <> t2] *) 
val  raw_make_neq : rawconstr -> rawconstr -> rawconstr
(* [raw_make_or P1 P2] build the rawconstr corresponding to [P1 \/ P2] *) 
val  raw_make_or : rawconstr -> rawconstr -> rawconstr

(* [raw_make_or_list [P1;...;Pn]] build the rawconstr corresponding 
   to [P1 \/ ( .... \/ Pn)] 
*) 
val  raw_make_or_list : rawconstr list -> rawconstr


(* alpha_conversion functions *)



(* Replace the var mapped in the rawconstr/context *)
val change_vars : Names.identifier Names.Idmap.t -> rawconstr -> rawconstr



(* [alpha_pat avoid pat] rename all the variables present in [pat] s.t. 
   the result does not share variables with [avoid]. This function create 
   a fresh variable for each occurence of the anonymous pattern.

   Also returns a mapping  from old variables to new ones and the concatenation of
   [avoid] with the variables appearing in the result.
*)
  val alpha_pat :
    Names.Idmap.key list ->
    Rawterm.cases_pattern ->
    Rawterm.cases_pattern * Names.Idmap.key list *
      Names.identifier Names.Idmap.t

(* [alpha_rt avoid rt] alpha convert [rt] s.t. the result repects barendregt 
   conventions and  does not share bound variables with avoid 
*)
val alpha_rt : Names.identifier list -> rawconstr -> rawconstr

(* same as alpha_rt but for case branches *)
val alpha_br : Names.identifier list ->
    Util.loc * Names.identifier list * Rawterm.cases_pattern list *
    Rawterm.rawconstr ->
    Util.loc * Names.identifier list * Rawterm.cases_pattern list *
    Rawterm.rawconstr


(* Reduction function *) 
val replace_var_by_term  :     
  Names.identifier ->
  Rawterm.rawconstr -> Rawterm.rawconstr -> Rawterm.rawconstr



(* 
   [is_free_in id rt] checks if [id] is a free variable in [rt]
*)
val is_free_in : Names.identifier -> rawconstr -> bool


val are_unifiable : cases_pattern -> cases_pattern -> bool 
val eq_cases_pattern : cases_pattern -> cases_pattern -> bool



(* 
   ids_of_pat : cases_pattern -> Idset.t 
   returns the set of variables appearing in a pattern 
*)
val   ids_of_pat : cases_pattern -> Names.Idset.t 

(* TODO: finish this function (Fix not treated) *)
val ids_of_rawterm: rawconstr -> Names.Idset.t

(* 
   removing let_in construction in a rawterm 
*)
val zeta_normalize : Rawterm.rawconstr -> Rawterm.rawconstr


val expand_as : rawconstr -> rawconstr
