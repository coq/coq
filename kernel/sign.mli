
(* $Id$ *)

(*i*)
open Names
(* open Generic *)
open Term
(*i*)

(*s Signatures of ordered named variables, intended to be accessed by name *)

type var_context = var_declaration list

val add_var : 
  identifier * constr option * typed_type -> var_context -> var_context
val add_var_decl : identifier * typed_type -> var_context -> var_context
val add_var_def : 
  identifier * constr * typed_type -> var_context -> var_context
val lookup_id : identifier -> var_context -> constr option * typed_type
val lookup_id_type : identifier -> var_context -> typed_type
val lookup_id_value : identifier -> var_context -> constr option 
val pop_var : identifier -> var_context -> var_context
val empty_var_context : var_context
val ids_of_var_context : var_context -> identifier list
val map_var_context : (constr -> constr) -> var_context -> var_context
val mem_var_context : identifier -> var_context -> bool
val fold_var_context : (var_declaration -> 'a -> 'a) -> var_context -> 'a -> 'a
val fold_var_context_reverse : ('a -> var_declaration -> 'a) -> 'a -> var_context -> 'a
val fold_var_context_both_sides :
  ('a -> var_declaration -> var_context -> 'a) -> var_context -> 'a -> 'a
val it_var_context_quantifier :
  (var_declaration -> constr -> constr) -> constr -> var_context -> constr
val instantiate_sign : var_context -> constr list -> (identifier * constr) list
val keep_hyps : Idset.t -> var_context -> var_context

(*s Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices *)

type rel_context = rel_declaration list

val add_rel : (name * constr option * typed_type) -> rel_context -> rel_context
val add_rel_decl : (name * typed_type) -> rel_context -> rel_context
val add_rel_def : (name * constr * typed_type) -> rel_context -> rel_context
val lookup_rel_type : int -> rel_context -> name * typed_type
val lookup_rel_value : int -> rel_context -> constr option
val lookup_rel_id : identifier -> rel_context -> int * typed_type
val empty_rel_context : rel_context
val rel_context_length : rel_context -> int
val lift_rel_context : int -> rel_context -> rel_context
val concat_rel_context : newer:rel_context -> older:rel_context -> rel_context
val ids_of_rel_context : rel_context -> identifier list
val decls_of_rel_context : rel_context -> (name * constr) list
val map_rel_context : (constr -> constr) -> rel_context -> rel_context

(*s This is used to translate names into de Bruijn indices and
   vice-versa without to care about typing information *)

type names_context
val add_name : name -> names_context -> names_context
val lookup_name_of_rel : int -> names_context -> name
val lookup_rel_of_name : identifier -> names_context -> int
val names_of_rel_context : rel_context -> names_context
val empty_names_context : names_context

(*s Term destructors *)

(* Transforms a product term $(x_1:T_1)..(x_n:T_n)T$ including letins
   into the pair $([(x_n,T_n);...;(x_1,T_1)],T)$, where $T$ is not a
   product nor a let. *)
val decompose_prod_assum : constr -> rel_context * constr

(* Transforms a lambda term $[x_1:T_1]..[x_n:T_n]T$ including letins
   into the pair $([(x_n,T_n);...;(x_1,T_1)],T)$, where $T$ is not a
   lambda nor a let. *)
val decompose_lam_assum : constr -> rel_context * constr

(* Given a positive integer n, transforms a product term 
   $(x_1:T_1)..(x_n:T_n)T$
   into the pair $([(xn,Tn);...;(x1,T1)],T)$. *)
val decompose_prod_n_assum : int -> constr -> rel_context * constr

(* Given a positive integer $n$, transforms a lambda term 
   $[x_1:T_1]..[x_n:T_n]T$ into the pair $([(x_n,T_n);...;(x_1,T_1)],T)$ *)
val decompose_lam_n_assum : int -> constr -> rel_context * constr
