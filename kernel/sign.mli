
(*i $Id$ i*)

(*i*)
open Names
open Term
(*i*)

(*s Signatures of ordered named declarations *)

type named_context = named_declaration list

val add_named_decl : 
  identifier * constr option * types -> named_context -> named_context
val add_named_assum : identifier * types -> named_context -> named_context
val add_named_def : 
  identifier * constr * types -> named_context -> named_context
val lookup_id : identifier -> named_context -> constr option * types
val lookup_id_type : identifier -> named_context -> types
val lookup_id_value : identifier -> named_context -> constr option 
val pop_named_decl : identifier -> named_context -> named_context
val empty_named_context : named_context
val ids_of_named_context : named_context -> identifier list
val map_named_context : (constr -> constr) -> named_context -> named_context
val mem_named_context : identifier -> named_context -> bool
val fold_named_context :
  (named_declaration -> 'a -> 'a) -> named_context -> 'a -> 'a
val fold_named_context_reverse :
  ('a -> named_declaration -> 'a) -> 'a -> named_context -> 'a
val fold_named_context_both_sides :
  ('a -> named_declaration -> named_context -> 'a) -> named_context -> 'a -> 'a
val it_named_context_quantifier :
  (named_declaration -> constr -> constr) -> constr -> named_context -> constr
val instantiate_sign :
  named_context -> constr list -> (identifier * constr) list
val keep_hyps : Idset.t -> named_context -> named_context
val instance_from_named_context : named_context -> constr list

(*s Signatures of ordered section variables *)

type section_declaration = variable_path * constr option * constr
type section_context = section_declaration list

val instance_from_section_context : section_context -> constr list

(*s Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices *)

(* In [rel_context], more recent declaration is on top *)
type rel_context = rel_declaration list

(* In [rev_rel_context], older declaration is on top *)
type rev_rel_context = rel_declaration list

val add_rel_decl : (name * constr option * types) -> rel_context -> rel_context
val add_rel_assum : (name * types) -> rel_context -> rel_context
val add_rel_def : (name * constr * types) -> rel_context -> rel_context
val lookup_rel_type : int -> rel_context -> name * types
val lookup_rel_value : int -> rel_context -> constr option
val lookup_rel_id : identifier -> rel_context -> int * types
val empty_rel_context : rel_context
val rel_context_length : rel_context -> int
val lift_rel_context : int -> rel_context -> rel_context
val lift_rev_rel_context : int -> rev_rel_context -> rev_rel_context
val concat_rel_context : newer:rel_context -> older:rel_context -> rel_context
val ids_of_rel_context : rel_context -> identifier list
val assums_of_rel_context : rel_context -> (name * constr) list
val map_rel_context : (constr -> constr) -> rel_context -> rel_context
val push_named_to_rel_context : named_context -> rel_context -> rel_context
val reverse_rel_context : rel_context -> rev_rel_context

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
