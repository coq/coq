open Names
open Cic

val family_of_sort : sorts -> sorts_family
val family_equal : sorts_family -> sorts_family -> bool

val decompose_app : constr -> constr * constr list
val applist : constr * constr list -> constr
val iter_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit
exception LocalOccur
val closedn : int -> constr -> bool
val closed0 : constr -> bool
val noccurn : int -> constr -> bool
val noccur_between : int -> int -> constr -> bool
val noccur_with_meta : int -> int -> constr -> bool
val map_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr
val exliftn : Esubst.lift -> constr -> constr
val liftn : int -> int -> constr -> constr
val lift : int -> constr -> constr
type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo : info; sit : 'a; }
val lift_substituend : int -> constr substituend -> constr
val make_substituend : 'a -> 'a substituend
val substn_many : constr substituend array -> int -> constr -> constr
val substnl : constr list -> int -> constr -> constr
val substl : constr list -> constr -> constr
val subst1 : constr -> constr -> constr

val empty_rel_context : rel_context
val rel_context_length : rel_context -> int
val rel_context_nhyps : rel_context -> int
val fold_rel_context :
  (rel_declaration -> 'a -> 'a) -> rel_context -> init:'a -> 'a
val fold_rel_context_outside :
  (rel_declaration -> 'a -> 'a) -> rel_context -> init:'a -> 'a
val map_rel_decl : (constr -> constr) -> rel_declaration -> rel_declaration
val map_rel_context : (constr -> constr) -> rel_context -> rel_context
val extended_rel_list : int -> rel_context -> constr list
val compose_lam : (Name.t * constr) list -> constr -> constr
val decompose_lam : constr -> (Name.t * constr) list * constr
val decompose_lam_n_assum : int -> constr -> rel_context * constr
val mkProd_or_LetIn : rel_declaration -> constr -> constr
val it_mkProd_or_LetIn : constr -> rel_context -> constr
val decompose_prod_assum : constr -> rel_context * constr
val decompose_prod_n_assum : int -> constr -> rel_context * constr

type arity = rel_context * sorts

val mkArity : arity -> constr
val destArity : constr -> arity
val isArity : constr -> bool
val compare_constr : (constr -> constr -> bool) -> constr -> constr -> bool
val eq_constr : constr -> constr -> bool

(** Instance substitution for polymorphism. *)
val subst_instance_constr : Univ.universe_instance -> constr -> constr
val subst_instance_context : Univ.universe_instance -> rel_context -> rel_context
