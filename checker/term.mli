open Names

type existential_key = int
type metavariable = int
type case_style =
    LetStyle
  | IfStyle
  | LetPatternStyle
  | MatchStyle
  | RegularStyle
type case_printing = { ind_nargs : int; style : case_style; }
type case_info = {
  ci_ind : inductive;
  ci_npar : int;
  ci_cstr_ndecls : int array;
  ci_pp_info : case_printing;
}
type contents = Pos | Null
type sorts = Prop of contents | Type of Univ.universe
type sorts_family = InProp | InSet | InType
val family_of_sort : sorts -> sorts_family
type 'a pexistential = existential_key * 'a array
type 'a prec_declaration = name array * 'a array * 'a array
type 'a pfixpoint = (int array * int) * 'a prec_declaration
type 'a pcofixpoint = int * 'a prec_declaration
type cast_kind = VMcast | DEFAULTcast
type constr =
    Rel of int
  | Var of identifier
  | Meta of metavariable
  | Evar of constr pexistential
  | Sort of sorts
  | Cast of constr * cast_kind * constr
  | Prod of name * constr * constr
  | Lambda of name * constr * constr
  | LetIn of name * constr * constr * constr
  | App of constr * constr array
  | Const of constant
  | Ind of inductive
  | Construct of constructor
  | Case of case_info * constr * constr * constr array
  | Fix of constr pfixpoint
  | CoFix of constr pcofixpoint
type existential = constr pexistential
type rec_declaration = constr prec_declaration
type fixpoint = constr pfixpoint
type cofixpoint = constr pcofixpoint
val strip_outer_cast : constr -> constr
val collapse_appl : constr -> constr
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

type named_declaration = identifier * constr option * constr
type rel_declaration = name * constr option * constr
type named_context = named_declaration list
val empty_named_context : named_context
val fold_named_context :
  (named_declaration -> 'a -> 'a) -> named_context -> init:'a -> 'a
type section_context = named_context
type rel_context = rel_declaration list
val empty_rel_context : rel_context
val rel_context_length : rel_context -> int
val rel_context_nhyps : rel_context -> int
val fold_rel_context :
  (rel_declaration -> 'a -> 'a) -> rel_context -> init:'a -> 'a
val map_context : (constr -> constr) -> named_context -> named_context
val map_rel_context : (constr -> constr) -> rel_context -> rel_context
val extended_rel_list : int -> rel_context -> constr list
val compose_lam : (name * constr) list -> constr -> constr
val decompose_lam : constr -> (name * constr) list * constr
val decompose_lam_n_assum : int -> constr -> rel_context * constr
val mkProd_or_LetIn : name * constr option * constr -> constr -> constr
val it_mkProd_or_LetIn : constr -> rel_context -> constr
val decompose_prod_assum : constr -> rel_context * constr
val decompose_prod_n_assum : int -> constr -> rel_context * constr

type arity = rel_context * sorts
val mkArity : arity -> constr
val destArity : constr -> arity
val isArity : constr -> bool
val compare_constr : (constr -> constr -> bool) -> constr -> constr -> bool
val eq_constr : constr -> constr -> bool

(* Validation *)
val val_sortfam : Validate.func
val val_sort : Validate.func
val val_constr : Validate.func
val val_rctxt : Validate.func
val val_nctxt : Validate.func
