
(*i $Id$ i*)

(*i*)
open Names
open Univ
open Term
open Sign
open Declarations
open Environ
open Evd
(*i*)

(*s Inductives are accessible at several stages:

A [mutual_inductive_body] contains all information about a
declaration of mutual (co-)inductive types. These informations are
closed (they depend on no free variables) and an instance of them
corresponds to a [mutual_inductive_instance =
mutual_inductive_body * constr list]. One inductive type in an
instanciated packet corresponds to an [inductive_instance =
mutual_inductive_instance * int]. Applying global parameters to an
[inductive_instance] gives an [inductive_family = inductive_instance *
constr list]. Finally, applying real parameters gives an
[inductive_type = inductive_family * constr list]. At each level
corresponds various appropriated functions *)

type inductive_instance (* ex-[mind_specif] *)

val build_mis : inductive -> mutual_inductive_body -> inductive_instance

val mis_index : inductive_instance -> int
val mis_ntypes : inductive_instance -> int
val mis_nconstr : inductive_instance -> int
val mis_nparams : inductive_instance -> int
val mis_nrealargs : inductive_instance -> int
val mis_kelim : inductive_instance -> sorts list
val mis_recargs : inductive_instance -> (recarg list) array array
val mis_recarg : inductive_instance -> (recarg list) array
val mis_typename : inductive_instance -> identifier
val mis_typepath : inductive_instance -> section_path
val mis_is_recursive_subset : int list -> inductive_instance -> bool
val mis_is_recursive : inductive_instance -> bool
val mis_consnames : inductive_instance -> identifier array
val mis_conspaths : inductive_instance -> section_path array
val mis_inductive : inductive_instance -> inductive
val mis_arity : inductive_instance -> types
val mis_params_ctxt : inductive_instance -> rel_context
val mis_sort : inductive_instance -> sorts
val mis_constructor_type : int -> inductive_instance -> types
val mis_finite : inductive_instance -> bool 

(* The ccl of constructor is pre-normalised in the following functions *)
val mis_nf_lc : inductive_instance -> constr array

(*s [inductive_family] = [inductive_instance] applied to global parameters *)
type inductive_family = IndFamily of inductive_instance * constr list

val make_ind_family : inductive_instance * constr list -> inductive_family
val dest_ind_family : inductive_family -> inductive_instance * constr list

val liftn_inductive_family : int -> int -> inductive_family -> inductive_family
val lift_inductive_family : int -> inductive_family -> inductive_family
val substnl_ind_family : constr list -> int -> inductive_family 
  -> inductive_family

(*s [inductive_type] = [inductive_family] applied to ``real'' parameters *)
type inductive_type = IndType of inductive_family * constr list

val make_ind_type : inductive_family * constr list -> inductive_type
val dest_ind_type : inductive_type -> inductive_family * constr list

val mkAppliedInd : inductive_type -> constr

val liftn_inductive_type : int -> int -> inductive_type -> inductive_type
val lift_inductive_type : int -> inductive_type -> inductive_type
val substnl_ind_type : constr list -> int -> inductive_type -> inductive_type

(*s A [constructor] is an [inductive] + an index; the following functions
    destructs and builds [constructor] *)
val inductive_of_constructor : constructor -> inductive
val index_of_constructor : constructor -> int
val ith_constructor_of_inductive : inductive -> int -> constructor

val inductive_path_of_constructor_path : constructor_path -> inductive_path
val ith_constructor_path_of_inductive_path :
  inductive_path -> int -> constructor_path

(*s This type gathers useful informations about some instance of a constructor
    relatively to some implicit context (the current one)

    If [cs_cstr] is a constructor in [(I p1...pm a1...an)] then
    [cs_params] is [p1...pm] and the type of [MutConstruct(cs_cstr)
    p1...pn] is [(cs_args)(I p1...pm cs_concl_realargs)] where [cs_args]
    and [cs_params] are relative to the current env and [cs_concl_realargs]
    is relative to the current env enriched by [cs_args]
*)

type constructor_summary = {
  cs_cstr : constructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : rel_context;
  cs_concl_realargs : constr array
}

val lift_constructor : int -> constructor_summary -> constructor_summary

(*s Functions to build standard types related to inductive *)

(* This builds [(ci params (Rel 1)...(Rel ci_nargs))] which is the argument
   of a dependent predicate in a Cases branch *)
val build_dependent_constructor : constructor_summary -> constr

(* This builds [(I params (Rel 1)...(Rel nrealargs))] which is the type of
   the constructor argument of a dependent predicate in a cases branch *)
val build_dependent_inductive : inductive_family -> constr

(*s [rel_list n m] and [rel_vect n m] compute [[Rel (n+m);...;Rel(n+1)]] *)
(* (this is iota operator in C. Paulin habilitation thesis) *)
val rel_vect : int -> int -> constr array
val rel_list : int -> int -> constr list

(*s [extended_rel_vect n hyps] and [extended_rel_list n hyps]
    generalizes [rel_vect] when local definitions may occur in parameters *)
val extended_rel_vect : int -> rel_context -> constr array
val extended_rel_list : int -> rel_context -> constr list

(* if the arity for some inductive family [indf] associated to [(I
   params)] is [(x1:A1)...(xn:An)sort'] then [make_arity env sigma dep
   indf k] builds [(x1:A1)...(xn:An)sort] which is the arity of an
   elimination predicate on sort [k]; if [dep=true] then it rather
   builds [(x1:A1)...(xn:An)(I params x1...xn)->sort] *)
val make_arity : env -> bool -> inductive_family -> sorts -> constr

(* [build_branch_type env dep p cs] builds the type of the branch
   associated to constructor [cs] in a Case with elimination predicate
   [p]; if [dep=true], the predicate is assumed dependent *)
val build_branch_type : env -> bool -> constr -> constructor_summary -> constr 


(*s Extracting an inductive type from a constructions *)

exception Induc

(* [extract_mrectype c] assumes [c] is syntactically an inductive type
   applied to arguments then it returns its components; if not an
   inductive type, it raises [Induc] *)
val extract_mrectype  : constr -> inductive * constr list

(* [find_m*type env sigma c] coerce [c] to an recursive type (I args).
   [find_rectype], [find_inductive] and [find_coinductive]
   respectively accepts any recursive type, only an inductive type and
   only a coinductive type.
   They raise [Induc] if not convertible to a recursive type. *)

val find_mrectype    : env -> 'a evar_map -> constr -> inductive * constr list
val find_inductive   : env -> 'a evar_map -> constr -> inductive * constr list
val find_coinductive : env -> 'a evar_map -> constr -> inductive * constr list

val lookup_mind_specif : inductive -> env -> inductive_instance

(* [find_rectype env sigma t] builds an [inductive_type] or raises
   [Induc] if [t] is not a (co-)inductive type; The result is relative to
   [env] and [sigma] *)

val find_rectype : env -> 'a evar_map -> constr -> inductive_type

(* [get_constructors_types indf] returns the array of the types of
   constructors of the inductive\_family [indf], i.e. the types are
   instantiated by the parameters of the family (the type may be not
   in canonical form -- e.g. cf sets library) *)

val get_constructors_types : inductive_family -> types array
val get_constructor_type : inductive_family -> int -> types

(* [get_constructors indf] build an array of [constructor_summary]
   from some inductive type already analysed as an [inductive_family];
   global parameters are already instanciated in the constructor
   types; the resulting summaries are valid in the environment where
   [indf] is valid; the names of the products of the constructors types
   are not renamed when [Anonymous] *)

val get_constructors : inductive_family -> constructor_summary array
val get_constructor : inductive_family -> int -> constructor_summary

(* [get_arity_type indf] returns the type of the arity of the
   inductive family described by [indf]; global parameters are already
   instanciated (but the type may be not in canonical form -- e.g. cf
   sets library); the products signature is relative to the
   environment definition of [indf]; the names of the products of the
   constructors types are not renamed when [Anonymous]; [get_arity
   indf] does the same but normalises and decomposes it as an arity *)

val get_arity_type : inductive_family -> types
val get_arity : inductive_family -> arity

(* [get_arity_type indf] returns the type of the arity of the inductive
   family described by [indf]; global parameters are already instanciated *)



(* Examples: assume
  
\begin{verbatim}
Inductive listn [A:Set] : nat -> Set :=
  niln : (listn A O)
| consn : (n:nat)A->(listn A n)->(listn A (S n)).
\end{verbatim}

has been defined. Then in some env containing ['x:nat'], 
\begin{quote}
[find_rectype env sigma (listn bool (S x))] returns [IndType (indf, '(S x)')]
\end{quote}
where [indf = IndFamily ('listn',['bool'])].

Then, [get_constructors indf] returns
\begin{quote}
[[| { cs_cstr = 'niln'; cs_params = 'bool'; cs_nargs = 0;
     cs_args = []; cs_concl_realargs = [|O|]};
   { cs_cstr = 'consn'; cs_params = 'bool'; cs_nargs = 3;
     cs_args = [(Anonymous,'(listn A n)'),(Anonymous,'A'),(Name n,'nat')];
     cs_concl_realargs = [|'(S n)'|]} |]]
\end{quote}
and [get_arity indf] returns [[(Anonymous,'nat')],'Set'].
\smallskip
*)

(*s [Cases] info *)

val make_case_info : inductive_instance -> case_style option 
  -> pattern_source array -> case_info
val make_default_case_info : inductive_instance -> case_info
