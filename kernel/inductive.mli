
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Sign
open Constant
open Environ
open Evd
(*i*)

(*s To give a more efficient access to the informations related to a given
  inductive type, we introduce the following type [mind_specif], which
  contains all the informations about the inductive type, including its
  instanciation arguments. *)

type mind_specif = {
  mis_sp : section_path;
  mis_mib : mutual_inductive_body;
  mis_tyi : int;
  mis_args : constr array;
  mis_mip : mutual_inductive_packet }

val mis_index : mind_specif -> int
val mis_ntypes : mind_specif -> int
val mis_nconstr : mind_specif -> int
val mis_nparams : mind_specif -> int
val mis_nrealargs : mind_specif -> int
val mis_kelim : mind_specif -> sorts list
val mis_recargs : mind_specif -> (recarg list) array array
val mis_recarg : mind_specif -> (recarg list) array
val mis_typename : mind_specif -> identifier
val mis_typepath : mind_specif -> section_path
val mis_is_recursive_subset : int list -> mind_specif -> bool
val mis_is_recursive : mind_specif -> bool
val mis_consnames : mind_specif -> identifier array
val mis_typed_arity : mind_specif -> typed_type
val mis_inductive : mind_specif -> inductive
val mis_arity : mind_specif -> constr
val mis_lc : mind_specif -> constr
val mis_lc_without_abstractions : mind_specif -> constr array
val mis_type_mconstructs : mind_specif -> constr array * constr array
val mis_params_ctxt : mind_specif -> (name * constr) list
val mis_sort : mind_specif -> sorts

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
  cs_args : (name * constr) list;
  cs_concl_realargs : constr array
}

val lift_constructor : int -> constructor_summary -> constructor_summary

(*s A variant of [mind_specif_of_mind] with pre-splitted args

   We recover the inductive type as \par
   [DOPN(AppL,[|MutInd mind;..params..;..realargs..|])] \par
   with [mind]  = [((sp,i),localvars)] for some [sp, i, localvars].

 *)

(* [inductive_family] = [inductive_instance] applied to global parameters *)
type inductive_family = IndFamily of mind_specif * constr list

val make_ind_family : mind_specif * constr list -> inductive_family
val dest_ind_family : inductive_family -> mind_specif * constr list

(* [inductive_type] = [inductive_family] applied to ``real'' parameters *)
type inductive_type = IndType of inductive_family * constr list

val make_ind_type : inductive_family * constr list -> inductive_type
val dest_ind_type : inductive_type -> inductive_family * constr list

val mkAppliedInd : inductive_type -> constr

val liftn_inductive_family : int -> int -> inductive_family -> inductive_family
val lift_inductive_family : int -> inductive_family -> inductive_family

val liftn_inductive_type : int -> int -> inductive_type -> inductive_type
val lift_inductive_type : int -> inductive_type -> inductive_type

val inductive_of_constructor : constructor -> inductive

val ith_constructor_of_inductive : inductive -> int -> constructor

val inductive_path_of_constructor_path : constructor_path -> inductive_path

val ith_constructor_path_of_inductive_path :
  inductive_path -> int -> constructor_path

(* This builds [(ci params (Rel 1)...(Rel ci_nargs))] which is the argument
   of a dependent predicate in a Cases branch *)
val build_dependent_constructor : constructor_summary -> constr

(* This builds [(I params (Rel 1)...(Rel nrealargs))] which is the type of
   the constructor argument of a dependent predicate in a cases branch *)
val build_dependent_inductive : inductive_family -> constr

(* if the arity for some inductive family [indf] associated to [(I
   params)] is [(x1:A1)...(xn:An)sort'] then [make_arity env sigma dep
   indf k] builds [(x1:A1)...(xn:An)sort] which is the arity of an
   elimination predicate on sort [k]; if [dep=true] then it rather
   builds [(x1:A1)...(xn:An)(I params x1...xn)->sort] *)
val make_arity : env -> 'a evar_map -> bool -> inductive_family ->
  sorts -> constr

(* [build_branch_type env dep p cs] builds the type of the branch
   associated to constructor [cs] in a Case with elimination predicate
   [p]; if [dep=true], the predicate is assumed dependent *)
val build_branch_type : env -> bool -> constr -> constructor_summary -> constr 

(* [find_m*type env sigma c] coerce [c] to an recursive type (I args).
   [find_mrectype], [find_minductype] and [find_mcoinductype]
   respectively accepts any recursive type, only an inductive type and
   only a coinductive type.
   They raise [Induc] if not convertible to a recursive type. *)

exception Induc
val find_mrectype     : env -> 'a evar_map -> constr -> inductive * constr list
val find_minductype   : env -> 'a evar_map -> constr -> inductive * constr list
val find_mcoinductype : env -> 'a evar_map -> constr -> inductive * constr list

val lookup_mind_specif : inductive -> env -> mind_specif

(* [find_inductive env sigma t] builds an [inductive_type] or raises
   [Induc] if [t] is not an inductive type; The result is relative to
   [env] and [sigma] *)

val find_inductive : env -> 'a evar_map -> constr -> inductive_type

(* [get_constructors indf] build an array of [constructor_summary]
   from some inductive type already analysed as an [inductive_family];
   global parameters are already instanciated in the constructor
   types; the resulting summaries are valid in the environment where
   [indf] is valid the names of the products of the constructors types
   are not renamed when [Anonymous] *)

val get_constructors : inductive_family -> constructor_summary array

(* [get_arity env sigma inf] returns the product and the sort of the
   arity of the inductive family described by [is]; global parameters are
   already instanciated; [indf] must be defined w.r.t. [env] and [sigma];
   the products signature is relative to [env] and [sigma]; the names
   of the products of the constructors types are not renamed when
   [Anonymous] *)

val get_arity : env -> 'a evar_map -> inductive_family ->
      (name * constr) list * sorts

(* Examples: assume
  
\begin{verbatim}
Inductive listn [A:Set] : nat -> Set :=
  niln : (listn A O)
| consn : (n:nat)A->(listn A n)->(listn A (S n)).
\end{verbatim}

has been defined. Then in some env containing ['x:nat'], 

[find_inductive env sigma (listn bool (S x))] returns

[is = {mind = 'listn'; params = 'bool'; realargs = '(S x)';
  nparams = 1; nrealargs = 1; nconstr = 2 }]

then [get_constructors env sigma is] returns

[[| { cs_cstr = 'niln'; cs_params = 'bool'; cs_nargs = 0;
     cs_args = []; cs_concl_realargs = [|O|]};
   { cs_cstr = 'consn'; cs_params = 'bool'; cs_nargs = 3;
     cs_args = [(Anonymous,'(listn A n)'),(Anonymous,'A'),(Name n,'nat')];
     cs_concl_realargs = [|'(S n)'|]} |]]

and [get_arity env sigma is] returns [[(Anonymous,'nat')],'Set'].
*)

(* Cases info *)

val make_case_info : mind_specif -> case_style option -> pattern_source array 
      -> case_info
val make_default_case_info : mind_specif -> case_info

