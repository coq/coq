
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Sign
(*i*)

(* Inductive types (internal representation). *)

type recarg = 
  | Param of int 
  | Norec 
  | Mrec of int 
  | Imbr of inductive_path * (recarg list)

type mutual_inductive_packet = {
  mind_consnames : identifier array;
  mind_typename : identifier;
  mind_lc : constr;
  mind_arity : typed_type;
  mind_nrealargs : int;
  mind_kelim : sorts list;
  mind_listrec : (recarg list) array;
  mind_finite : bool }

type mutual_inductive_body = {
  mind_kind : path_kind;
  mind_ntypes : int;
  mind_hyps : typed_type signature;
  mind_packets : mutual_inductive_packet array;
  mind_constraints : constraints;
  mind_singl : constr option;
  mind_nparams : int }

val mind_type_finite : mutual_inductive_body -> int -> bool


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

val mis_ntypes : mind_specif -> int
val mis_nconstr : mind_specif -> int
val mis_nparams : mind_specif -> int
val mis_nrealargs : mind_specif -> int
val mis_kelim : mind_specif -> sorts list
val mis_recargs : mind_specif -> (recarg list) array array
val mis_recarg : mind_specif -> (recarg list) array
val mis_typename : mind_specif -> identifier
val is_recursive : int list -> recarg list array -> bool
val mis_is_recursive : mind_specif -> bool
val mis_consnames : mind_specif -> identifier array

val mind_nth_type_packet : 
  mutual_inductive_body -> int -> mutual_inductive_packet

val make_case_info : mind_specif -> case_style option -> pattern_source array 
      -> case_info
val make_default_case_info : mind_specif -> case_info

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

(*s A variant of [mind_specif_of_mind] with pre-splitted args

   We recover the inductive type as \par
   [DOPN(AppL,[|MutInd mind;..params..;..realargs..|])] \par
   with [mind]  = [((sp,i),localvars)] for some [sp, i, localvars].

 *)

type inductive_summary = {
  mind : inductive;
  params : constr list;
  realargs : constr list;
  nparams : int;
  nrealargs : int;
  nconstr : int;
}

(*s Declaration of inductive types. *)

type mutual_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_finite : bool;
  mind_entry_inds : (identifier * constr * identifier list * constr) list }

val inductive_of_constructor : constructor -> inductive

val ith_constructor_of_inductive : inductive -> int -> constructor

val inductive_path_of_constructor_path : constructor_path -> inductive_path

val ith_constructor_path_of_inductive_path :
  inductive_path -> int -> constructor_path

(* This builds [(ci params (Rel 1)...(Rel ci_nargs))] which is the argument
   of predicate in a cases branch *)
val build_dependent_constructor : constructor_summary -> constr

(* This builds [(I params (Rel 1)...(Rel nrealargs))] which is the argument
   of predicate in a cases branch *)
val build_dependent_inductive : inductive_summary -> constr
