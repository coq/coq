
(* $Id$ *)

open Names
open Term
open Evd
open Environ

type metamap = (int * constr) list

(* This family of functions assumes its constr argument is known to be
   well-typable. It does not type-check, just recompute the type
   without any costly verifications. On non well-typable terms, it
   either produces a wrong result or raise an anomaly. Use with care.
   It doesn't handle predicative universes too. *)

val get_type_of : env -> 'a evar_map -> constr -> constr
val get_type_of_with_meta : env -> 'a evar_map -> metamap -> constr -> constr
val get_sort_of : env -> 'a evar_map -> constr -> sorts

(*i The following should be merged with mind_specif and put elsewhere 
    Note : it needs Reduction i*)

(* A light version of [mind_specif] *)

(* Invariant: We have\\
   -- Hnf (fullmind) = DOPN(AppL,[|coremind;..params..;..realargs..|])\\
   -- with mind  = MutInd ((sp,i),localvars) for some sp, i, localvars
 *)
type mutind_id = inductive_path * constr array

type mutind = {
  fullmind : constr;
  mind : mutind_id;
  nparams : int;
  nrealargs : int;
  nconstr : int;
  params : constr list;
  realargs : constr list;
  arity : constr }

(* [try_mutind_of sigma t] raise Induc if [t] is not an inductive type *)
val try_mutind_of : env -> 'a Evd.evar_map -> constr -> mutind
