
(* $Id$ *)

(*i*)
open Names
open Sign
open Term
open Environ
(*i*)

type constr_pattern =
  | PRef of constr array reference
  | PRel of int
  | PApp of constr_pattern * constr_pattern array
  | PSoApp of int * constr_pattern list
  | PBinder of binder_kind * name * constr_pattern * constr_pattern
  | PLet of identifier * constr_pattern * constr_pattern * constr_pattern
  | PSort of Rawterm.rawsort
  | PMeta of int option
  | PCase of constr_pattern option * constr_pattern * constr_pattern array

val occur_meta_pattern : constr_pattern -> bool

type constr_label =
  | ConstNode of section_path
  | IndNode of inductive_path
  | CstrNode of constructor_path
  | VarNode of identifier

exception BoundPattern

(* [head_pattern_bound t] extracts the head variable/constant of the
   type [t] or raises [BoundPattern] (even if a sort); it raises an anomaly
   if [t] is an abstraction *)

val head_pattern_bound : constr_pattern -> constr_label

(* [head_of_constr_reference c] assumes [r] denotes a reference and
   returns its label; raises an anomaly otherwise *)

val head_of_constr_reference : Term.constr -> constr_label

(* [pattern_of_constr c] translates a term [c] with metavariables into
   a pattern; currently, no destructor (Cases, Fix, Cofix) and no
   existential variable are allowed in [c] *)

val pattern_of_constr : constr -> constr_pattern


exception PatternMatchingFailure

(* [matches pat c] matches [c] against [pat] and returns the resulting
   assignment of metavariables; it raises [PatternMatchingFailure] if
   not matchable; bindings are given in increasing order based on the
   numbers given in the pattern *)
val matches      :
  constr_pattern -> constr -> (int * constr) list

(* [is_matching pat c] just tells if [c] matches against [pat] *)

val is_matching      :
  constr_pattern -> constr -> bool

(* [matches_conv env sigma] matches up to conversion in environment
   [(env,sigma)] when constants in pattern are concerned; it raises
   [PatternMatchingFailure] if not matchable; bindings are given in
   increasing order based on the numbers given in the pattern *)

val matches_conv :
  env -> 'a Evd.evar_map -> constr_pattern -> constr -> (int * constr) list

(* [is_matching_conv env sigma pat c] tells if [c] matches against [pat]
   up to conversion for constants in patterns *)

val is_matching_conv :
  env -> 'a Evd.evar_map -> constr_pattern -> constr -> bool

