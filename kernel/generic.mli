
(* $Id$ *)

(*i*)
open Util
open Names
(*i*)

(* \label{generic_terms} A generic notion of terms with binders,
   over any kind of operators. 
   [DLAM] is a de Bruijn binder on one term, and [DLAMV] on many terms.
   [VAR] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)

type 'oper term =
  | DOP0 of 'oper
  | DOP1 of 'oper * 'oper term
  | DOP2 of 'oper * 'oper term * 'oper term
  | DOPN of 'oper * 'oper term array
  | DOPL of 'oper * 'oper term list
  | DLAM of name * 'oper term
  | DLAMV of name * 'oper term array
  | VAR of identifier
  | Rel of int

val isRel  : 'a term -> bool
val isVAR  : 'a term -> bool
val free_rels : 'a term -> Intset.t

exception FreeVar
exception Occur

val closedn : int -> 'a term -> unit
val closed0 : 'a term -> bool
val noccurn : int -> 'a term -> bool
val noccur_bet : int -> int -> 'a term -> bool

(*s Lifts. [ELSHFT(l,n)] == lift of [n], then apply [lift l].
  [ELLFT(n,l)] == apply [l] to de Bruijn > [n] i.e under n binders. *)

type lift_spec =
  | ELID
  | ELSHFT of lift_spec * int
  | ELLFT of int * lift_spec

val el_shft : int -> lift_spec -> lift_spec
val el_lift : lift_spec -> lift_spec
val el_liftn :  int -> lift_spec -> lift_spec
val reloc_rel: int -> lift_spec -> int
val exliftn : lift_spec -> 'a term -> 'a term
val liftn : int -> int -> 'a term -> 'a term
val lift : int -> 'a term -> 'a term
val pop : 'a term -> 'a term

(*s Explicit substitutions of type ['a]. [ESID] = identity. 
  [CONS(t,S)] = $S.t$ i.e. parallel substitution. [SHIFT(n,S)] = 
  $(\uparrow n~o~S)$ i.e. terms in S are relocated with n vars. 
  [LIFT(n,S)] = $(\%n~S)$ stands for $((\uparrow n~o~S).n...1)$. *)

type 'a subs =
  | ESID
  | CONS of 'a * 'a subs
  | SHIFT of int * 'a subs
  | LIFT of int * 'a subs

val subs_cons  : 'a * 'a subs -> 'a subs
val subs_lift  : 'a subs -> 'a subs
val subs_shft  : int * 'a subs -> 'a subs
val exp_rel    : int -> int -> 'a subs -> (int * 'a, int) union
val expand_rel : int -> 'a subs -> (int * 'a, int) union

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo : info; sit : 'a }

val lift_substituend : int -> 'a term substituend -> 'a term
val make_substituend : 'a term -> 'a term substituend
val substn_many : 'a term substituend array -> int -> 'a term -> 'a term
val substl : 'a term list -> 'a term -> 'a term
val subst1 : 'a term -> 'a term -> 'a term
val occur_opern : 'a -> 'a term -> bool
val occur_oper0 : 'a -> 'a term -> bool
val occur_var : identifier -> 'a term -> bool
val occur_oper : 'a -> 'a term -> bool
val process_opers_of_term : 
  ('a -> bool) -> ('a -> 'b) -> 'b list -> 'a term -> 'b list
val dependent : 'a term -> 'a term -> bool
val global_varsl : identifier list -> 'a term -> identifier list
val global_vars : 'a term -> identifier list
val global_vars_set : 'a term -> Idset.t
val subst_var : identifier -> 'a term -> 'a term
val subst_varn : identifier -> int -> 'a term -> 'a term
val replace_vars : 
  (identifier * 'a term substituend) list -> 'a term -> 'a term

val rename_diff_occ : 
  identifier -> identifier list ->'a term -> identifier list * 'a term 

val sAPP : 'a term -> 'a term -> 'a term
val sAPPV : 'a term -> 'a term -> 'a term array
val sAPPVi : int -> 'a term -> 'a term -> 'a term

val sAPPList : 'a term -> 'a term list -> 'a term
val sAPPVList : 'a term -> 'a term list-> 'a term array
val sAPPViList : int -> 'a term -> 'a term list -> 'a term
val under_dlams : ('a term -> 'a term) -> 'a term -> 'a term
val eq_term : 'a term -> 'a term -> bool

val put_DLAMSV : name list -> 'a term array -> 'a term
val decomp_DLAMV : int -> 'a term -> 'a term array
val decomp_DLAMV_name : int -> 'a term -> name list * 'a term array
val decomp_all_DLAMV_name : 'a term -> name list * 'a term array
val put_DLAMSV_subst : identifier list -> 'a term array -> 'a term
val rel_vect : int -> int -> 'a term array
val rel_list : int -> int -> 'a term list

val count_dlam : 'a term -> int

(*s For hash-consing. *)

val hash_term :
  ('a term -> 'a term)
  * (('a -> 'a) * (name -> name) * (identifier -> identifier))
  -> 'a term -> 'a term
val comp_term : 'a term -> 'a term -> bool
