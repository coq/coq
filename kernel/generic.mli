
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

val free_rels : 'a term -> Intset.t

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)
val closed0 : 'a term -> bool

(* [noccurn n M] returns true iff [Rel n] does NOT occur in term [M]  *)
val noccurn : int -> 'a term -> bool

(* [noccur_between n m M] returns true iff [Rel p] does NOT occur in term [M]
  for n <= p < n+m *)
val noccur_between : int -> int -> 'a term -> bool

(* [liftn n k c] lifts by [n] indexes above [k] in [c] *)
val liftn : int -> int -> 'a term -> 'a term

(* [lift n c] lifts by [n] the positive indexes in [c] *)
val lift : int -> 'a term -> 'a term

(* [pop c] lifts by -1 the positive indexes in [c] *)
val pop : 'a term -> 'a term

(* [lift_context n ctxt] lifts terms in [ctxt] by [n] preserving
   (i.e. not lifting) the internal references between terms of [ctxt];
   more recent terms come first in [ctxt] *)
val lift_context : int -> (name * 'a term) list -> (name * 'a term) list

val substnl : 'a term list -> int -> 'a term -> 'a term
val substl : 'a term list -> 'a term -> 'a term
val subst1 : 'a term -> 'a term -> 'a term

(* [global_vars c] returns the list of [id]'s occurring as [VAR id] in [c] *)
val global_vars : 'a term -> identifier list

val global_vars_set : 'a term -> Idset.t
val subst_var : identifier -> 'a term -> 'a term
val replace_vars : (identifier * 'a term) list -> 'a term -> 'a term

(* [rel_list n m] and [rel_vect n m] compute [[Rel (n+m);...;Rel(n+1)]] *)
val rel_vect : int -> int -> 'a term array
val rel_list : int -> int -> 'a term list

(*i************************************************************************i*)
(*i Pour Closure *)
(* Explicit substitutions of type ['a]. [ESID] = identity. 
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
val expand_rel : int -> 'a subs -> (int * 'a, int) union
(*
val exp_rel    : int -> int -> 'a subs -> (int * 'a, int) union
*)
(*i*)

(*i Pour Closure *)
(*s Lifts. [ELSHFT(l,n)] == lift of [n], then apply [lift l].
  [ELLFT(n,l)] == apply [l] to de Bruijn > [n] i.e under n binders. *)
type lift_spec =
  | ELID
  | ELSHFT of lift_spec * int
  | ELLFT of int * lift_spec
val el_shft : int -> lift_spec -> lift_spec
val el_lift : lift_spec -> lift_spec
val reloc_rel: int -> lift_spec -> int
(*
val exliftn : lift_spec -> 'a term -> 'a term
val el_liftn :  int -> lift_spec -> lift_spec
*)
(*i*)

(*i À virer...
exception FreeVar
val closedn : int -> 'a term -> unit

exception Occur
type info = Closed | Open | Unknown
val global_varsl : identifier list -> 'a term -> identifier list
val subst_varn : identifier -> int -> 'a term -> 'a term
val sAPP : 'a term -> 'a term -> 'a term
val sAPPV : 'a term -> 'a term -> 'a term array
val sAPPVi : int -> 'a term -> 'a term -> 'a term

val sAPPList : 'a term -> 'a term list -> 'a term
val sAPPVList : 'a term -> 'a term list-> 'a term array
val sAPPViList : int -> 'a term -> 'a term list -> 'a term
val under_dlams : ('a term -> 'a term) -> 'a term -> 'a term
val put_DLAMSV : name list -> 'a term array -> 'a term
val decomp_DLAMV : int -> 'a term -> 'a term array
val decomp_DLAMV_name : int -> 'a term -> name list * 'a term array
val decomp_all_DLAMV_name : 'a term -> name list * 'a term array
val put_DLAMSV_subst : identifier list -> 'a term array -> 'a term
val count_dlam : 'a term -> int

(*s For hash-consing. (déplacé dans term) *)
val hash_term :
  ('a term -> 'a term)
  * (('a -> 'a) * (name -> name) * (identifier -> identifier))
  -> 'a term -> 'a term
val comp_term : 'a term -> 'a term -> bool
i*)
