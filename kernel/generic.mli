
(* $Id$ *)

open Util
open Names

exception FreeVar
exception Occur

type 'oper term =
  | DOP0 of 'oper                            (* atomic terms *)
  | DOP1 of 'oper * 'oper term               (* operator of arity 1 *)
  | DOP2 of 'oper * 'oper term * 'oper term  (* operator of arity 2 *)
  | DOPN of 'oper * 'oper term array         (* operator of variadic arity *)
  | DOPL of 'oper * 'oper term list          (* operator of variadic arity *)
  | DLAM of name * 'oper term                (* deBruijn binder on one term*)
  | DLAMV of name * 'oper term array         (* deBruijn binder on many terms*)
  | VAR of identifier                        (* named variable *)
  | Rel of int                               (* variable as deBruijn index *)

val isRel  : 'a term -> bool
val isVAR  : 'a term -> bool
val free_rels : 'a term -> Intset.t
val closedn : int -> 'a term -> unit
val closed0 : 'a term -> bool
val noccurn : int -> 'a term -> bool
val noccur_bet : int -> int -> 'a term -> bool


(* lifts *)
type lift_spec =
  | ELID
  | ELSHFT of lift_spec * int (* ELSHFT(l,n) == lift of n, then apply lift l *)
  | ELLFT of int * lift_spec  (* ELLFT(n,l)  == apply l to de Bruijn > n *)
                              (*                 i.e under n binders *)
val el_shft : int -> lift_spec -> lift_spec
val el_lift : lift_spec -> lift_spec
val el_liftn :  int -> lift_spec -> lift_spec
val reloc_rel: int -> lift_spec -> int

(* explicit substitutions of type 'a *)
type 'a subs =
  | ESID                   (* ESID       =          identity *)
  | CONS of 'a * 'a subs   (* CONS(t,S)  = (S.t)    parallel substitution *)
  | SHIFT of int * 'a subs (* SHIFT(n,S) = (^n o S) terms in S are relocated *)
                           (*                        with n vars *)
  | LIFT of int * 'a subs  (* LIFT(n,S) = (%n S) stands for ((^n o S).n...1) *)

val subs_cons  : 'a * 'a subs -> 'a subs
val subs_lift  : 'a subs -> 'a subs
val subs_shft  : int * 'a subs -> 'a subs
val exp_rel    : int -> int -> 'a subs -> (int * 'a, int) union
val expand_rel : int -> 'a subs -> (int * 'a, int) union

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo : info; sit : 'a }

val exliftn : lift_spec -> 'a term -> 'a term
val liftn : int -> int -> 'a term -> 'a term
val lift : int -> 'a term -> 'a term
val pop : 'a term -> 'a term
val lift_substituend : int -> 'a term substituend -> 'a term
val make_substituend : 'a term -> 'a term substituend
val substn_many : 'a term substituend array -> int -> 'a term -> 'a term
val substl : 'a term list -> 'a term -> 'a term
val subst1 : 'a term -> 'a term -> 'a term
val occur_opern : 'a -> 'a term -> bool
val occur_oper0 : 'a -> 'a term -> bool
val occur_var : identifier -> 'a term -> bool
val occur_oper : 'a -> 'a term -> bool
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

type modification_action = ABSTRACT | ERASE

type 'a modification =
  | NOT_OCCUR
  | DO_ABSTRACT of 'a * modification_action list
  | DO_REPLACE

val modify_opers : ('a term -> 'a term) -> ('a term -> 'a term -> 'a term) 
  -> ('a * 'a modification) list -> 'a term -> 'a term

val put_DLAMSV : name list -> 'a term array -> 'a term
val decomp_DLAMV : int -> 'a term -> 'a term array
val decomp_DLAMV_name : int -> 'a term -> name list * 'a term array
val decomp_all_DLAMV_name : 'a term -> name list * 'a term array
val put_DLAMSV_subst : identifier list -> 'a term array -> 'a term
val rel_vect : int -> int -> 'a term array
val rel_list : int -> int -> 'a term list

(* For hash-consing use *)
val hash_term :
  ('a term -> 'a term)
  * (('a -> 'a) * (name -> name) * (identifier -> identifier))
  -> 'a term -> 'a term
val comp_term : 'a term -> 'a term -> bool
