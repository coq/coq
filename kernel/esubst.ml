
(* $Id$ *)

open Util

(*********************)
(*      Lifting      *)
(*********************)

(* Explicit lifts and basic operations *)
type lift =
  | ELID
  | ELSHFT of lift * int (* ELSHFT(l,n) == lift of n, then apply lift l *)
  | ELLFT of int * lift  (* ELLFT(n,l)  == apply l to de Bruijn > n *)
                         (*                 i.e under n binders *)

(* compose a relocation of magnitude n *)
let rec el_shft n = function
  | ELSHFT(el,k) -> el_shft (k+n) el
  | el -> if n = 0 then el else ELSHFT(el,n)


(* cross n binders *)
let rec el_liftn n = function
  | ELID -> ELID
  | ELLFT(k,el) -> el_liftn (n+k) el
  | el -> if n=0 then el else ELLFT(n, el)

let el_lift el = el_liftn 1 el

(* relocation of de Bruijn n in an explicit lift *)
let rec reloc_rel n = function
  | ELID -> n
  | ELLFT(k,el) ->
      if n <= k then n else (reloc_rel (n-k) el) + k
  | ELSHFT(el,k) -> (reloc_rel (n+k) el)

let rec is_lift_id = function
  | ELID -> true
  | ELSHFT(e,n) -> n=0 & is_lift_id e
  | ELLFT (_,e) -> is_lift_id e

(*********************)
(*  Substitutions    *)
(*********************)

(* (bounded) explicit substitutions of type 'a *)
type 'a subs =
  | ESID of int            (* ESID(n)    = %n END   bounded identity *)
  | CONS of 'a * 'a subs   (* CONS(t,S)  = (S.t)    parallel substitution *)
  | SHIFT of int * 'a subs (* SHIFT(n,S) = (^n o S) terms in S are relocated *)
                           (*                        with n vars *)
  | LIFT of int * 'a subs  (* LIFT(n,S) = (%n S) stands for ((^n o S).n...1) *)

(* operations of subs: collapses constructors when possible.
 * Needn't be recursive if we always use these functions
 *)

let subs_cons(x,s) = CONS(x,s)

let subs_liftn n = function
  | ESID p -> ESID (p+n) (* bounded identity lifted extends by p *)
  | LIFT (p,lenv) -> LIFT (p+n, lenv)
  | lenv -> LIFT (n,lenv)

let subs_lift a = subs_liftn 1 a

let subs_shft = function
  | (0, s)            -> s
  | (n, SHIFT (k,s1)) -> SHIFT (k+n, s1)
  | (n, s)            -> SHIFT (n,s)

let subs_shift_cons = function
  (0, s, t) -> CONS(t,s)
| (k, SHIFT(n,s1), t) -> CONS(t,SHIFT(k+n, s1))
| (k, s, t) -> CONS(t,SHIFT(k, s));;

(* Tests whether a substitution is extensionnaly equal to the identity *)
let rec is_subs_id = function
    ESID _ -> true
  | LIFT(_,s) -> is_subs_id s
  | SHIFT(0,s) -> is_subs_id s
  | _ -> false

(* Expands de Bruijn k in the explicit substitution subs
 * lams accumulates de shifts to perform when retrieving the i-th value
 * the rules used are the following:
 *
 *    [id]k       --> k
 *    [S.t]1      --> t
 *    [S.t]k      --> [S](k-1)  if k > 1
 *    [^n o S] k  --> [^n]([S]k)
 *    [(%n S)] k  --> k         if k <= n
 *    [(%n S)] k  --> [^n]([S](k-n))
 *
 * the result is (Inr (k+lams,p)) when the variable is just relocated
 * where p is None if the variable points inside subs and Some(k) if the
 * variable points k bindings beyond subs.
 *) 
let rec exp_rel lams k subs =
  match (k,subs) with
    | (1, CONS (def,_)) -> Inl(lams,def)
    | (_, CONS (_,l)) -> exp_rel lams (pred k) l
    | (_, LIFT (n,_)) when k<=n -> Inr(lams+k,None)
    | (_, LIFT (n,l)) -> exp_rel (n+lams) (k-n) l
    | (_, SHIFT (n,s)) -> exp_rel (n+lams) k s
    | (_, ESID n) when k<=n -> Inr(lams+k,None)
    | (_, ESID n) -> Inr(lams+k,Some (k-n))

let expand_rel k subs = exp_rel 0 k subs

