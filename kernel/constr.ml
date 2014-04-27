(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* File initially created by Gérard Huet and Thierry Coquand in 1984 *)
(* Extension to inductive constructions by Christine Paulin for Coq V5.6 *)
(* Extension to mutual inductive constructions by Christine Paulin for
   Coq V5.10.2 *)
(* Extension to co-inductive constructions by Eduardo Gimenez *)
(* Optimization of substitution functions by Chet Murthy *)
(* Optimization of lifting functions by Bruno Barras, Mar 1997 *)
(* Hash-consing by Bruno Barras in Feb 1998 *)
(* Restructuration of Coq of the type-checking kernel by Jean-Christophe 
   Filliâtre, 1999 *)
(* Abstraction of the syntax of terms and iterators by Hugo Herbelin, 2000 *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)

(* This file defines the internal syntax of the Calculus of
   Inductive Constructions (CIC) terms together with constructors,
   destructors, iterators and basic functions *)

open Util
open Names


type existential_key = Evar.t
type metavariable = int

(* This defines the strategy to use for verifiying a Cast *)
(* Warning: REVERTcast is not exported to vo-files; as of r14492, it has to *)
(* come after the vo-exported cast_kind so as to be compatible with coqchk *)
type cast_kind = VMcast | NATIVEcast | DEFAULTcast | REVERTcast

(* This defines Cases annotations *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle
type case_printing =
  { ind_nargs : int; (* length of the arity of the inductive type *)
    style     : case_style }
type case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array; (* number of pattern vars of each constructor (with let's)*)
    ci_cstr_nargs : int array; (* number of pattern vars of each constructor (w/o let's) *)
    ci_pp_info    : case_printing (* not interpreted by the kernel *)
  }

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr array
type ('constr, 'types) prec_declaration =
    Name.t array * 'types array * 'constr array
type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration

(* [Var] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)
type ('constr, 'types) kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of Sorts.t
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant
  | Ind       of inductive
  | Construct of constructor
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint

(* constr is the fixpoint of the previous type. Requires option
   -rectypes of the Caml compiler to be set *)
type t = (t,t) kind_of_term
type constr = t

type existential = existential_key * constr array
type rec_declaration = Name.t array * constr array * constr array
type fixpoint = (int array * int) * rec_declaration
type cofixpoint = int * rec_declaration

type types = constr

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a DeBrujin index with number n *)
let rels =
  [|Rel  1;Rel  2;Rel  3;Rel  4;Rel  5;Rel  6;Rel  7; Rel  8;
    Rel  9;Rel 10;Rel 11;Rel 12;Rel 13;Rel 14;Rel 15; Rel 16|]

let mkRel n = if 0<n && n<=16 then rels.(n-1) else Rel n

(* Construct a type *)
let mkProp   = Sort Sorts.prop
let mkSet    = Sort Sorts.set
let mkType u = Sort (Sorts.Type u)
let mkSort   = function
  | Sorts.Prop Sorts.Null -> mkProp (* Easy sharing *)
  | Sorts.Prop Sorts.Pos -> mkSet
  | s -> Sort s

(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
let mkCast (t1,k2,t2) =
  match t1 with
  | Cast (c,k1, _) when (k1 == VMcast || k1 == NATIVEcast) && k1 == k2 -> Cast (c,k1,t2)
  | _ -> Cast (t1,k2,t2)

(* Constructs the product (x:t1)t2 *)
let mkProd (x,t1,t2) = Prod (x,t1,t2)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda (x,t1,t2) = Lambda (x,t1,t2)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn (x,c1,t,c2) = LetIn (x,c1,t,c2)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
(* We ensure applicative terms have at least one argument and the
   function is not itself an applicative term *)
let mkApp (f, a) =
  if Int.equal (Array.length a) 0 then f else
    match f with
      | App (g, cl) -> App (g, Array.append cl a)
      | _ -> App (f, a)

(* Constructs a constant *)
let mkConst c = Const c

(* Constructs an existential variable *)
let mkEvar e = Evar e

(* Constructs the ith (co)inductive type of the block named kn *)
let mkInd m = Ind m

(* Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. The array of terms correspond to the variables
   introduced in the section *)
let mkConstruct c = Construct c

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkCase (ci, p, c, ac) = Case (ci, p, c, ac)

(* If recindxs = [|i1,...in|]
      funnames = [|f1,...fn|]
      typarray = [|t1,...tn|]
      bodies   = [|b1,...bn|]
   then

      mkFix ((recindxs,i),(funnames,typarray,bodies))

   constructs the ith function of the block

    Fixpoint f1 [ctx1] : t1 := b1
    with     f2 [ctx2] : t2 := b2
    ...
    with     fn [ctxn] : tn := bn.

   where the length of the jth context is ij.
*)

let mkFix fix = Fix fix

(* If funnames = [|f1,...fn|]
      typarray = [|t1,...tn|]
      bodies   = [|b1,...bn|]
   then

      mkCoFix (i,(funnames,typsarray,bodies))

   constructs the ith function of the block

    CoFixpoint f1 : t1 := b1
    with       f2 : t2 := b2
    ...
    with       fn : tn := bn.
*)
let mkCoFix cofix= CoFix cofix

(* Constructs an existential variable named "?n" *)
let mkMeta  n =  Meta n

(* Constructs a Variable named id *)
let mkVar id = Var id


(************************************************************************)
(*    kind_of_term = constructions as seen by the user                 *)
(************************************************************************)

(* User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

let kind c = c

(****************************************************************************)
(*              Functions to recur through subterms                         *)
(****************************************************************************)

(* [fold f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

let fold f acc c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> acc
  | Cast (c,_,t) -> f (f acc c) t
  | Prod (_,t,c) -> f (f acc t) c
  | Lambda (_,t,c) -> f (f acc t) c
  | LetIn (_,b,t,c) -> f (f (f acc b) t) c
  | App (c,l) -> Array.fold_left f (f acc c) l
  | Evar (_,l) -> Array.fold_left f acc l
  | Case (_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
    Array.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl
  | CoFix (_,(lna,tl,bl)) ->
    Array.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl

(* [iter f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let iter f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_,t) -> f c; f t
  | Prod (_,t,c) -> f t; f c
  | Lambda (_,t,c) -> f t; f c
  | LetIn (_,b,t,c) -> f b; f t; f c
  | App (c,l) -> f c; Array.iter f l
  | Evar (_,l) -> Array.iter f l
  | Case (_,p,c,bl) -> f p; f c; Array.iter f bl
  | Fix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl
  | CoFix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl

(* [iter_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_with_binders g f n c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (_,t,c) -> f n t; f (g n) c
  | Lambda (_,t,c) -> f n t; f (g n) c
  | LetIn (_,b,t,c) -> f n b; f n t; f (g n) c
  | App (c,l) -> f n c; CArray.Fun1.iter f n l
  | Evar (_,l) -> CArray.Fun1.iter f n l
  | Case (_,p,c,bl) -> f n p; f n c; CArray.Fun1.iter f n bl
  | Fix (_,(_,tl,bl)) ->
      CArray.Fun1.iter f n tl;
      CArray.Fun1.iter f (iterate g (Array.length tl) n) bl
  | CoFix (_,(_,tl,bl)) ->
      CArray.Fun1.iter f n tl;
      CArray.Fun1.iter f (iterate g (Array.length tl) n) bl

(* [map f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let map f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (b,k,t) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkCast (b', k, t')
  | Prod (na,t,b) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkProd (na, t', b')
  | Lambda (na,t,b) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkLambda (na, t', b')
  | LetIn (na,b,t,k) ->
      let b' = f b in
      let t' = f t in
      let k' = f k in
      if b'==b && t' == t && k'==k then c
      else mkLetIn (na, b', t', k')
  | App (b,l) ->
      let b' = f b in
      let l' = Array.smartmap f l in
      if b'==b && l'==l then c
      else mkApp (b', l')
  | Evar (e,l) ->
      let l' = Array.smartmap f l in
      if l'==l then c
      else mkEvar (e, l')
  | Case (ci,p,b,bl) ->
      let b' = f b in
      let p' = f p in
      let bl' = Array.smartmap f bl in
      if b'==b && p'==p && bl'==bl then c
      else mkCase (ci, p', b', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.smartmap f tl in
      let bl' = Array.smartmap f bl in
      if tl'==tl && bl'==bl then c
      else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let tl' = Array.smartmap f tl in
      let bl' = Array.smartmap f bl in
      if tl'==tl && bl'==bl then c
      else mkCoFix (ln,(lna,tl',bl'))

(* Like {!map} but with an accumulator. *)

let fold_map f accu c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> accu, c
  | Cast (b,k,t) ->
      let accu, b' = f accu b in
      let accu, t' = f accu t in
      if b'==b && t' == t then accu, c
      else accu, mkCast (b', k, t')
  | Prod (na,t,b) ->
      let accu, b' = f accu b in
      let accu, t' = f accu t in
      if b'==b && t' == t then accu, c
      else accu, mkProd (na, t', b')
  | Lambda (na,t,b) ->
      let accu, b' = f accu b in
      let accu, t' = f accu t in
      if b'==b && t' == t then accu, c
      else accu, mkLambda (na, t', b')
  | LetIn (na,b,t,k) ->
      let accu, b' = f accu b in
      let accu, t' = f accu t in
      let accu, k' = f accu k in
      if b'==b && t' == t && k'==k then accu, c
      else accu, mkLetIn (na, b', t', k')
  | App (b,l) ->
      let accu, b' = f accu b in
      let accu, l' = Array.smartfoldmap f accu l in
      if b'==b && l'==l then accu, c
      else accu, mkApp (b', l')
  | Evar (e,l) ->
      let accu, l' = Array.smartfoldmap f accu l in
      if l'==l then accu, c
      else accu, mkEvar (e, l')
  | Case (ci,p,b,bl) ->
      let accu, b' = f accu b in
      let accu, p' = f accu p in
      let accu, bl' = Array.smartfoldmap f accu bl in
      if b'==b && p'==p && bl'==bl then accu, c
      else accu, mkCase (ci, p', b', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let accu, tl' = Array.smartfoldmap f accu tl in
      let accu, bl' = Array.smartfoldmap f accu bl in
      if tl'==tl && bl'==bl then accu, c
      else accu, mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let accu, tl' = Array.smartfoldmap f accu tl in
      let accu, bl' = Array.smartfoldmap f accu bl in
      if tl'==tl && bl'==bl then accu, c
      else accu, mkCoFix (ln,(lna,tl',bl'))

(* [map_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let map_with_binders g f l c0 = match kind c0 with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c0
  | Cast (c, k, t) ->
    let c' = f l c in
    let t' = f l t in
    if c' == c && t' == t then c0
    else mkCast (c', k, t')
  | Prod (na, t, c) ->
    let t' = f l t in
    let c' = f (g l) c in
    if t' == t && c' == c then c0
    else mkProd (na, t', c')
  | Lambda (na, t, c) ->
    let t' = f l t in
    let c' = f (g l) c in
    if t' == t && c' == c then c0
    else mkLambda (na, t', c')
  | LetIn (na, b, t, c) ->
    let b' = f l b in
    let t' = f l t in
    let c' = f (g l) c in
    if b' == b && t' == t && c' == c then c0
    else mkLetIn (na, b', t', c')
  | App (c, al) ->
    let c' = f l c in
    let al' = CArray.Fun1.smartmap f l al in
    if c' == c && al' == al then c0
    else mkApp (c', al')
  | Evar (e, al) ->
    let al' = CArray.Fun1.smartmap f l al in
    if al' == al then c0
    else mkEvar (e, al')
  | Case (ci, p, c, bl) ->
    let p' = f l p in
    let c' = f l c in
    let bl' = CArray.Fun1.smartmap f l bl in
    if p' == p && c' == c && bl' == bl then c0
    else mkCase (ci, p', c', bl')
  | Fix (ln, (lna, tl, bl)) ->
    let tl' = CArray.Fun1.smartmap f l tl in
    let l' = iterate g (Array.length tl) l in
    let bl' = CArray.Fun1.smartmap f l' bl in
    if tl' == tl && bl' == bl then c0
    else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
    let tl' = CArray.Fun1.smartmap f l tl in
    let l' = iterate g (Array.length tl) l in
    let bl' = CArray.Fun1.smartmap f l' bl in
    mkCoFix (ln,(lna,tl',bl'))

(* [compare f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account *)


let compare_head f t1 t2 =
  match kind t1, kind t2 with
  | Rel n1, Rel n2 -> Int.equal n1 n2
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Sort s1, Sort s2 -> Sorts.equal s1 s2
  | Cast (c1,_,_), _ -> f c1 t2
  | _, Cast (c2,_,_) -> f t1 c2
  | Prod (_,t1,c1), Prod (_,t2,c2) -> f t1 t2 && f c1 c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) -> f t1 t2 && f c1 c2
  | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> f b1 b2 && f t1 t2 && f c1 c2
  | App (Cast(c1, _, _),l1), _ -> f (mkApp (c1,l1)) t2
  | _, App (Cast (c2, _, _),l2) -> f t1 (mkApp (c2,l2))
  | App (c1,l1), App (c2,l2) ->
    Int.equal (Array.length l1) (Array.length l2) &&
      f c1 c2 && Array.equal f l1 l2
  | Evar (e1,l1), Evar (e2,l2) -> Evar.equal e1 e2 && Array.equal f l1 l2
  | Const c1, Const c2 -> eq_constant c1 c2
  | Ind c1, Ind c2 -> eq_ind c1 c2
  | Construct c1, Construct c2 -> eq_constructor c1 c2
  | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
      f p1 p2 && f c1 c2 && Array.equal f bl1 bl2
  | Fix ((ln1, i1),(_,tl1,bl1)), Fix ((ln2, i2),(_,tl2,bl2)) ->
      Int.equal i1 i2 && Array.equal Int.equal ln1 ln2
      && Array.equal f tl1 tl2 && Array.equal f bl1 bl2
  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      Int.equal ln1 ln2 && Array.equal f tl1 tl2 && Array.equal f bl1 bl2
  | _ -> false

(*******************************)
(*  alpha conversion functions *)
(*******************************)

(* alpha conversion : ignore print names and casts *)

let rec eq_constr m n =
  (m == n) || compare_head eq_constr m n

let equal m n = eq_constr m n (* to avoid tracing a recursive fun *)

(** We only use this function over blocks! *)
let tag t = Obj.tag (Obj.repr t)

let constr_ord_int f t1 t2 =
  let (=?) f g i1 i2 j1 j2=
    let c = f i1 i2 in
    if Int.equal c 0 then g j1 j2 else c in
  let (==?) fg h i1 i2 j1 j2 k1 k2=
    let c=fg i1 i2 j1 j2 in
    if Int.equal c 0 then h k1 k2 else c in
  let fix_cmp (a1, i1) (a2, i2) =
    ((Array.compare Int.compare) =? Int.compare) a1 a2 i1 i2
  in
  match kind t1, kind t2 with
    | Rel n1, Rel n2 -> Int.compare n1 n2
    | Meta m1, Meta m2 -> Int.compare m1 m2
    | Var id1, Var id2 -> Id.compare id1 id2
    | Sort s1, Sort s2 -> Sorts.compare s1 s2
    | Cast (c1,_,_), _ -> f c1 t2
    | _, Cast (c2,_,_) -> f t1 c2
    | Prod (_,t1,c1), Prod (_,t2,c2)
    | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
        (f =? f) t1 t2 c1 c2
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) ->
        ((f =? f) ==? f) b1 b2 t1 t2 c1 c2
    | App (Cast(c1,_,_),l1), _ -> f (mkApp (c1,l1)) t2
    | _, App (Cast(c2, _,_),l2) -> f t1 (mkApp (c2,l2))
    | App (c1,l1), App (c2,l2) -> (f =? (Array.compare f)) c1 c2 l1 l2
    | Evar (e1,l1), Evar (e2,l2) ->
        (Evar.compare =? (Array.compare f)) e1 e2 l1 l2
    | Const c1, Const c2 -> con_ord c1 c2
    | Ind ind1, Ind ind2 -> ind_ord ind1 ind2
    | Construct ct1, Construct ct2 -> constructor_ord ct1 ct2
    | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
        ((f =? f) ==? (Array.compare f)) p1 p2 c1 c2 bl1 bl2
    | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
        ((fix_cmp =? (Array.compare f)) ==? (Array.compare f))
        ln1 ln2 tl1 tl2 bl1 bl2
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
        ((Int.compare =? (Array.compare f)) ==? (Array.compare f))
        ln1 ln2 tl1 tl2 bl1 bl2
    | t1, t2 -> Int.compare (tag t1) (tag t2)

let rec compare m n=
  constr_ord_int compare m n

(*******************)
(*  hash-consing   *)
(*******************)

(* Hash-consing of [constr] does not use the module [Hashcons] because
   [Hashcons] is not efficient on deep tree-like data
   structures. Indeed, [Hashcons] is based the (very efficient)
   generic hash function [Hashtbl.hash], which computes the hash key
   through a depth bounded traversal of the data structure to be
   hashed. As a consequence, for a deep [constr] like the natural
   number 1000 (S (S (... (S O)))), the same hash is assigned to all
   the sub [constr]s greater than the maximal depth handled by
   [Hashtbl.hash]. This entails a huge number of collisions in the
   hash table and leads to cubic hash-consing in this worst-case.

   In order to compute a hash key that is independent of the data
   structure depth while being constant-time, an incremental hashing
   function must be devised. A standard implementation creates a cache
   of the hashing function by decorating each node of the hash-consed
   data structure with its hash key. In that case, the hash function
   can deduce the hash key of a toplevel data structure by a local
   computation based on the cache held on its substructures.
   Unfortunately, this simple implementation introduces a space
   overhead that is damageable for the hash-consing of small [constr]s
   (the most common case). One can think of an heterogeneous
   distribution of caches on smartly chosen nodes, but this is forbidden
   by the use of generic equality in Coq source code. (Indeed, this forces
   each [constr] to have a unique canonical representation.)

   Given that hash-consing proceeds inductively, we can nonetheless
   computes the hash key incrementally during hash-consing by changing
   a little the signature of the hash-consing function: it now returns
   both the hash-consed term and its hash key. This simple solution is
   implemented in the following code: it does not introduce a space
   overhead in [constr], that's why the efficiency is unchanged for
   small [constr]s. Besides, it does handle deep [constr]s without
   introducing an unreasonable number of collisions in the hash table.
   Some benchmarks make us think that this implementation of
   hash-consing is linear in the size of the hash-consed data
   structure for our daily use of Coq.
*)

let array_eqeq t1 t2 =
  t1 == t2 ||
  (Int.equal (Array.length t1) (Array.length t2) &&
   let rec aux i =
     (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
   in aux 0)

let hasheq t1 t2 =
  match t1, t2 with
    | Rel n1, Rel n2 -> n1 == n2
    | Meta m1, Meta m2 -> m1 == m2
    | Var id1, Var id2 -> id1 == id2
    | Sort s1, Sort s2 -> s1 == s2
    | Cast (c1,k1,t1), Cast (c2,k2,t2) -> c1 == c2 && k1 == k2 && t1 == t2
    | Prod (n1,t1,c1), Prod (n2,t2,c2) -> n1 == n2 && t1 == t2 && c1 == c2
    | Lambda (n1,t1,c1), Lambda (n2,t2,c2) -> n1 == n2 && t1 == t2 && c1 == c2
    | LetIn (n1,b1,t1,c1), LetIn (n2,b2,t2,c2) ->
      n1 == n2 && b1 == b2 && t1 == t2 && c1 == c2
    | App (c1,l1), App (c2,l2) -> c1 == c2 && array_eqeq l1 l2
    | Evar (e1,l1), Evar (e2,l2) -> Evar.equal e1 e2 && array_eqeq l1 l2
    | Const c1, Const c2 -> c1 == c2
    | Ind (sp1,i1), Ind (sp2,i2) -> sp1 == sp2 && Int.equal i1 i2
    | Construct ((sp1,i1),j1), Construct ((sp2,i2),j2) ->
      sp1 == sp2 && Int.equal i1 i2 && Int.equal j1 j2
    | Case (ci1,p1,c1,bl1), Case (ci2,p2,c2,bl2) ->
      ci1 == ci2 && p1 == p2 && c1 == c2 && array_eqeq bl1 bl2
    | Fix ((ln1, i1),(lna1,tl1,bl1)), Fix ((ln2, i2),(lna2,tl2,bl2)) ->
      Int.equal i1 i2
      && Array.equal Int.equal ln1 ln2
      && array_eqeq lna1 lna2
      && array_eqeq tl1 tl2
      && array_eqeq bl1 bl2
    | CoFix(ln1,(lna1,tl1,bl1)), CoFix(ln2,(lna2,tl2,bl2)) ->
      Int.equal ln1 ln2
      && array_eqeq lna1 lna2
      && array_eqeq tl1 tl2
      && array_eqeq bl1 bl2
    | _ -> false

(** Note that the following Make has the side effect of creating
    once and for all the table we'll use for hash-consing all constr *)

module HashsetTerm =
  Hashset.Make(struct type t = constr let equal = hasheq end)

module HashsetTermArray =
  Hashset.Make(struct type t = constr array let equal = array_eqeq end)

let term_table = HashsetTerm.create 19991
(* The associative table to hashcons terms. *)

let term_array_table = HashsetTermArray.create 4999
(* The associative table to hashcons term arrays. *)

open Hashset.Combine

let hash_cast_kind = function
| VMcast -> 0
| NATIVEcast -> 1
| DEFAULTcast -> 2
| REVERTcast -> 3

(* [hashcons hash_consing_functions constr] computes an hash-consed
   representation for [constr] using [hash_consing_functions] on
   leaves. *)
let hashcons (sh_sort,sh_ci,sh_construct,sh_ind,sh_con,sh_na,sh_id) =
  let rec hash_term t =
    match t with
      | Var i ->
	(Var (sh_id i), combinesmall 1 (Id.hash i))
      | Sort s ->
	(Sort (sh_sort s), combinesmall 2 (Sorts.hash s))
      | Cast (c, k, t) ->
	let c, hc = sh_rec c in
	let t, ht = sh_rec t in
	(Cast (c, k, t), combinesmall 3 (combine3 hc (hash_cast_kind k) ht))
      | Prod (na,t,c) ->
	let t, ht = sh_rec t
	and c, hc = sh_rec c in
	(Prod (sh_na na, t, c), combinesmall 4 (combine3 (Name.hash na) ht hc))
      | Lambda (na,t,c) ->
	let t, ht = sh_rec t
	and c, hc = sh_rec c in
	(Lambda (sh_na na, t, c), combinesmall 5 (combine3 (Name.hash na) ht hc))
      | LetIn (na,b,t,c) ->
	let b, hb = sh_rec b in
	let t, ht = sh_rec t in
	let c, hc = sh_rec c in
	(LetIn (sh_na na, b, t, c), combinesmall 6 (combine4 (Name.hash na) hb ht hc))
      | App (c,l) ->
	let c, hc = sh_rec c in
	let l, hl = hash_term_array l in
	(App (c,l), combinesmall 7 (combine hl hc))
      | Evar (e,l) ->
	let l, hl = hash_term_array l in
	(Evar (e,l), combinesmall 8 (combine (Evar.hash e) hl))
      | Const c ->
	(Const (sh_con c), combinesmall 9 (Constant.hash c))
      | Ind ind ->
	(Ind (sh_ind ind), combinesmall 10 (ind_hash ind))
      | Construct c ->
	(Construct (sh_construct c), combinesmall 11 (constructor_hash c))
      | Case (ci,p,c,bl) ->
	let p, hp = sh_rec p
	and c, hc = sh_rec c in
	let bl,hbl = hash_term_array bl in
	let hbl = combine (combine hc hp) hbl in
	(Case (sh_ci ci, p, c, bl), combinesmall 12 hbl)
      | Fix (ln,(lna,tl,bl)) ->
	let bl,hbl = hash_term_array bl in
	let tl,htl = hash_term_array tl in
        let () = Array.iteri (fun i x -> Array.unsafe_set lna i (sh_na x)) lna in
        let fold accu na = combine (Name.hash na) accu in
        let hna = Array.fold_left fold 0 lna in
        let h = combine3 hna hbl htl in
	(Fix (ln,(lna,tl,bl)), combinesmall 13 h)
      | CoFix(ln,(lna,tl,bl)) ->
	let bl,hbl = hash_term_array bl in
	let tl,htl = hash_term_array tl in
        let () = Array.iteri (fun i x -> Array.unsafe_set lna i (sh_na x)) lna in
        let fold accu na = combine (Name.hash na) accu in
        let hna = Array.fold_left fold 0 lna in
        let h = combine3 hna hbl htl in
	(CoFix (ln,(lna,tl,bl)), combinesmall 14 h)
      | Meta n ->
	(t, combinesmall 15 n)
      | Rel n ->
	(t, combinesmall 16 n)

  and sh_rec t =
    let (y, h) = hash_term t in
    (* [h] must be positive. *)
    let h = h land 0x3FFFFFFF in
    (HashsetTerm.repr h y term_table, h)

  (* Note : During hash-cons of arrays, we modify them *in place* *)

  and hash_term_array t =
    let accu = ref 0 in
    for i = 0 to Array.length t - 1 do
      let x, h = sh_rec (Array.unsafe_get t i) in
      accu := combine !accu h;
      Array.unsafe_set t i x
    done;
    (* [h] must be positive. *)
    let h = !accu land 0x3FFFFFFF in
    (HashsetTermArray.repr h t term_array_table, h)

  in
  (* Make sure our statically allocated Rels (1 to 16) are considered
     as canonical, and hence hash-consed to themselves *)
  ignore (hash_term_array rels);

  fun t -> fst (sh_rec t)

(* Exported hashing fonction on constr, used mainly in plugins.
   Appears to have slight differences from [snd (hash_term t)] above ? *)

let rec hash t =
  match kind t with
    | Var i -> combinesmall 1 (Id.hash i)
    | Sort s -> combinesmall 2 (Sorts.hash s)
    | Cast (c, k, t) ->
      let hc = hash c in
      let ht = hash t in
      combinesmall 3 (combine3 hc (hash_cast_kind k) ht)
    | Prod (_, t, c) -> combinesmall 4 (combine (hash t) (hash c))
    | Lambda (_, t, c) -> combinesmall 5 (combine (hash t) (hash c))
    | LetIn (_, b, t, c) ->
      combinesmall 6 (combine3 (hash b) (hash t) (hash c))
    | App (Cast(c, _, _),l) -> hash (mkApp (c,l))
    | App (c,l) ->
      combinesmall 7 (combine (hash_term_array l) (hash c))
    | Evar (e,l) ->
      combinesmall 8 (combine (Evar.hash e) (hash_term_array l))
    | Const c ->
      combinesmall 9 (Constant.hash c)
    | Ind ind ->
      combinesmall 10 (ind_hash ind)
    | Construct c ->
      combinesmall 11 (constructor_hash c)
    | Case (_ , p, c, bl) ->
      combinesmall 12 (combine3 (hash c) (hash p) (hash_term_array bl))
    | Fix (ln ,(_, tl, bl)) ->
      combinesmall 13 (combine (hash_term_array bl) (hash_term_array tl))
    | CoFix(ln, (_, tl, bl)) ->
       combinesmall 14 (combine (hash_term_array bl) (hash_term_array tl))
    | Meta n -> combinesmall 15 n
    | Rel n -> combinesmall 16 n

and hash_term_array t =
  Array.fold_left (fun acc t -> combine (hash t) acc) 0 t

module CaseinfoHash =
struct
  type t = case_info
  type u = inductive -> inductive
  let hashcons hind ci = { ci with ci_ind = hind ci.ci_ind }
  let pp_info_equal info1 info2 =
    Int.equal info1.ind_nargs info2.ind_nargs &&
    info1.style == info2.style
  let equal ci ci' =
    ci.ci_ind == ci'.ci_ind &&
    Int.equal ci.ci_npar ci'.ci_npar &&
    Array.equal Int.equal ci.ci_cstr_ndecls ci'.ci_cstr_ndecls && (* we use [Array.equal] on purpose *)
    Array.equal Int.equal ci.ci_cstr_nargs ci'.ci_cstr_nargs && (* we use [Array.equal] on purpose *)
    pp_info_equal ci.ci_pp_info ci'.ci_pp_info  (* we use (=) on purpose *)
  open Hashset.Combine
  let hash_pp_info info =
    let h = match info.style with
    | LetStyle -> 0
    | IfStyle -> 1
    | LetPatternStyle -> 2
    | MatchStyle -> 3
    | RegularStyle -> 4
    in
    combine info.ind_nargs h
  let hash ci =
    let h1 = ind_hash ci.ci_ind in
    let h2 = Int.hash ci.ci_npar in
    let h3 = Array.fold_left combine 0 ci.ci_cstr_ndecls in
    let h4 = Array.fold_left combine 0 ci.ci_cstr_nargs in
    let h5 = hash_pp_info ci.ci_pp_info in
    combine5 h1 h2 h3 h4 h5
end

module Hcaseinfo = Hashcons.Make(CaseinfoHash)

let case_info_hash = CaseinfoHash.hash

let hcons_caseinfo = Hashcons.simple_hcons Hcaseinfo.generate hcons_ind

let hcons =
  hashcons
    (Sorts.hcons,
     hcons_caseinfo,
     hcons_construct,
     hcons_ind,
     hcons_con,
     Name.hcons,
     Id.hcons)

(* let hcons_types = hcons_constr *)

(*******)
(* Type of abstract machine values *)
(** FIXME: nothing to do there *)
type values
