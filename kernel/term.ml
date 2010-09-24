(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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
open Pp
open Names
open Univ
open Esubst


type existential_key = int
type metavariable = int

(* This defines the strategy to use for verifiying a Cast *)

(* This defines Cases annotations *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle
type case_printing =
  { ind_nargs : int; (* length of the arity of the inductive type *)
    style     : case_style }
type case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array; (* number of pattern vars of each constructor *)
    ci_pp_info    : case_printing (* not interpreted by the kernel *)
  }

(* Sorts. *)

type contents = Pos | Null

type sorts =
  | Prop of contents                      (* proposition types *)
  | Type of universe

let prop_sort = Prop Null
let set_sort = Prop Pos
let type1_sort = Type type1_univ

type sorts_family = InProp | InSet | InType

let family_of_sort = function
  | Prop Null -> InProp
  | Prop Pos -> InSet
  | Type _ -> InType

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

type cast_kind = VMcast | DEFAULTcast

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr array
type ('constr, 'types) prec_declaration =
    name array * 'types array * 'constr array
type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration

(* [Var] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)
type ('constr, 'types) kind_of_term =
  | Rel       of int
  | Var       of identifier
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of sorts
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of name * 'types * 'types
  | Lambda    of name * 'types * 'constr
  | LetIn     of name * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant
  | Ind       of inductive
  | Construct of constructor
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint

(* Experimental *)
type ('constr, 'types) kind_of_type =
  | SortType   of sorts
  | CastType   of 'types * 'types
  | ProdType   of name * 'types * 'types
  | LetInType  of name * 'constr * 'types * 'types
  | AtomicType of 'constr * 'constr array

let kind_of_type = function
  | Sort s -> SortType s
  | Cast (c,_,t) -> CastType (c, t)
  | Prod (na,t,c) -> ProdType (na, t, c)
  | LetIn (na,b,t,c) -> LetInType (na, b, t, c)
  | App (c,l) -> AtomicType (c, l)
  | (Rel _ | Meta _ | Var _ | Evar _ | Const _ | Case _ | Fix _ | CoFix _ | Ind _ as c)
    -> AtomicType (c,[||])
  | (Lambda _ | Construct _) -> failwith "Not a type"

(* constr is the fixpoint of the previous type. Requires option
   -rectypes of the Caml compiler to be set *)
type constr = (constr,constr) kind_of_term

type existential = existential_key * constr array
type rec_declaration = name array * constr array * constr array
type fixpoint = (int array * int) * rec_declaration
type cofixpoint = int * rec_declaration

(***************************)
(* hash-consing functions  *)
(***************************)

let comp_term t1 t2 =
  match t1, t2 with
  | Rel n1, Rel n2 -> n1 = n2
  | Meta m1, Meta m2 -> m1 == m2
  | Var id1, Var id2 -> id1 == id2
  | Sort s1, Sort s2 -> s1 == s2
  | Cast (c1,_,t1), Cast (c2,_,t2) -> c1 == c2 & t1 == t2
  | Prod (n1,t1,c1), Prod (n2,t2,c2) -> n1 == n2 & t1 == t2 & c1 == c2
  | Lambda (n1,t1,c1), Lambda (n2,t2,c2) -> n1 == n2 & t1 == t2 & c1 == c2
  | LetIn (n1,b1,t1,c1), LetIn (n2,b2,t2,c2) ->
      n1 == n2 & b1 == b2 & t1 == t2 & c1 == c2
  | App (c1,l1), App (c2,l2) -> c1 == c2 & array_for_all2 (==) l1 l2
  | Evar (e1,l1), Evar (e2,l2) -> e1 = e2 & array_for_all2 (==) l1 l2
  | Const c1, Const c2 -> c1 == c2
  | Ind (sp1,i1), Ind (sp2,i2) -> sp1 == sp2 & i1 = i2
  | Construct ((sp1,i1),j1), Construct ((sp2,i2),j2) ->
      sp1 == sp2 & i1 = i2 & j1 = j2
  | Case (ci1,p1,c1,bl1), Case (ci2,p2,c2,bl2) ->
      ci1 == ci2 & p1 == p2 & c1 == c2 & array_for_all2 (==) bl1 bl2
  | Fix (ln1,(lna1,tl1,bl1)), Fix (ln2,(lna2,tl2,bl2)) ->
      ln1 = ln2
      & array_for_all2 (==) lna1 lna2
      & array_for_all2 (==) tl1 tl2
      & array_for_all2 (==) bl1 bl2
  | CoFix(ln1,(lna1,tl1,bl1)), CoFix(ln2,(lna2,tl2,bl2)) ->
      ln1 = ln2
      & array_for_all2 (==) lna1 lna2
      & array_for_all2 (==) tl1 tl2
      & array_for_all2 (==) bl1 bl2
  | _ -> false

let hash_term (sh_rec,(sh_sort,sh_con,sh_kn,sh_na,sh_id)) t =
  match t with
  | Rel _ -> t
  | Meta x -> Meta x
  | Var x -> Var (sh_id x)
  | Sort s -> Sort (sh_sort s)
  | Cast (c, k, t) -> Cast (sh_rec c, k, (sh_rec t))
  | Prod (na,t,c) -> Prod (sh_na na, sh_rec t, sh_rec c)
  | Lambda (na,t,c) -> Lambda (sh_na na, sh_rec t, sh_rec c)
  | LetIn (na,b,t,c) -> LetIn (sh_na na, sh_rec b, sh_rec t, sh_rec c)
  | App (c,l) -> App (sh_rec c, Array.map sh_rec l)
  | Evar (e,l) -> Evar (e, Array.map sh_rec l)
  | Const c -> Const (sh_con c)
  | Ind (kn,i) -> Ind (sh_kn kn,i)
  | Construct ((kn,i),j) -> Construct ((sh_kn kn,i),j)
  | Case (ci,p,c,bl) -> (* TO DO: extract ind_kn *)
      Case (ci, sh_rec p, sh_rec c, Array.map sh_rec bl)
  | Fix (ln,(lna,tl,bl)) ->
      Fix (ln,(Array.map sh_na lna,
                 Array.map sh_rec tl,
                 Array.map sh_rec bl))
  | CoFix(ln,(lna,tl,bl)) ->
      CoFix (ln,(Array.map sh_na lna,
                   Array.map sh_rec tl,
                   Array.map sh_rec bl))

module Hconstr =
  Hashcons.Make(
    struct
      type t = constr
      type u = (constr -> constr) *
               ((sorts -> sorts) * (constant -> constant) *
               (mutual_inductive -> mutual_inductive) * (name -> name) *
               (identifier -> identifier))
      let hash_sub = hash_term
      let equal = comp_term
      let hash = Hashtbl.hash
    end)

let hcons_term (hsorts,hcon,hkn,hname,hident) =
  Hashcons.recursive_hcons Hconstr.f (hsorts,hcon,hkn,hname,hident)

(* Constructs a DeBrujin index with number n *)
let rels =
  [|Rel  1;Rel  2;Rel  3;Rel  4;Rel  5;Rel  6;Rel  7; Rel  8;
    Rel  9;Rel 10;Rel 11;Rel 12;Rel 13;Rel 14;Rel 15; Rel 16|]

let mkRel n = if 0<n & n<=16 then rels.(n-1) else Rel n

(* Constructs an existential variable named "?n" *)
let mkMeta  n =  Meta n

(* Constructs a Variable named id *)
let mkVar id = Var id

(* Construct a type *)
let mkSort s = Sort s

(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1)
   [s] is the strategy to use when *)
let mkCast (t1,k2,t2) =
  match t1 with
  | Cast (c,k1, _) when k1 = k2 -> Cast (c,k1,t2)
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
  if Array.length a = 0 then f else
    match f with
      | App (g, cl) -> App (g, Array.append cl a)
      | _ -> App (f, a)


(* Constructs a constant *)
(* The array of terms correspond to the variables introduced in the section *)
let mkConst c = Const c

(* Constructs an existential variable *)
let mkEvar e = Evar e

(* Constructs the ith (co)inductive type of the block named kn *)
(* The array of terms correspond to the variables introduced in the section *)
let mkInd m = Ind m

(* Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. The array of terms correspond to the variables
   introduced in the section *)
let mkConstruct c = Construct c

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkCase (ci, p, c, ac) = Case (ci, p, c, ac)

let mkFix fix = Fix fix

let mkCoFix cofix = CoFix cofix

let kind_of_term c = c
let kind_of_term2 c = c

(************************************************************************)
(*    kind_of_term = constructions as seen by the user                 *)
(************************************************************************)

(* User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

let kind_of_term = kind_of_term

(**********************************************************************)
(*          Non primitive term destructors                            *)
(**********************************************************************)

(* Destructor operations : partial functions
   Raise invalid_arg "dest*" if the const has not the expected form *)

(* Destructs a DeBrujin index *)
let destRel c = match kind_of_term c with
  | Rel n -> n
  | _ -> invalid_arg "destRel"

(* Destructs an existential variable *)
let destMeta c = match kind_of_term c with
  | Meta n -> n
  | _ -> invalid_arg "destMeta"

let isMeta c = match kind_of_term c with Meta _ -> true | _ -> false

(* Destructs a variable *)
let destVar c = match kind_of_term c with
  | Var id -> id
  | _ -> invalid_arg "destVar"

(* Destructs a type *)
let isSort c = match kind_of_term c with
  | Sort s -> true
  | _ -> false

let destSort c = match kind_of_term c with
  | Sort s -> s
  | _ -> invalid_arg "destSort"

let rec isprop c = match kind_of_term c with
  | Sort (Prop _) -> true
  | Cast (c,_,_) -> isprop c
  | _ -> false

let rec is_Prop c = match kind_of_term c with
  | Sort (Prop Null) -> true
  | Cast (c,_,_) -> is_Prop c
  | _ -> false

let rec is_Set c = match kind_of_term c with
  | Sort (Prop Pos) -> true
  | Cast (c,_,_) -> is_Set c
  | _ -> false

let rec is_Type c = match kind_of_term c with
  | Sort (Type _) -> true
  | Cast (c,_,_) -> is_Type c
  | _ -> false

let is_small = function
  | Prop _ -> true
  | _ -> false

let iskind c = isprop c or is_Type c

(* Tests if an evar *)
let isEvar c = match kind_of_term c with Evar _ -> true | _ -> false

let isEvar_or_Meta c = match kind_of_term c with
  | Evar _ | Meta _ -> true
  | _ -> false

(* Destructs a casted term *)
let destCast c = match kind_of_term c with
  | Cast (t1,k,t2) -> (t1,k,t2)
  | _ -> invalid_arg "destCast"

let isCast c = match kind_of_term c with Cast _ -> true | _ -> false


(* Tests if a de Bruijn index *)
let isRel c = match kind_of_term c with Rel _ -> true | _ -> false

(* Tests if a variable *)
let isVar c = match kind_of_term c with Var _ -> true | _ -> false

(* Tests if an inductive *)
let isInd c = match kind_of_term c with Ind _ -> true | _ -> false

(* Destructs the product (x:t1)t2 *)
let destProd c = match kind_of_term c with
  | Prod (x,t1,t2) -> (x,t1,t2)
  | _ -> invalid_arg "destProd"

let isProd c = match kind_of_term c with | Prod _ -> true | _ -> false

(* Destructs the abstraction [x:t1]t2 *)
let destLambda c = match kind_of_term c with
  | Lambda (x,t1,t2) -> (x,t1,t2)
  | _ -> invalid_arg "destLambda"

let isLambda c = match kind_of_term c with | Lambda _ -> true | _ -> false

(* Destructs the let [x:=b:t1]t2 *)
let destLetIn c = match kind_of_term c with
  | LetIn (x,b,t1,t2) -> (x,b,t1,t2)
  | _ -> invalid_arg "destProd"

let isLetIn c =  match kind_of_term c with LetIn _ -> true | _ -> false

(* Destructs an application *)
let destApp c = match kind_of_term c with
  | App (f,a) -> (f, a)
  | _ -> invalid_arg "destApplication"

let destApplication = destApp

let isApp c = match kind_of_term c with App _ -> true | _ -> false

(* Destructs a constant *)
let destConst c = match kind_of_term c with
  | Const kn -> kn
  | _ -> invalid_arg "destConst"

let isConst c = match kind_of_term c with Const _ -> true | _ -> false

(* Destructs an existential variable *)
let destEvar c = match kind_of_term c with
  | Evar (kn, a as r) -> r
  | _ -> invalid_arg "destEvar"

(* Destructs a (co)inductive type named kn *)
let destInd c = match kind_of_term c with
  | Ind (kn, a as r) -> r
  | _ -> invalid_arg "destInd"

(* Destructs a constructor *)
let destConstruct c = match kind_of_term c with
  | Construct (kn, a as r) -> r
  | _ -> invalid_arg "dest"

let isConstruct c = match kind_of_term c with Construct _ -> true | _ -> false

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
let destCase c = match kind_of_term c with
  | Case (ci,p,c,v) -> (ci,p,c,v)
  | _ -> anomaly "destCase"

let isCase c =  match kind_of_term c with Case _ -> true | _ -> false

let destFix c = match kind_of_term c with
  | Fix fix -> fix
  | _ -> invalid_arg "destFix"

let isFix c =  match kind_of_term c with Fix _ -> true | _ -> false

let destCoFix c = match kind_of_term c with
  | CoFix cofix -> cofix
  | _ -> invalid_arg "destCoFix"

let isCoFix c =  match kind_of_term c with CoFix _ -> true | _ -> false

(******************************************************************)
(* Cast management                                                *)
(******************************************************************)

let rec strip_outer_cast c = match kind_of_term c with
  | Cast (c,_,_) -> strip_outer_cast c
  | _ -> c

(* Fonction spéciale qui laisse les cast clés sous les Fix ou les Case *)

let under_outer_cast f c =  match kind_of_term c with
  | Cast (b,k,t) -> mkCast (f b, k, f t)
  | _ -> f c

let rec under_casts f c = match kind_of_term c with
  | Cast (c,k,t) -> mkCast (under_casts f c, k, t)
  | _            -> f c

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

(* flattens application lists throwing casts in-between *)
let rec collapse_appl c = match kind_of_term c with
  | App (f,cl) ->
      let rec collapse_rec f cl2 =
        match kind_of_term (strip_outer_cast f) with
	| App (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
	| _ -> mkApp (f,cl2)
      in
      collapse_rec f cl
  | _ -> c

let decompose_app c =
  match kind_of_term c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])

(****************************************************************************)
(*              Functions to recur through subterms                         *)
(****************************************************************************)

(* [fold_constr f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

let fold_constr f acc c = match kind_of_term c with
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
      let fd = array_map3 (fun na t b -> (na,t,b)) lna tl bl in
      Array.fold_left (fun acc (na,t,b) -> f (f acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let fd = array_map3 (fun na t b -> (na,t,b)) lna tl bl in
      Array.fold_left (fun acc (na,t,b) -> f (f acc t) b) acc fd

(* [iter_constr f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let iter_constr f c = match kind_of_term c with
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

(* [iter_constr_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_constr_with_binders g f n c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (_,t,c) -> f n t; f (g n) c
  | Lambda (_,t,c) -> f n t; f (g n) c
  | LetIn (_,b,t,c) -> f n b; f n t; f (g n) c
  | App (c,l) -> f n c; Array.iter (f n) l
  | Evar (_,l) -> Array.iter (f n) l
  | Case (_,p,c,bl) -> f n p; f n c; Array.iter (f n) bl
  | Fix (_,(_,tl,bl)) ->
      Array.iter (f n) tl;
      Array.iter (f (iterate g (Array.length tl) n)) bl
  | CoFix (_,(_,tl,bl)) ->
      Array.iter (f n) tl;
      Array.iter (f (iterate g (Array.length tl) n)) bl

(* [map_constr f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let map_constr f c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,k,t) -> mkCast (f c, k, f t)
  | Prod (na,t,c) -> mkProd (na, f t, f c)
  | Lambda (na,t,c) -> mkLambda (na, f t, f c)
  | LetIn (na,b,t,c) -> mkLetIn (na, f b, f t, f c)
  | App (c,l) -> mkApp (f c, Array.map f l)
  | Evar (e,l) -> mkEvar (e, Array.map f l)
  | Case (ci,p,c,bl) -> mkCase (ci, f p, f c, Array.map f bl)
  | Fix (ln,(lna,tl,bl)) ->
      mkFix (ln,(lna,Array.map f tl,Array.map f bl))
  | CoFix(ln,(lna,tl,bl)) ->
      mkCoFix (ln,(lna,Array.map f tl,Array.map f bl))

(* [map_constr_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let map_constr_with_binders g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,k,t) -> mkCast (f l c, k, f l t)
  | Prod (na,t,c) -> mkProd (na, f l t, f (g l) c)
  | Lambda (na,t,c) -> mkLambda (na, f l t, f (g l) c)
  | LetIn (na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g l) c)
  | App (c,al) -> mkApp (f l c, Array.map (f l) al)
  | Evar (e,al) -> mkEvar (e, Array.map (f l) al)
  | Case (ci,p,c,bl) -> mkCase (ci, f l p, f l c, Array.map (f l) bl)
  | Fix (ln,(lna,tl,bl)) ->
      let l' = iterate g (Array.length tl) l in
      mkFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | CoFix(ln,(lna,tl,bl)) ->
      let l' = iterate g (Array.length tl) l in
      mkCoFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))

(* [compare_constr f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account *)


let compare_constr f t1 t2 =
  match kind_of_term t1, kind_of_term t2 with
  | Rel n1, Rel n2 -> n1 = n2
  | Meta m1, Meta m2 -> m1 = m2
  | Var id1, Var id2 -> id1 = id2
  | Sort s1, Sort s2 -> s1 = s2
  | Cast (c1,_,_), _ -> f c1 t2
  | _, Cast (c2,_,_) -> f t1 c2
  | Prod (_,t1,c1), Prod (_,t2,c2) -> f t1 t2 & f c1 c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) -> f t1 t2 & f c1 c2
  | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> f b1 b2 & f t1 t2 & f c1 c2
  | App (c1,l1), App (c2,l2) ->
      if Array.length l1 = Array.length l2 then
        f c1 c2 & array_for_all2 f l1 l2
      else
        let (h1,l1) = decompose_app t1 in
        let (h2,l2) = decompose_app t2 in
        if List.length l1 = List.length l2 then
          f h1 h2 & List.for_all2 f l1 l2
        else false
  | Evar (e1,l1), Evar (e2,l2) -> e1 = e2 & array_for_all2 f l1 l2
  | Const c1, Const c2 -> eq_constant c1 c2
  | Ind c1, Ind c2 -> eq_ind c1 c2
  | Construct c1, Construct c2 -> eq_constructor c1 c2
  | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
      f p1 p2 & f c1 c2 & array_for_all2 f bl1 bl2
  | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
      ln1 = ln2 & array_for_all2 f tl1 tl2 & array_for_all2 f bl1 bl2
  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      ln1 = ln2 & array_for_all2 f tl1 tl2 & array_for_all2 f bl1 bl2
  | _ -> false

(***************************************************************************)
(*     Type of assumptions                                                 *)
(***************************************************************************)

type types = constr

type strategy = types option

type named_declaration = identifier * constr option * types
type rel_declaration = name * constr option * types

let map_named_declaration f (id, v, ty) = (id, Option.map f v, f ty)
let map_rel_declaration = map_named_declaration

let fold_named_declaration f (_, v, ty) a = f ty (Option.fold_right f v a)
let fold_rel_declaration = fold_named_declaration

(***************************************************************************)
(*     Type of local contexts (telescopes)                                 *)
(***************************************************************************)

(*s Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices (to represent bound variables) *)

type rel_context = rel_declaration list

let empty_rel_context = []

let add_rel_decl d ctxt = d::ctxt

let rec lookup_rel n sign =
  match n, sign with
  | 1, decl :: _ -> decl
  | n, _ :: sign -> lookup_rel (n-1) sign
  | _, []        -> raise Not_found

let rel_context_length = List.length

let rel_context_nhyps hyps =
  let rec nhyps acc = function
    | [] -> acc
    | (_,None,_)::hyps -> nhyps (1+acc) hyps
    | (_,Some _,_)::hyps -> nhyps acc hyps in
  nhyps 0 hyps

(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(*********************)
(*     Occurring     *)
(*********************)

exception LocalOccur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn n c =
  let rec closed_rec n c = match kind_of_term c with
    | Rel m -> if m>n then raise LocalOccur
    | _ -> iter_constr_with_binders succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)

let closed0 = closedn 0

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term =
  let rec occur_rec n c = match kind_of_term c with
    | Rel m -> if m = n then raise LocalOccur
    | _ -> iter_constr_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M
  for n <= p < n+m *)

let noccur_between n m term =
  let rec occur_rec n c = match kind_of_term c with
    | Rel(p) -> if n<=p && p<n+m then raise LocalOccur
    | _        -> iter_constr_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* Checking function for terms containing existential variables.
 The function [noccur_with_meta] considers the fact that
 each existential variable (as well as each isevar)
 in the term appears applied to its local context,
 which may contain the CoFix variables. These occurrences of CoFix variables
 are not considered *)

let noccur_with_meta n m term =
  let rec occur_rec n c = match kind_of_term c with
    | Rel p -> if n<=p & p<n+m then raise LocalOccur
    | App(f,cl) ->
	(match kind_of_term f with
           | Cast (c,_,_) when isMeta c -> ()
           | Meta _ -> ()
	   | _ -> iter_constr_with_binders succ occur_rec n c)
    | Evar (_, _) -> ()
    | _ -> iter_constr_with_binders succ occur_rec n c
  in
  try (occur_rec n term; true) with LocalOccur -> false


(*********************)
(*      Lifting      *)
(*********************)

(* The generic lifting function *)
let rec exliftn el c = match kind_of_term c with
  | Rel i -> mkRel(reloc_rel i el)
  | _ -> map_constr_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn k n =
  match el_liftn (pred n) (el_shft k ELID) with
    | ELID -> (fun c -> c)
    | el -> exliftn el

let lift k = liftn k 1

(*********************)
(*   Substituting    *)
(*********************)

(* (subst1 M c) substitutes M for Rel(1) in c
   we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
   M1,...,Mn for respectively Rel(1),...,Rel(n) in c *)

(* 1st : general case *)

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo: info; sit: 'a }

let rec lift_substituend depth s =
  match s.sinfo with
    | Closed -> s.sit
    | Open -> lift depth s.sit
    | Unknown ->
        s.sinfo <- if closed0 s.sit then Closed else Open;
        lift_substituend depth s

let make_substituend c = { sinfo=Unknown; sit=c }

let substn_many lamv n c =
  let lv = Array.length lamv in
  if lv = 0 then c
  else
    let rec substrec depth c = match kind_of_term c with
      | Rel k     ->
          if k<=depth then c
          else if k-depth <= lv then lift_substituend depth lamv.(k-depth-1)
          else mkRel (k-lv)
      | _ -> map_constr_with_binders succ substrec depth c in
    substrec n c

(*
let substkey = Profile.declare_profile "substn_many";;
let substn_many lamv n c = Profile.profile3 substkey substn_many lamv n c;;
*)

let substnl laml n =
  substn_many (Array.map make_substituend (Array.of_list laml)) n
let substl laml = substnl laml 0
let subst1 lam = substl [lam]

let substnl_decl laml k (id,bodyopt,typ) =
  (id,Option.map (substnl laml k) bodyopt,substnl laml k typ)
let substl_decl laml = substnl_decl laml 0
let subst1_decl lam = substl_decl [lam]
let subst1_named_decl = subst1_decl
let substl_named_decl = substl_decl

(* (thin_val sigma) removes identity substitutions from sigma *)

let rec thin_val = function
  | [] -> []
  | (((id,{ sit = v }) as s)::tl) when isVar v ->
      if id = destVar v then thin_val tl else s::(thin_val tl)
  | h::tl -> h::(thin_val tl)

(* (replace_vars sigma M) applies substitution sigma to term M *)
let replace_vars var_alist =
  let var_alist =
    List.map (fun (str,c) -> (str,make_substituend c)) var_alist in
  let var_alist = thin_val var_alist in
  let rec substrec n c = match kind_of_term c with
    | Var x ->
        (try lift_substituend n (List.assoc x var_alist)
         with Not_found -> c)
    | _ -> map_constr_with_binders succ substrec n c
  in
  if var_alist = [] then (function x -> x) else substrec 0

(*
let repvarkey = Profile.declare_profile "replace_vars";;
let replace_vars vl c = Profile.profile2 repvarkey replace_vars vl c ;;
*)

(* (subst_var str t) substitute (VAR str) by (Rel 1) in t *)
let subst_var str = replace_vars [(str, mkRel 1)]

(* (subst_vars [id1;...;idn] t) substitute (VAR idj) by (Rel j) in t *)
let substn_vars p vars =
  let _,subst =
    List.fold_left (fun (n,l) var -> ((n+1),(var,mkRel n)::l)) (p,[]) vars
  in replace_vars (List.rev subst)

let subst_vars = substn_vars 1

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a DeBrujin index with number n *)
let mkRel = mkRel

(* Constructs an existential variable named "?n" *)
let mkMeta = mkMeta

(* Constructs a Variable named id *)
let mkVar = mkVar

(* Construct a type *)
let mkProp   = mkSort prop_sort
let mkSet    = mkSort set_sort
let mkType u = mkSort (Type u)
let mkSort   = function
  | Prop Null -> mkProp (* Easy sharing *)
  | Prop Pos -> mkSet
  | s -> mkSort s

(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
let mkCast = mkCast

(* Constructs the product (x:t1)t2 *)
let mkProd = mkProd
let mkNamedProd id typ c = mkProd (Name id, typ, subst_var id c)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda = mkLambda
let mkNamedLambda id typ c = mkLambda (Name id, typ, subst_var id c)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn = mkLetIn
let mkNamedLetIn id c1 t c2 = mkLetIn (Name id, c1, t, subst_var id c2)

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
let mkProd_or_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

let mkNamedProd_or_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedProd id t c
    | Some b -> mkNamedLetIn id b t c

(* Constructs either [[x:t]c] or [[x=b:t]c] *)
let mkLambda_or_LetIn (na,body,t) c =
  match body with
    | None -> mkLambda (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

let mkNamedLambda_or_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedLambda id t c
    | Some b -> mkNamedLetIn id b t c

(* Constructs either [(x:t)c] or [c] where [x] is replaced by [b] *)
let mkNamedProd_wo_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedProd id t c
    | Some b -> subst1 b (subst_var id c)

(* non-dependent product t1 -> t2 *)
let mkArrow t1 t2 = mkProd (Anonymous, t1, t2)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
(* We ensure applicative terms have at most one arguments and the
   function is not itself an applicative term *)
let mkApp = mkApp

(* Constructs a constant *)
(* The array of terms correspond to the variables introduced in the section *)
let mkConst = mkConst

(* Constructs an existential variable *)
let mkEvar = mkEvar

(* Constructs the ith (co)inductive type of the block named kn *)
(* The array of terms correspond to the variables introduced in the section *)
let mkInd = mkInd

(* Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. The array of terms correspond to the variables
   introduced in the section *)
let mkConstruct = mkConstruct

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkCase = mkCase

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

   where the lenght of the jth context is ij.
*)

let mkFix = mkFix

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
let mkCoFix = mkCoFix

(* Construct an implicit *)
let implicit_sort = Type (make_univ(make_dirpath[id_of_string"implicit"],0))
let mkImplicit = mkSort implicit_sort

(***************************)
(* Other term constructors *)
(***************************)

let abs_implicit c = mkLambda (Anonymous, mkImplicit, c)
let lambda_implicit a = mkLambda (Name(id_of_string"y"), mkImplicit, a)
let lambda_implicit_lift n a = iterate lambda_implicit n (lift n a)

(* prodn n [xn:Tn;..;x1:T1;Gamma] b = (x1:T1)..(xn:Tn)b *)
let prodn n env b =
  let rec prodrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> prodrec (n-1,  l, mkProd (v,t,b))
    | _ -> assert false
  in
  prodrec (n,env,b)

(* compose_prod [xn:Tn;..;x1:T1] b = (x1:T1)..(xn:Tn)b *)
let compose_prod l b = prodn (List.length l) l b

(* lamn n [xn:Tn;..;x1:T1;Gamma] b = [x1:T1]..[xn:Tn]b *)
let lamn n env b =
  let rec lamrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> lamrec (n-1,  l, mkLambda (v,t,b))
    | _ -> assert false
  in
  lamrec (n,env,b)

(* compose_lam [xn:Tn;..;x1:T1] b = [x1:T1]..[xn:Tn]b *)
let compose_lam l b = lamn (List.length l) l b

let applist (f,l) = mkApp (f, Array.of_list l)

let applistc f l = mkApp (f, Array.of_list l)

let appvect = mkApp

let appvectc f l = mkApp (f,l)

(* to_lambda n (x1:T1)...(xn:Tn)T =
 * [x1:T1]...[xn:Tn]T *)
let rec to_lambda n prod =
  if n = 0 then
    prod
  else
    match kind_of_term prod with
      | Prod (na,ty,bd) -> mkLambda (na,ty,to_lambda (n-1) bd)
      | Cast (c,_,_) -> to_lambda n c
      | _   -> errorlabstrm "to_lambda" (mt ())

let rec to_prod n lam =
  if n=0 then
    lam
  else
    match kind_of_term lam with
      | Lambda (na,ty,bd) -> mkProd (na,ty,to_prod (n-1) bd)
      | Cast (c,_,_) -> to_prod n c
      | _   -> errorlabstrm "to_prod" (mt ())

(* pseudo-reduction rule:
 * [prod_app  s (Prod(_,B)) N --> B[N]
 * with an strip_outer_cast on the first argument to produce a product *)

let prod_app t n =
  match kind_of_term (strip_outer_cast t) with
    | Prod (_,_,b) -> subst1 n b
    | _ ->
	errorlabstrm "prod_app"
	  (str"Needed a product, but didn't find one" ++ fnl ())


(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_appvect t nL = Array.fold_left prod_app t nL

(* prod_applist T [ a1 ; ... ; an ] -> (T a1 ... an) *)
let prod_applist t nL = List.fold_left prod_app t nL

let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)
let it_mkLambda_or_LetIn = List.fold_left (fun c d -> mkLambda_or_LetIn d c)

(*********************************)
(* Other term destructors        *)
(*********************************)

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod =
  let rec prodec_rec l c = match kind_of_term c with
    | Prod (x,t,c) -> prodec_rec ((x,t)::l) c
    | Cast (c,_,_)   -> prodec_rec l c
    | _              -> l,c
  in
  prodec_rec []

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam =
  let rec lamdec_rec l c = match kind_of_term c with
    | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | Cast (c,_,_)     -> lamdec_rec l c
    | _                -> l,c
  in
  lamdec_rec []

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n n =
  if n < 0 then error "decompose_prod_n: integer parameter must be positive";
  let rec prodec_rec l n c =
    if n=0 then l,c
    else match kind_of_term c with
      | Prod (x,t,c) -> prodec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_)   -> prodec_rec l n c
      | _ -> error "decompose_prod_n: not enough products"
  in
  prodec_rec [] n

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n n =
  if n < 0 then error "decompose_lam_n: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if n=0 then l,c
    else match kind_of_term c with
      | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_)     -> lamdec_rec l n c
      | _ -> error "decompose_lam_n: not enough abstractions"
  in
  lamdec_rec [] n

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod_assum =
  let rec prodec_rec l c =
    match kind_of_term c with
    | Prod (x,t,c)    -> prodec_rec (add_rel_decl (x,None,t) l) c
    | LetIn (x,b,t,c) -> prodec_rec (add_rel_decl (x,Some b,t) l) c
    | Cast (c,_,_)      -> prodec_rec l c
    | _               -> l,c
  in
  prodec_rec empty_rel_context

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam_assum =
  let rec lamdec_rec l c =
    match kind_of_term c with
    | Lambda (x,t,c)  -> lamdec_rec (add_rel_decl (x,None,t) l) c
    | LetIn (x,b,t,c) -> lamdec_rec (add_rel_decl (x,Some b,t) l) c
    | Cast (c,_,_)      -> lamdec_rec l c
    | _               -> l,c
  in
  lamdec_rec empty_rel_context

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n_assum n =
  if n < 0 then
    error "decompose_prod_n_assum: integer parameter must be positive";
  let rec prodec_rec l n c =
    if n=0 then l,c
    else match kind_of_term c with
    | Prod (x,t,c)    -> prodec_rec (add_rel_decl (x,None,t) l) (n-1) c
    | LetIn (x,b,t,c) -> prodec_rec (add_rel_decl (x,Some b,t) l) (n-1) c
    | Cast (c,_,_)      -> prodec_rec l n c
    | c -> error "decompose_prod_n_assum: not enough assumptions"
  in
  prodec_rec empty_rel_context n

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T
   into the pair ([(xn,Tn);...;(x1,T1)],T)
   Lets in between are not expanded but turn into local definitions,
   but n is the actual number of destructurated lambdas.  *)
let decompose_lam_n_assum n =
  if n < 0 then
    error "decompose_lam_n_assum: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if n=0 then l,c
    else match kind_of_term c with
    | Lambda (x,t,c)  -> lamdec_rec (add_rel_decl (x,None,t) l) (n-1) c
    | LetIn (x,b,t,c) -> lamdec_rec (add_rel_decl (x,Some b,t) l) n c
    | Cast (c,_,_)      -> lamdec_rec l n c
    | c -> error "decompose_lam_n_assum: not enough abstractions"
  in
  lamdec_rec empty_rel_context n

(* (nb_lam [na1:T1]...[nan:Tan]c) where c is not an abstraction
 * gives n (casts are ignored) *)
let nb_lam =
  let rec nbrec n c = match kind_of_term c with
    | Lambda (_,_,c) -> nbrec (n+1) c
    | Cast (c,_,_) -> nbrec n c
    | _ -> n
  in
  nbrec 0

(* similar to nb_lam, but gives the number of products instead *)
let nb_prod =
  let rec nbrec n c = match kind_of_term c with
    | Prod (_,_,c) -> nbrec (n+1) c
    | Cast (c,_,_) -> nbrec n c
    | _ -> n
  in
  nbrec 0

let prod_assum t = fst (decompose_prod_assum t)
let prod_n_assum n t = fst (decompose_prod_n_assum n t)
let strip_prod_assum t = snd (decompose_prod_assum t)
let strip_prod t = snd (decompose_prod t)
let strip_prod_n n t = snd (decompose_prod_n n t)
let lam_assum t = fst (decompose_lam_assum t)
let lam_n_assum n t = fst (decompose_lam_n_assum n t)
let strip_lam_assum t = snd (decompose_lam_assum t)
let strip_lam t = snd (decompose_lam t)
let strip_lam_n n t = snd (decompose_lam_n n t)

(***************************)
(* Arities                 *)
(***************************)

(* An "arity" is a term of the form [[x1:T1]...[xn:Tn]s] with [s] a sort.
   Such a term can canonically be seen as the pair of a context of types
   and of a sort *)

type arity = rel_context * sorts

let destArity =
  let rec prodec_rec l c =
    match kind_of_term c with
    | Prod (x,t,c)    -> prodec_rec ((x,None,t)::l) c
    | LetIn (x,b,t,c) -> prodec_rec ((x,Some b,t)::l) c
    | Cast (c,_,_)      -> prodec_rec l c
    | Sort s          -> l,s
    | _               -> anomaly "destArity: not an arity"
  in
  prodec_rec []

let mkArity (sign,s) = it_mkProd_or_LetIn (mkSort s) sign

let rec isArity c =
  match kind_of_term c with
  | Prod (_,_,c)    -> isArity c
  | LetIn (_,b,_,c) -> isArity (subst1 b c)
  | Cast (c,_,_)      -> isArity c
  | Sort _          -> true
  | _               -> false

(*******************************)
(*  alpha conversion functions *)
(*******************************)

(* alpha conversion : ignore print names and casts *)

let rec eq_constr m n =
  (m==n) or
  compare_constr eq_constr m n

let eq_constr m n = eq_constr m n (* to avoid tracing a recursive fun *)

(*******************)
(*  hash-consing   *)
(*******************)

module Htype =
  Hashcons.Make(
    struct
      type t = types
      type u = (constr -> constr) * (sorts -> sorts)
(*
      let hash_sub (hc,hs) j = {body=hc j.body; typ=hs j.typ}
      let equal j1 j2 = j1.body==j2.body & j1.typ==j2.typ
*)
(**)
      let hash_sub (hc,hs) j = hc j
      let equal j1 j2 = j1==j2
(**)
      let hash = Hashtbl.hash
    end)

module Hsorts =
  Hashcons.Make(
    struct
      type t = sorts
      type u = universe -> universe
      let hash_sub huniv = function
          Prop c -> Prop c
        | Type u -> Type (huniv u)
      let equal s1 s2 =
        match (s1,s2) with
            (Prop c1, Prop c2) -> c1=c2
          | (Type u1, Type u2) -> u1 == u2
          |_ -> false
      let hash = Hashtbl.hash
    end)

let hsort = Hsorts.f

let hcons_constr (hcon,hkn,hdir,hname,hident,hstr) =
  let hsortscci = Hashcons.simple_hcons hsort hcons1_univ in
  let hcci = hcons_term (hsortscci,hcon,hkn,hname,hident) in
  let htcci = Hashcons.simple_hcons Htype.f (hcci,hsortscci) in
  (hcci,htcci)

let (hcons1_constr, hcons1_types) = hcons_constr (hcons_names())


(*******)
(* Type of abstract machine values *)
type values
