(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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
open Univ
open Context
open Stages
open SVars
open Stage
open Annot
open Constraints

type existential_key = Evar.t
type metavariable = int

(* This defines the strategy to use for verifiying a Cast *)
(* Warning: REVERTcast is not exported to vo-files; as of r14492, it has to *)
(* come after the vo-exported cast_kind so as to be compatible with coqchk *)
type cast_kind = VMcast | NATIVEcast | DEFAULTcast | REVERTcast

(* This defines Cases annotations *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle
type case_printing =
  { ind_tags : bool list; (** tell whether letin or lambda in the arity of the inductive type *)
    cstr_tags : bool list array; (* whether each pattern var of each constructor is a let-in (true) or not (false) *)
    style     : case_style }

(* INVARIANT:
 * - Array.length ci_cstr_ndecls = Array.length ci_cstr_nargs
 * - forall (i : 0 .. pred (Array.length ci_cstr_ndecls)),
 *          ci_cstr_ndecls.(i) >= ci_cstr_nargs.(i)
 *)
type case_info =
  { ci_ind        : inductive;      (* inductive type to which belongs the value that is being matched *)
    ci_npar       : int;            (* number of parameters of the above inductive type *)
    ci_cstr_ndecls : int array;     (* For each constructor, the corresponding integer determines
                                       the number of values that can be bound in a match-construct.
                                       NOTE: parameters of the inductive type are therefore excluded from the count *)
    ci_cstr_nargs : int array;      (* for each constructor, the corresponding integers determines
                                       the number of values that can be applied to the constructor,
                                       in addition to the parameters of the related inductive type
                                       NOTE: "lets" are therefore excluded from the count
                                       NOTE: parameters of the inductive type are also excluded from the count *)
    ci_relevance : Sorts.relevance;
    ci_pp_info    : case_printing   (* not interpreted by the kernel *)
  }

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr list
type ('constr, 'types) prec_declaration =
    Name.t binder_annot array * 'types array * 'constr array
type ('constr, 'types) pfixpoint =
    (int option array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pfixpoint_nopt =
    (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration
type 'a puniverses = 'a Univ.puniverses
type pconstant = Constant.t puniverses
type pinductive = inductive puniverses
type pconstructor = constructor puniverses

(* [Var] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)
type ('constr, 'types, 'sort, 'univs) kind_of_term =
  | Rel       of int * Annot.t list option
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of 'sort
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t binder_annot * 'types * 'types
  | Lambda    of Name.t binder_annot * 'types * 'constr
  | LetIn     of Name.t binder_annot * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of (Constant.t * 'univs) * Annot.t list option
  | Ind       of (inductive * 'univs) * Annot.t
  | Construct of (constructor * 'univs)
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | Proj      of Projection.t * 'constr
  | Int       of Uint63.t
  | Float     of Float64.t
(* constr is the fixpoint of the previous type. Requires option
   -rectypes of the Caml compiler to be set *)
type t = (t, t, Sorts.t, Instance.t) kind_of_term
type constr = t

type existential = existential_key * constr list

type types = constr

type rec_declaration = (constr, types) prec_declaration
type fixpoint = (constr, types) pfixpoint
type fixpoint_nopt = (constr, types) pfixpoint_nopt
type cofixpoint = (constr, types) pcofixpoint

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a de Bruijn index with number n *)
let rels =
  let mkRel n = Rel (n, None) in
  [|mkRel  1;mkRel  2;mkRel  3;mkRel  4;mkRel  5;mkRel  6;mkRel  7;mkRel  8;
    mkRel  9;mkRel 10;mkRel 11;mkRel 12;mkRel 13;mkRel 14;mkRel 15;mkRel 16|]

let mkRel n = if 0<n && n<=16 then rels.(n-1) else Rel (n, None)
let mkRelA n ans = Rel (n, ans)

(* Construct a type *)
let mkSProp  = Sort Sorts.sprop
let mkProp   = Sort Sorts.prop
let mkSet    = Sort Sorts.set
let mkType u = Sort (Sorts.sort_of_univ u)
let mkSort   = function
  | Sorts.SProp -> mkSProp
  | Sorts.Prop -> mkProp (* Easy sharing *)
  | Sorts.Set -> mkSet
  | Sorts.Type _ as s -> Sort s

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

let map_puniverses f (x,u) = (f x, u)
let in_punivs a = (a, Univ.Instance.empty)

(* Constructs a constant *)
let mkConst c = Const ((in_punivs c), None)
let mkConstU c = Const (c, None)
let mkConstUA c ans = Const (c, ans)

(* Constructs an applied projection *)
let mkProj (p,c) = Proj (p,c)

(* Constructs an existential variable *)
let mkEvar e = Evar e

(* Constructs the ith (co)inductive type of the block named kn *)
let mkInd m = Ind ((in_punivs m), Empty)
let mkIndU m = Ind (m, Empty)
let mkIndUS m stg = Ind (m, stg)

(* Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. *)
let mkConstruct c = Construct (in_punivs c)
let mkConstructU c = Construct c
let mkConstructUi ((ind,u),i) = Construct ((ind,i),u)

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
let mkFixOpt ((vn, i), rec_decl) =
  mkFix ((Array.map (fun i -> Some i) vn, i), rec_decl)

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

let mkRef (gr,u) = let open GlobRef in match gr with
  | ConstRef c -> mkConstU (c,u)
  | IndRef ind -> mkIndU (ind,u)
  | ConstructRef c -> mkConstructU (c,u)
  | VarRef x -> mkVar x

(* Constructs a primitive integer *)
let mkInt i = Int i

(* Constructs a primitive float number *)
let mkFloat f = Float f

(************************************************************************)
(*    kind_of_term = constructions as seen by the user                 *)
(************************************************************************)

(* User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

let kind (c:t) = c

let rec kind_nocast_gen kind c =
  match kind c with
  | Cast (c, _, _) -> kind_nocast_gen kind c
  | App (h, outer) as k ->
    (match kind_nocast_gen kind h with
     | App (h, inner) -> App (h, Array.append inner outer)
     | _ -> k)
  | k -> k

let kind_nocast c = kind_nocast_gen kind c

(* The other way around. We treat specifically smart constructors *)
let of_kind = function
| App (f, a) -> mkApp (f, a)
| Cast (c, knd, t) -> mkCast (c, knd, t)
| k -> k

(**********************************************************************)
(*          Non primitive term destructors                            *)
(**********************************************************************)

(* Destructor operations : partial functions
   Raise [DestKO] if the const has not the expected form *)

exception DestKO

let isMeta c = match kind c with Meta _ -> true | _ -> false

(* Destructs a type *)
let isSort c = match kind c with
  | Sort _ -> true
  | _ -> false

let rec isprop c = match kind c with
  | Sort (Sorts.Prop | Sorts.Set) -> true
  | Cast (c,_,_) -> isprop c
  | _ -> false

let rec is_Prop c = match kind c with
  | Sort Sorts.Prop -> true
  | Cast (c,_,_) -> is_Prop c
  | _ -> false

let rec is_Set c = match kind c with
  | Sort Sorts.Set -> true
  | Cast (c,_,_) -> is_Set c
  | _ -> false

let rec is_Type c = match kind c with
  | Sort (Sorts.Type _) -> true
  | Cast (c,_,_) -> is_Type c
  | _ -> false

let is_small = Sorts.is_small
let iskind c = isprop c || is_Type c

(* Tests if an evar *)
let isEvar c = match kind c with Evar _ -> true | _ -> false
let isEvar_or_Meta c = match kind c with
  | Evar _ | Meta _ -> true
  | _ -> false

let isCast c = match kind c with Cast _ -> true | _ -> false
(* Tests if a de Bruijn index *)
let isRel c = match kind c with Rel _ -> true | _ -> false
let isRelN n c =
  match kind c with Rel (n', _) -> Int.equal n n' | _ -> false
(* Tests if a variable *)
let isVar c = match kind c with Var _ -> true | _ -> false
let isVarId id c = match kind c with Var id' -> Id.equal id id' | _ -> false
(* Tests if an inductive *)
let isInd c = match kind c with Ind _ -> true | _ -> false
let isProd c = match kind c with | Prod _ -> true | _ -> false
let isLambda c = match kind c with | Lambda _ -> true | _ -> false
let isLetIn c =  match kind c with LetIn _ -> true | _ -> false
let isApp c = match kind c with App _ -> true | _ -> false
let isConst c = match kind c with Const _ -> true | _ -> false
let isConstruct c = match kind c with Construct _ -> true | _ -> false
let isCase c =  match kind c with Case _ -> true | _ -> false
let isProj c =  match kind c with Proj _ -> true | _ -> false
let isFix c =  match kind c with Fix _ -> true | _ -> false
let isCoFix c =  match kind c with CoFix _ -> true | _ -> false

let isRef c = match kind c with
  | Const _ | Ind _ | Construct _ | Var _ -> true
  | _ -> false

let isRefX x c =
  let open GlobRef in
  match x, kind c with
  | ConstRef c, Const ((c', _), _) -> Constant.equal c c'
  | IndRef i, Ind ((i', _), _) -> eq_ind i i'
  | ConstructRef i, Construct (i', _) -> eq_constructor i i'
  | VarRef id, Var id' -> Id.equal id id'
  | _ -> false

(* Destructs a de Bruijn index *)
let destRel c = match kind c with
  | Rel (n, _) -> n
  | _ -> raise DestKO

(* Destructs an existential variable *)
let destMeta c = match kind c with
  | Meta n -> n
  | _ -> raise DestKO

(* Destructs a variable *)
let destVar c = match kind c with
  | Var id -> id
  | _ -> raise DestKO

let destSort c = match kind c with
  | Sort s -> s
  | _ -> raise DestKO

(* Destructs a casted term *)
let destCast c = match kind c with
  | Cast (t1,k,t2) -> (t1,k,t2)
  | _ -> raise DestKO

(* Destructs the product (x:t1)t2 *)
let destProd c = match kind c with
  | Prod (x,t1,t2) -> (x,t1,t2)
  | _ -> raise DestKO

(* Destructs the abstraction [x:t1]t2 *)
let destLambda c = match kind c with
  | Lambda (x,t1,t2) -> (x,t1,t2)
  | _ -> raise DestKO

(* Destructs the let [x:=b:t1]t2 *)
let destLetIn c = match kind c with
  | LetIn (x,b,t1,t2) -> (x,b,t1,t2)
  | _ -> raise DestKO

(* Destructs an application *)
let destApp c = match kind c with
  | App (f,a) -> (f, a)
  | _ -> raise DestKO

(* Destructs a constant *)
let destConst c = match kind c with
  | Const (kn, _) -> kn
  | _ -> raise DestKO

(* Destructs an existential variable *)
let destEvar c = match kind c with
  | Evar (_kn, _a as r) -> r
  | _ -> raise DestKO

(* Destructs a (co)inductive type named kn *)
let destInd c = match kind c with
  | Ind ((_kn, _a as r), _) -> r
  | _ -> raise DestKO

(* Destructs a constructor *)
let destConstruct c = match kind c with
  | Construct (_kn, _a as r) -> r
  | _ -> raise DestKO

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
let destCase c = match kind c with
  | Case (ci,p,c,v) -> (ci,p,c,v)
  | _ -> raise DestKO

let destProj c = match kind c with
  | Proj (p, c) -> (p, c)
  | _ -> raise DestKO

let destFix c = match kind c with
  | Fix fix -> fix
  | _ -> raise DestKO

let destCoFix c = match kind c with
  | CoFix cofix -> cofix
  | _ -> raise DestKO

let destRef c = let open GlobRef in match kind c with
  | Var x -> VarRef x, Univ.Instance.empty
  | Const ((c,u), _) -> ConstRef c, u
  | Ind ((ind,u), _) -> IndRef ind, u
  | Construct (c,u) -> ConstructRef c, u
  | _ -> raise DestKO

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

let decompose_app c =
  match kind c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])

let decompose_appvect c =
  match kind c with
    | App (f,cl) -> (f, cl)
    | _ -> (c,[||])

(****************************************************************************)
(*              Functions to recur through subterms                         *)
(****************************************************************************)

(* [fold f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

let fold f acc c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _) -> acc
  | Cast (c,_,t) -> f (f acc c) t
  | Prod (_,t,c) -> f (f acc t) c
  | Lambda (_,t,c) -> f (f acc t) c
  | LetIn (_,b,t,c) -> f (f (f acc b) t) c
  | App (c,l) -> Array.fold_left f (f acc c) l
  | Proj (_p,c) -> f acc c
  | Evar (_,l) -> List.fold_left f acc l
  | Case (_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
  | Fix (_,(_lna,tl,bl)) ->
    Array.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl
  | CoFix (_,(_lna,tl,bl)) ->
    Array.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl

(* [iter f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let iter f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _) -> ()
  | Cast (c,_,t) -> f c; f t
  | Prod (_,t,c) -> f t; f c
  | Lambda (_,t,c) -> f t; f c
  | LetIn (_,b,t,c) -> f b; f t; f c
  | App (c,l) -> f c; Array.iter f l
  | Proj (_p,c) -> f c
  | Evar (_,l) -> List.iter f l
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
    | Construct _ | Int _ | Float _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (_,t,c) -> f n t; f (g n) c
  | Lambda (_,t,c) -> f n t; f (g n) c
  | LetIn (_,b,t,c) -> f n b; f n t; f (g n) c
  | App (c,l) -> f n c; Array.Fun1.iter f n l
  | Evar (_,l) -> List.iter (fun c -> f n c) l
  | Case (_,p,c,bl) -> f n p; f n c; Array.Fun1.iter f n bl
  | Proj (_p,c) -> f n c
  | Fix (_,(_,tl,bl)) ->
      Array.Fun1.iter f n tl;
      Array.Fun1.iter f (iterate g (Array.length tl) n) bl
  | CoFix (_,(_,tl,bl)) ->
      Array.Fun1.iter f n tl;
      Array.Fun1.iter f (iterate g (Array.length tl) n) bl

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

let fold_constr_with_binders g f n acc c =
  match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _) -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (_na,t,c) -> f (g  n) (f n acc t) c
  | Lambda (_na,t,c) -> f (g  n) (f n acc t) c
  | LetIn (_na,b,t,c) -> f (g  n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (_p,c) -> f n acc c
  | Evar (_,l) -> List.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(_,tl,bl)) ->
      let n' = iterate g (Array.length tl) n in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(_,tl,bl)) ->
      let n' = iterate g (Array.length tl) n in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd

(* [map f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let rec map_under_context f n d =
  if n = 0 then f d else
  match kind d with
  | LetIn (na,b,t,c) ->
    let b' = f b in
    let t' = f t in
    let c' = map_under_context f (n-1) c in
    if b' == b && t' == t && c' == c then d
    else mkLetIn (na,b',t',c')
  | Lambda (na,t,b) ->
    let t' = f t in
    let b' = map_under_context f (n-1) b in
    if t' == t && b' == b then d
    else mkLambda (na,t',b')
  | _ -> CErrors.anomaly (Pp.str "Ill-formed context")

let map_branches f ci bl =
  let nl = Array.map List.length ci.ci_pp_info.cstr_tags in
  let bl' = Array.map2 (map_under_context f) nl bl in
  if Array.for_all2 (==) bl' bl then bl else bl'

let map_return_predicate f ci p =
  map_under_context f (List.length ci.ci_pp_info.ind_tags) p

let rec map_under_context_with_binders g f l n d =
  if n = 0 then f l d else
  match kind d with
  | LetIn (na,b,t,c) ->
      let b' = f l b in
      let t' = f l t in
      let c' = map_under_context_with_binders g f (g l) (n-1) c in
      if b' == b && t' == t && c' == c then d
      else mkLetIn (na,b',t',c')
  | Lambda (na,t,b) ->
      let t' = f l t in
      let b' = map_under_context_with_binders g f (g l) (n-1) b in
      if t' == t && b' == b then d
      else mkLambda (na,t',b')
  | _ -> CErrors.anomaly (Pp.str "Ill-formed context")

let map_branches_with_binders g f l ci bl =
  let tags = Array.map List.length ci.ci_pp_info.cstr_tags in
  let bl' = Array.map2 (map_under_context_with_binders g f l) tags bl in
  if Array.for_all2 (==) bl' bl then bl else bl'

let map_return_predicate_with_binders g f l ci p =
  map_under_context_with_binders g f l (List.length ci.ci_pp_info.ind_tags) p

let rec map_under_context_with_full_binders g f l n d =
  if n = 0 then f l d else
    match kind d with
    | LetIn (na,b,t,c) ->
       let b' = f l b in
       let t' = f l t in
       let c' = map_under_context_with_full_binders g f (g (Context.Rel.Declaration.LocalDef (na,b,t)) l) (n-1) c in
       if b' == b && t' == t && c' == c then d
       else mkLetIn (na,b',t',c')
    | Lambda (na,t,b) ->
       let t' = f l t in
       let b' = map_under_context_with_full_binders g f (g (Context.Rel.Declaration.LocalAssum (na,t)) l) (n-1) b in
       if t' == t && b' == b then d
       else mkLambda (na,t',b')
    | _ -> CErrors.anomaly (Pp.str "Ill-formed context")

let map_branches_with_full_binders g f l ci bl =
  let tags = Array.map List.length ci.ci_pp_info.cstr_tags in
  let bl' = Array.map2 (map_under_context_with_full_binders g f l) tags bl in
  if Array.for_all2 (==) bl' bl then bl else bl'

let map_return_predicate_with_full_binders g f l ci p =
  map_under_context_with_full_binders g f l (List.length ci.ci_pp_info.ind_tags) p

let map_gen userview f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _) -> c
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
      let l' = Array.Smart.map f l in
      if b'==b && l'==l then c
      else mkApp (b', l')
  | Proj (p,t) ->
      let t' = f t in
      if t' == t then c
      else mkProj (p, t')
  | Evar (e,l) ->
      let l' = List.Smart.map f l in
      if l'==l then c
      else mkEvar (e, l')
  | Case (ci,p,b,bl) when userview ->
      let b' = f b in
      let p' = map_return_predicate f ci p in
      let bl' = map_branches f ci bl in
      if b'==b && p'==p && bl'==bl then c
      else mkCase (ci, p', b', bl')
  | Case (ci,p,b,bl) ->
      let b' = f b in
      let p' = f p in
      let bl' = Array.Smart.map f bl in
      if b'==b && p'==p && bl'==bl then c
      else mkCase (ci, p', b', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.Smart.map f tl in
      let bl' = Array.Smart.map f bl in
      if tl'==tl && bl'==bl then c
      else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let tl' = Array.Smart.map f tl in
      let bl' = Array.Smart.map f bl in
      if tl'==tl && bl'==bl then c
      else mkCoFix (ln,(lna,tl',bl'))

let map_user_view = map_gen true
let map = map_gen false

(* Like {!map} but with an accumulator. *)

let fold_map f accu c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _) -> accu, c
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
      let accu, l' = Array.Smart.fold_left_map f accu l in
      if b'==b && l'==l then accu, c
      else accu, mkApp (b', l')
  | Proj (p,t) ->
      let accu, t' = f accu t in
      if t' == t then accu, c
      else accu, mkProj (p, t')
  | Evar (e,l) ->
    (* Doesn't matter, we should not hashcons evars anyways *)
      let accu, l' = List.fold_left_map f accu l in
      if l'==l then accu, c
      else accu, mkEvar (e, l')
  | Case (ci,p,b,bl) ->
      let accu, b' = f accu b in
      let accu, p' = f accu p in
      let accu, bl' = Array.Smart.fold_left_map f accu bl in
      if b'==b && p'==p && bl'==bl then accu, c
      else accu, mkCase (ci, p', b', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let accu, tl' = Array.Smart.fold_left_map f accu tl in
      let accu, bl' = Array.Smart.fold_left_map f accu bl in
      if tl'==tl && bl'==bl then accu, c
      else accu, mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let accu, tl' = Array.Smart.fold_left_map f accu tl in
      let accu, bl' = Array.Smart.fold_left_map f accu bl in
      if tl'==tl && bl'==bl then accu, c
      else accu, mkCoFix (ln,(lna,tl',bl'))

(* [map_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let map_with_binders g f l c0 = match kind c0 with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _) -> c0
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
    let al' = Array.Fun1.Smart.map f l al in
    if c' == c && al' == al then c0
    else mkApp (c', al')
  | Proj (p, t) ->
    let t' = f l t in
    if t' == t then c0
    else mkProj (p, t')
  | Evar (e, al) ->
    let al' = List.Smart.map (fun c -> f l c) al in
    if al' == al then c0
    else mkEvar (e, al')
  | Case (ci, p, c, bl) ->
    let p' = f l p in
    let c' = f l c in
    let bl' = Array.Fun1.Smart.map f l bl in
    if p' == p && c' == c && bl' == bl then c0
    else mkCase (ci, p', c', bl')
  | Fix (ln, (lna, tl, bl)) ->
    let tl' = Array.Fun1.Smart.map f l tl in
    let l' = iterate g (Array.length tl) l in
    let bl' = Array.Fun1.Smart.map f l' bl in
    if tl' == tl && bl' == bl then c0
    else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
    let tl' = Array.Fun1.Smart.map f l tl in
    let l' = iterate g (Array.length tl) l in
    let bl' = Array.Fun1.Smart.map f l' bl in
    mkCoFix (ln,(lna,tl',bl'))


(*********************)
(* Stage annotations *)
(*********************)

(** fold-type functions on stage annotations of constrs *)

let rec count_annots cstr =
  match cstr with
  | Ind _ -> 1
  | Rel (_, la) -> List.length (Option.default [] la)
  | Cast (c, _, _)
  | Lambda (_, _, c) ->
    count_annots c
  | LetIn (_, b, _, c) ->
    count_annots b + count_annots c
  | Const (_, la) -> List.length (Option.default [] la)
  | Case (_, _, c, lf) ->
    Array.fold_left (fun count c -> count + count_annots c) (count_annots c) lf
  | Fix (_, (_, _, bl))
  | CoFix (_, (_, _, bl)) ->
    Array.fold_left (fun count c -> count + count_annots c) 0 bl
  | _ ->
    fold (fun count c -> count + count_annots c) 0 cstr

let rec collect_annots c =
  match c with
  | Ind (_, Stage (StageVar (na, _))) -> SVars.add na SVars.empty
  | _ -> fold (fun vars c -> SVars.union vars (collect_annots c)) SVars.empty c

let rec any_annot f c =
  match c with
  | Ind (_, a) -> f a
  | _ -> fold (fun acc c -> acc || any_annot f c) false c

(** map-type functions on stage annotations of constrs *)

let rec map_annots f g cstr =
  match cstr with
  | Ind (iu, a) -> f iu a cstr
  | Rel _ -> g cstr
  | Cast (c, k, t) ->
    let c' = map_annots f g c in
    if c == c' then cstr else
    mkCast (c', k, t)
  | Lambda (n, t, c) ->
    let c' = map_annots f g c in
    if c == c' then cstr else
    mkLambda (n, t, c')
  | LetIn (n, b, t, c) ->
    let b' = map_annots f g b in
    let c' = map_annots f g c in
    if b == b' && c == c' then cstr else
    mkLetIn (n, b', t, c')
  | Const _ -> g cstr
  | Case (ci, p, c, lf) ->
    let c' = map_annots f g c in
    let lf' = Array.Smart.map (map_annots f g) lf in
    if c == c' && lf == lf' then cstr else
    mkCase (ci, p, c', lf')
  | Fix (ln, (nl, tl, bl)) ->
    let bl' = Array.Smart.map (map_annots f g) bl in
    if bl == bl' then cstr else
    mkFix (ln, (nl, tl, bl'))
  | CoFix (ln, (nl, tl, bl)) ->
    let bl' = Array.Smart.map (map_annots f g) bl in
    if bl == bl' then cstr else
    mkCoFix (ln, (nl, tl, bl'))
  | _ -> map (map_annots f g) cstr

let make_annots_list annot la =
  List.make (List.length la) annot

let map_annots_list g cstr =
  match cstr with
  | Rel (n, Some la) ->
    let la = g la in
    mkRelA n (Some la)
  | Const (c, Some la) ->
    let la = g la in
    mkConstUA c (Some la)
  | _ -> cstr

let erase =
  let f iu a c =
    match a with
    | Empty -> c
    | _ -> mkIndUS iu Empty in
  map_annots f (map_annots_list (make_annots_list Empty))

let erase_infty =
  let f iu a c =
    match a with
    | Stage Infty -> c
    | _ -> mkIndUS iu infty in
  map_annots f (map_annots_list (make_annots_list infty))

let erase_glob vars =
  let f iu a c =
    match a with
    | Stage (StageVar (na, _))
      when mem na vars ->
      mkIndUS iu Glob
    | Stage Infty -> c
    | _ -> mkIndUS iu infty in
  map_annots f (map_annots_list (make_annots_list Empty))

let erase_star vars =
  let f iu a c =
    match a with
    | Stage (StageVar (na, _))
      when SVars.mem na vars ->
      mkIndUS iu Star
    | Empty -> c
    | _ -> mkIndUS iu Empty in
  map_annots f (map_annots_list (make_annots_list Empty))

let annotate ind s =
  let f (((i, _), _) as iu) _ c =
    if MutInd.equal ind i then
      mkIndUS iu s
    else c in
  map_annots f identity

let annotate_fresh annots =
  let annots_ref = ref annots in
  let f iu _ _ =
    let annots = !annots_ref in
    annots_ref := List.tl annots;
    mkIndUS iu (List.hd annots) in
  let g la =
    let annots = !annots_ref in
    let la, annots = List.chop (List.length la) annots in
    annots_ref := annots; la in
  map_annots f (map_annots_list g)

let annotate_glob s =
  let f iu a c =
    match a with
    | Glob -> mkIndUS iu s
    | _ -> c in
  map_annots f identity

let annotate_succ vars =
  let f iu a c =
    match a with
    | Stage (StageVar (na, _))
      when mem na vars ->
      mkIndUS iu (hat a)
    | _ -> c in
  map_annots f identity

(*********************)
(*      Lifting      *)
(*********************)

(* The generic lifting function *)
let rec exliftn el c =
  let open Esubst in
  match kind c with
  | Rel (i, ans) -> mkRelA (reloc_rel i el) ans
  | _ -> map_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn n k c =
  let open Esubst in
  match el_liftn (pred k) (el_shft n el_id) with
    | ELID -> c
    | el -> exliftn el c

let lift n = liftn n 1

let fold_with_full_binders g f n acc c =
  let open Context.Rel.Declaration in
  match kind c with
  | Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _  | Int _ | Float _ -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | Lambda (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g (LocalDef (na,b,t)) n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (_,c) -> f n acc c
  | Evar (_,l) -> List.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd


type 'univs instance_compare_fn = GlobRef.t -> int ->
  'univs -> 'univs -> bool

type 'constr constr_compare_fn = int -> 'constr -> 'constr -> bool

let compare_head_gen_leq_with_cstrnts kind1 kind2 leq_universes leq_sorts leq_annot eq leq nargs t1 t2 =
  match kind_nocast_gen kind1 t1, kind_nocast_gen kind2 t2 with
  | Cast _, _ | _, Cast _ -> assert false (* kind_nocast *)
  | Rel (n1, _), Rel (n2, _) -> Int.equal n1 n2
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Int i1, Int i2 -> Uint63.equal i1 i2
  | Float f1, Float f2 -> Float64.equal f1 f2
  | Sort s1, Sort s2 -> leq_sorts s1 s2
  | Prod (_,t1,c1), Prod (_,t2,c2) -> eq 0 t1 t2 && leq 0 c1 c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) -> eq 0 t1 t2 && eq 0 c1 c2
  | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> eq 0 b1 b2 && eq 0 t1 t2 && leq nargs c1 c2
  (* Why do we suddenly make a special case for Cast here? *)
  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    Int.equal len (Array.length l2) &&
    leq (nargs+len) c1 c2 && Array.equal_norefl (eq 0) l1 l2
  | Proj (p1,c1), Proj (p2,c2) -> Projection.equal p1 p2 && eq 0 c1 c2
  | Evar (e1,l1), Evar (e2,l2) -> Evar.equal e1 e2 && List.equal (eq 0) l1 l2
  | Const ((c1,u1), _), Const ((c2,u2), _) ->
    (* The args length currently isn't used but may as well pass it. *)
    Constant.equal c1 c2 && leq_universes (GlobRef.ConstRef c1) nargs u1 u2
  | Ind ((c1,u1), s1), Ind ((c2,u2), s2) ->
    eq_ind c1 c2 && leq_universes (GlobRef.IndRef c1) nargs u1 u2 && leq_annot c1 s1 s2
  | Construct (c1,u1), Construct (c2,u2) ->
    eq_constructor c1 c2 && leq_universes (GlobRef.ConstructRef c1) nargs u1 u2
  | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
    eq 0 p1 p2 && eq 0 c1 c2 && Array.equal (eq 0) bl1 bl2
  | Fix ((lon1, i1),(_,tl1,bl1)), Fix ((lon2, i2),(_,tl2,bl2)) ->
    Int.equal i1 i2 && Array.equal (Option.equal Int.equal) lon1 lon2
    && Array.equal_norefl (eq 0) tl1 tl2 && Array.equal_norefl (eq 0) bl1 bl2
  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
    Int.equal ln1 ln2 && Array.equal_norefl (eq 0) tl1 tl2 && Array.equal_norefl (eq 0) bl1 bl2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _), _ -> false

(* [compare_head_gen_leq_with k1 k2 u s e eq leq c1 c2] compare [c1] and
   [c2] (using [k1] to expose the structure of [c1] and [k2] to expose
   the structure [c2]) using [eq] to compare the immediate subterms of
   [c1] of [c2] for conversion if needed, [leq] for cumulativity, [u]
   to compare universe instances, and [s] to compare sorts; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account. Note that as [kind1] and [kind2] are
   potentially different, we cannot use, in recursive case, the
   optimisation that physically equal arrays are equals (hence the
   calls to {!Array.equal_norefl}). *)

let compare_head_gen_leq_with kind1 kind2 leq_universes leq_sorts eq leq nargs t1 t2 =
  compare_head_gen_leq_with_cstrnts kind1 kind2 leq_universes leq_sorts (fun _ _ _ -> true) eq leq nargs t1 t2

(* [compare_head_gen_leq u s eq leq c1 c2] compare [c1] and [c2] using [eq] to compare
   the immediate subterms of [c1] of [c2] for conversion if needed, [leq] for cumulativity,
   [u] to compare universe instances and [s] to compare sorts; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account *)

let compare_head_gen_leq leq_universes leq_sorts eq leq nargs t1 t2 =
  compare_head_gen_leq_with kind kind leq_universes leq_sorts eq leq nargs t1 t2

let compare_head_gen_leq_cstrnts leq_universes leq_sorts leq_annot eq leq nargs t1 t2 =
  compare_head_gen_leq_with_cstrnts kind kind leq_universes leq_sorts leq_annot eq leq nargs t1 t2

(* [compare_head_gen u s f c1 c2] compare [c1] and [c2] using [f] to
   compare the immediate subterms of [c1] of [c2] if needed, [u] to
   compare universe instances and [s] to compare sorts; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account.

   [compare_head_gen_with] is a variant taking kind-of-term functions,
   to expose subterms of [c1] and [c2], as arguments. *)

let compare_head_gen_with kind1 kind2 eq_universes eq_sorts eq nargs t1 t2 =
  compare_head_gen_leq_with kind1 kind2 eq_universes eq_sorts eq eq nargs t1 t2

let compare_head_gen_cstrnts eq_universes eq_sorts eq_annot eq nargs t1 t2 =
  compare_head_gen_leq_cstrnts eq_universes eq_sorts eq_annot eq eq nargs t1 t2

let compare_head_gen eq_universes eq_sorts eq nargs t1 t2 =
  compare_head_gen_leq eq_universes eq_sorts eq eq nargs t1 t2

let compare_head = compare_head_gen (fun _ _ -> Univ.Instance.equal) Sorts.equal

(*******************************)
(*  alpha conversion functions *)
(*******************************)

type compare_annot = Constraints.t ref -> Names.inductive -> Annot.t -> Annot.t -> bool

(* alpha conversion : ignore print names and casts *)

let rec eq_constr nargs m n =
  (m == n) || compare_head_gen (fun _ _ -> Instance.equal) Sorts.equal eq_constr nargs m n

let equal n m = eq_constr 0 m n (* to avoid tracing a recursive fun *)

let eq_constr_univs eq_annot leq_annot univs m n =
  if m == n then true, empty ()
  else
    let cstrnts = ref (empty ()) in
    let eq_universes _ _ = UGraph.check_eq_instances univs in
    let eq_sorts s1 s2 = s1 == s2 || UGraph.check_eq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2) in
    let rec eq_constr' nargs m n =
      m == n ||	compare_head_gen_cstrnts eq_universes eq_sorts (eq_annot cstrnts) eq_constr' nargs m n in
    let rec leq_constr' nargs m n =
      m == n || compare_head_gen_leq_cstrnts eq_universes eq_sorts (leq_annot cstrnts) eq_constr' leq_constr' nargs m n in
    let res = leq_constr' 0 m n in
    res, !cstrnts

let leq_constr_univs eq_annot leq_annot univs m n =
  if m == n then true, empty ()
  else
    let cstrnts = ref (empty ()) in
    let eq_universes _ _ = UGraph.check_eq_instances univs in
    let eq_sorts s1 s2 = s1 == s2 ||
      UGraph.check_eq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2) in
    let leq_sorts s1 s2 = s1 == s2 ||
      UGraph.check_leq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2) in
    let rec eq_constr' nargs m n =
      m == n || compare_head_gen_cstrnts eq_universes eq_sorts (eq_annot cstrnts) eq_constr' nargs m n
    in
    let rec compare_leq nargs m n =
      compare_head_gen_leq_cstrnts eq_universes leq_sorts (leq_annot cstrnts) eq_constr' leq_constr' nargs m n
    and leq_constr' nargs m n = m == n || compare_leq nargs m n in
    let res = compare_leq 0 m n in
    res, !cstrnts

let eq_constr_univs_infer univs m n =
  if m == n then true, Constraint.empty
  else
    let cstrs = ref Constraint.empty in
    let eq_universes _ _ = UGraph.check_eq_instances univs in
    let eq_sorts s1 s2 =
      if Sorts.equal s1 s2 then true
      else
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        if UGraph.check_eq univs u1 u2 then true
        else
          (cstrs := Univ.enforce_eq u1 u2 !cstrs;
           true)
    in
    let rec eq_constr' nargs m n =
      m == n || compare_head_gen eq_universes eq_sorts eq_constr' nargs m n
    in
    let res = compare_head_gen eq_universes eq_sorts eq_constr' 0 m n in
    res, !cstrs

let leq_constr_univs_infer univs m n =
  if m == n then true, Constraint.empty
  else
    let cstrs = ref Constraint.empty in
    let eq_universes _ _ l l' = UGraph.check_eq_instances univs l l' in
    let eq_sorts s1 s2 =
      if Sorts.equal s1 s2 then true
      else
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        if UGraph.check_eq univs u1 u2 then true
        else (cstrs := Univ.enforce_eq u1 u2 !cstrs;
              true)
    in
    let leq_sorts s1 s2 =
      if Sorts.equal s1 s2 then true
      else
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        if UGraph.check_leq univs u1 u2 then true
        else
          (try let c, _ = UGraph.enforce_leq_alg u1 u2 univs in
            cstrs := Univ.Constraint.union c !cstrs;
            true
          with Univ.UniverseInconsistency _ -> false)
    in
    let rec eq_constr' nargs m n =
      m == n || compare_head_gen eq_universes eq_sorts eq_constr' nargs m n
    in
    let rec compare_leq nargs m n =
      compare_head_gen_leq eq_universes leq_sorts eq_constr' leq_constr' nargs m n
    and leq_constr' nargs m n = m == n || compare_leq nargs m n in
    let res = compare_leq 0 m n in
    res, !cstrs

let rec eq_constr_nounivs m n =
  (m == n) || compare_head_gen (fun _ _ _ _ -> true) (fun _ _ -> true) (fun _ -> eq_constr_nounivs) 0 m n

let constr_ord_int f t1 t2 =
  let (=?) f g i1 i2 j1 j2=
    let c = f i1 i2 in
    if Int.equal c 0 then g j1 j2 else c in
  let (==?) fg h i1 i2 j1 j2 k1 k2=
    let c=fg i1 i2 j1 j2 in
    if Int.equal c 0 then h k1 k2 else c in
  let fix_cmp (a1, i1) (a2, i2) =
    ((Array.compare (Option.compare Int.compare)) =? Int.compare) a1 a2 i1 i2
  in
  match kind t1, kind t2 with
    | Cast (c1,_,_), _ -> f c1 t2
    | _, Cast (c2,_,_) -> f t1 c2
    (* Why this special case? *)
    | App (Cast(c1,_,_),l1), _ -> f (mkApp (c1,l1)) t2
    | _, App (Cast(c2, _,_),l2) -> f t1 (mkApp (c2,l2))
    | Rel (n1, _), Rel (n2, _) -> Int.compare n1 n2
    | Rel _, _ -> -1 | _, Rel _ -> 1
    | Var id1, Var id2 -> Id.compare id1 id2
    | Var _, _ -> -1 | _, Var _ -> 1
    | Meta m1, Meta m2 -> Int.compare m1 m2
    | Meta _, _ -> -1 | _, Meta _ -> 1
    | Evar (e1,l1), Evar (e2,l2) ->
        (Evar.compare =? (List.compare f)) e1 e2 l1 l2
    | Evar _, _ -> -1 | _, Evar _ -> 1
    | Sort s1, Sort s2 -> Sorts.compare s1 s2
    | Sort _, _ -> -1 | _, Sort _ -> 1
    | Prod (_,t1,c1), Prod (_,t2,c2)
    | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
        (f =? f) t1 t2 c1 c2
    | Prod _, _ -> -1 | _, Prod _ -> 1
    | Lambda _, _ -> -1 | _, Lambda _ -> 1
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) ->
        ((f =? f) ==? f) b1 b2 t1 t2 c1 c2
    | LetIn _, _ -> -1 | _, LetIn _ -> 1
    | App (c1,l1), App (c2,l2) -> (f =? (Array.compare f)) c1 c2 l1 l2
    | App _, _ -> -1 | _, App _ -> 1
    | Const ((c1,_u1), _), Const ((c2,_u2), _) -> Constant.CanOrd.compare c1 c2
    | Const _, _ -> -1 | _, Const _ -> 1
    | Ind ((ind1, _u1), _), Ind ((ind2, _u2), _) -> ind_ord ind1 ind2
    | Ind _, _ -> -1 | _, Ind _ -> 1
    | Construct (ct1,_u1), Construct (ct2,_u2) -> constructor_ord ct1 ct2
    | Construct _, _ -> -1 | _, Construct _ -> 1
    | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
        ((f =? f) ==? (Array.compare f)) p1 p2 c1 c2 bl1 bl2
    | Case _, _ -> -1 | _, Case _ -> 1
    | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
        ((fix_cmp =? (Array.compare f)) ==? (Array.compare f))
        ln1 ln2 tl1 tl2 bl1 bl2
    | Fix _, _ -> -1 | _, Fix _ -> 1
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
        ((Int.compare =? (Array.compare f)) ==? (Array.compare f))
        ln1 ln2 tl1 tl2 bl1 bl2
    | CoFix _, _ -> -1 | _, CoFix _ -> 1
    | Proj (p1,c1), Proj (p2,c2) -> (Projection.compare =? f) p1 p2 c1 c2
    | Proj _, _ -> -1 | _, Proj _ -> 1
    | Int i1, Int i2 -> Uint63.compare i1 i2
    | Int _, _ -> -1 | _, Int _ -> 1
    | Float f1, Float f2 -> Float64.total_compare f1 f2

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
    | Rel (n1, ans1), Rel (n2, ans2) -> n1 == n2 && ans1 == ans2
    | Meta m1, Meta m2 -> m1 == m2
    | Var id1, Var id2 -> id1 == id2
    | Sort s1, Sort s2 -> s1 == s2
    | Cast (c1,k1,t1), Cast (c2,k2,t2) -> c1 == c2 && k1 == k2 && t1 == t2
    | Prod (n1,t1,c1), Prod (n2,t2,c2) -> n1 == n2 && t1 == t2 && c1 == c2
    | Lambda (n1,t1,c1), Lambda (n2,t2,c2) -> n1 == n2 && t1 == t2 && c1 == c2
    | LetIn (n1,b1,t1,c1), LetIn (n2,b2,t2,c2) ->
      n1 == n2 && b1 == b2 && t1 == t2 && c1 == c2
    | App (c1,l1), App (c2,l2) -> c1 == c2 && array_eqeq l1 l2
    | Proj (p1,c1), Proj(p2,c2) -> p1 == p2 && c1 == c2
    | Evar (e1,l1), Evar (e2,l2) -> e1 == e2 && List.equal l1 l2
    | Const ((c1,u1), ans1), Const ((c2,u2), ans2) -> c1 == c2 && u1 == u2 && ans1 == ans2
    | Ind ((ind1,u1), stg1), Ind ((ind2,u2), stg2) -> ind1 == ind2 && u1 == u2 && stg1 == stg2
    | Construct (cstr1,u1), Construct (cstr2,u2) -> cstr1 == cstr2 && u1 == u2
    | Case (ci1,p1,c1,bl1), Case (ci2,p2,c2,bl2) ->
      ci1 == ci2 && p1 == p2 && c1 == c2 && array_eqeq bl1 bl2
    | Fix ((lon1, i1),(lna1,tl1,bl1)), Fix ((lon2, i2),(lna2,tl2,bl2)) ->
      Int.equal i1 i2
      && Array.equal (Option.equal Int.equal) lon1 lon2
      && array_eqeq lna1 lna2
      && array_eqeq tl1 tl2
      && array_eqeq bl1 bl2
    | CoFix(ln1,(lna1,tl1,bl1)), CoFix(ln2,(lna2,tl2,bl2)) ->
      Int.equal ln1 ln2
      && array_eqeq lna1 lna2
      && array_eqeq tl1 tl2
      && array_eqeq bl1 bl2
    | Int i1, Int i2 -> i1 == i2
    | Float f1, Float f2 -> Float64.equal f1 f2
    | (Rel _ | Meta _ | Var _ | Sort _ | Cast _ | Prod _ | Lambda _ | LetIn _
      | App _ | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _
      | Fix _ | CoFix _ | Int _ | Float _), _ -> false

(** Note that the following Make has the side effect of creating
    once and for all the table we'll use for hash-consing all constr *)

module HashsetTerm =
  Hashset.Make(struct type t = constr let eq = hasheq end)

module HashsetTermArray =
  Hashset.Make(struct type t = constr array let eq = array_eqeq end)

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

let sh_instance = Univ.Instance.share

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
        (Prod (sh_na na, t, c), combinesmall 4 (combine3 (hash_annot Name.hash na) ht hc))
      | Lambda (na,t,c) ->
        let t, ht = sh_rec t
        and c, hc = sh_rec c in
        (Lambda (sh_na na, t, c), combinesmall 5 (combine3 (hash_annot Name.hash na) ht hc))
      | LetIn (na,b,t,c) ->
        let b, hb = sh_rec b in
        let t, ht = sh_rec t in
        let c, hc = sh_rec c in
        (LetIn (sh_na na, b, t, c), combinesmall 6 (combine4 (hash_annot Name.hash na) hb ht hc))
      | App (c,l) ->
        let c, hc = sh_rec c in
        let l, hl = hash_term_array l in
        (App (c,l), combinesmall 7 (combine hl hc))
      | Evar (e,l) ->
        let l, hl = hash_list_array l in
        (Evar (e,l), combinesmall 8 (combine (Evar.hash e) hl))
      | Const ((c,u), ans) ->
        let c' = sh_con c in
        let u', hu = sh_instance u in
        (Const ((c', u'), ans), combinesmall 9 (combine (Constant.SyntacticOrd.hash c) hu))
      | Ind ((ind,u), stg) ->
        let u', hu = sh_instance u in
        (Ind ((sh_ind ind, u'), stg),
         combinesmall 10 (combine3 (ind_syntactic_hash ind) hu (Annot.hash stg)))
      | Construct (c,u) ->
        let u', hu = sh_instance u in
        (Construct (sh_construct c, u'),
         combinesmall 11 (combine (constructor_syntactic_hash c) hu))
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
        let fold accu na = combine (hash_annot Name.hash na) accu in
        let hna = Array.fold_left fold 0 lna in
        let h = combine3 hna hbl htl in
        (Fix (ln,(lna,tl,bl)), combinesmall 13 h)
      | CoFix(ln,(lna,tl,bl)) ->
        let bl,hbl = hash_term_array bl in
        let tl,htl = hash_term_array tl in
        let () = Array.iteri (fun i x -> Array.unsafe_set lna i (sh_na x)) lna in
        let fold accu na = combine (hash_annot Name.hash na) accu in
        let hna = Array.fold_left fold 0 lna in
        let h = combine3 hna hbl htl in
        (CoFix (ln,(lna,tl,bl)), combinesmall 14 h)
      | Meta n ->
        (t, combinesmall 15 n)
      | Rel (n, _) ->
        (t, combinesmall 16 n)
      | Proj (p,c) ->
        let c, hc = sh_rec c in
        let p' = Projection.hcons p in
          (Proj (p', c), combinesmall 17 (combine (Projection.SyntacticOrd.hash p') hc))
      | Int i ->
        let (h,l) = Uint63.to_int2 i in
        (t, combinesmall 18 (combine h l))
      | Float f -> (t, combinesmall 19 (Float64.hash f))

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

  and hash_list_array l =
    let fold accu c =
      let c, h = sh_rec c in
      (combine accu h, c)
    in
    let h, l = List.fold_left_map fold 0 l in
    (l, h land 0x3FFFFFFF)

  in
  (* Make sure our statically allocated Rels (1 to 16) are considered
     as canonical, and hence hash-consed to themselves *)
  ignore (hash_term_array rels);

  fun t -> fst (sh_rec t)

(* Exported hashing fonction on constr, used mainly in plugins.
   Slight differences from [snd (hash_term t)] above: it ignores binders
   and doesn't do [land  0x3FFFFFFF]. *)

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
      combinesmall 8 (combine (Evar.hash e) (hash_term_list l))
    | Const ((c,u), _) ->
      combinesmall 9 (combine (Constant.hash c) (Instance.hash u))
    | Ind ((ind,u), stg) ->
      combinesmall 10 (combine3 (ind_hash ind) (Instance.hash u) (Annot.hash stg))
    | Construct (c,u) ->
      combinesmall 11 (combine (constructor_hash c) (Instance.hash u))
    | Case (_ , p, c, bl) ->
      combinesmall 12 (combine3 (hash c) (hash p) (hash_term_array bl))
    | Fix (_ln ,(_, tl, bl)) ->
      combinesmall 13 (combine (hash_term_array bl) (hash_term_array tl))
    | CoFix(_ln, (_, tl, bl)) ->
       combinesmall 14 (combine (hash_term_array bl) (hash_term_array tl))
    | Meta n -> combinesmall 15 n
    | Rel (n, _) -> combinesmall 16 n
    | Proj (p,c) ->
      combinesmall 17 (combine (Projection.hash p) (hash c))
    | Int i -> combinesmall 18 (Uint63.hash i)
    | Float f -> combinesmall 19 (Float64.hash f)

and hash_term_array t =
  Array.fold_left (fun acc t -> combine acc (hash t)) 0 t

and hash_term_list t =
  List.fold_left (fun acc t -> combine (hash t) acc) 0 t

module CaseinfoHash =
struct
  type t = case_info
  type u = inductive -> inductive
  let hashcons hind ci = { ci with ci_ind = hind ci.ci_ind }
  let pp_info_equal info1 info2 =
    List.equal (==) info1.ind_tags info2.ind_tags &&
    Array.equal (List.equal (==)) info1.cstr_tags info2.cstr_tags &&
    info1.style == info2.style
  let eq ci ci' =
    ci.ci_ind == ci'.ci_ind &&
    ci.ci_relevance == ci'.ci_relevance &&
    Int.equal ci.ci_npar ci'.ci_npar &&
    Array.equal Int.equal ci.ci_cstr_ndecls ci'.ci_cstr_ndecls && (* we use [Array.equal] on purpose *)
    Array.equal Int.equal ci.ci_cstr_nargs ci'.ci_cstr_nargs && (* we use [Array.equal] on purpose *)
    pp_info_equal ci.ci_pp_info ci'.ci_pp_info  (* we use (=) on purpose *)
  open Hashset.Combine
  let hash_bool b = if b then 0 else 1
  let hash_bool_list = List.fold_left (fun n b -> combine n (hash_bool b))
  let hash_pp_info info =
    let h1 = match info.style with
    | LetStyle -> 0
    | IfStyle -> 1
    | LetPatternStyle -> 2
    | MatchStyle -> 3
    | RegularStyle -> 4 in
    let h2 = hash_bool_list 0 info.ind_tags in
    let h3 = Array.fold_left hash_bool_list 0 info.cstr_tags in
    combine3 h1 h2 h3
  let hash ci =
    let h1 = ind_hash ci.ci_ind in
    let h2 = Int.hash ci.ci_npar in
    let h3 = Array.fold_left combine 0 ci.ci_cstr_ndecls in
    let h4 = Array.fold_left combine 0 ci.ci_cstr_nargs in
    let h5 = hash_pp_info ci.ci_pp_info in
    combinesmall (Sorts.relevance_hash ci.ci_relevance) (combine5 h1 h2 h3 h4 h5)
end

module Hcaseinfo = Hashcons.Make(CaseinfoHash)

let case_info_hash = CaseinfoHash.hash

let hcons_caseinfo = Hashcons.simple_hcons Hcaseinfo.generate Hcaseinfo.hcons hcons_ind

module Hannotinfo = struct
    type t = Name.t binder_annot
    type u = Name.t -> Name.t
    let hash = hash_annot Name.hash
    let eq = eq_annot (fun na1 na2 -> na1 == na2)
    let hashcons h {binder_name=na;binder_relevance} =
      {binder_name=h na;binder_relevance}
  end
module Hannot = Hashcons.Make(Hannotinfo)

let hcons_annot = Hashcons.simple_hcons Hannot.generate Hannot.hcons Name.hcons

let hcons =
  hashcons
    (Sorts.hcons,
     hcons_caseinfo,
     hcons_construct,
     hcons_ind,
     hcons_con,
     hcons_annot,
     Id.hcons)

(* let hcons_types = hcons_constr *)

type rel_declaration = (constr, types) Context.Rel.Declaration.pt
type named_declaration = (constr, types) Context.Named.Declaration.pt
type compacted_declaration = (constr, types) Context.Compacted.Declaration.pt
type rel_context = rel_declaration list
type named_context = named_declaration list
type compacted_context = compacted_declaration list

(** Minimalistic constr printer, typically for debugging *)

let debug_print_fix pr_constr ((t,i),(lna,tl,bl)) =
  let open Pp in
  let fixl = Array.mapi (fun i na -> (na.binder_name,t.(i),tl.(i),bl.(i))) lna in
  hov 1
      (str"fix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,io,ty,bd) ->
           Name.print na ++ str"/" ++ option int io ++ str":" ++ pr_constr ty ++
           cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")

let debug_print_annots ans =
  let open Pp in
  str "[" ++
  option (List.fold_left (fun s annot -> s ++ str ";" ++ Annot.pr annot) (str ";")) ans ++
  str "]"

let pr_puniverses p u =
  if Univ.Instance.is_empty u then p
  else Pp.(p ++ str"(*" ++ Univ.Instance.pr Univ.Level.pr u ++ str"*)")

let rec debug_print c =
  let open Pp in
  match kind c with
  | Rel (n, ans) -> str "#"++int n ++debug_print_annots ans
  | Meta n -> str "Meta(" ++ int n ++ str ")"
  | Var id -> Id.print id
  | Sort s -> Sorts.debug_print s
  | Cast (c,_, t) -> hov 1
      (str"(" ++ debug_print c ++ cut() ++
       str":" ++ debug_print t ++ str")")
  | Prod ({binder_name=Name id;_},t,c) -> hov 1
      (str"forall " ++ Id.print id ++ str":" ++ debug_print t ++ str"," ++
       spc() ++ debug_print c)
  | Prod ({binder_name=Anonymous;_},t,c) -> hov 0
      (str"(" ++ debug_print t ++ str " ->" ++ spc() ++
       debug_print c ++ str")")
  | Lambda (na,t,c) -> hov 1
      (str"fun " ++ Name.print na.binder_name ++ str":" ++
       debug_print t ++ str" =>" ++ spc() ++ debug_print c)
  | LetIn (na,b,t,c) -> hov 0
      (str"let " ++ Name.print na.binder_name ++ str":=" ++ debug_print b ++
       str":" ++ brk(1,2) ++ debug_print t ++ cut() ++
       debug_print c)
  | App (c,l) ->  hov 1
      (str"(" ++ debug_print c ++ spc() ++
       prlist_with_sep spc debug_print (Array.to_list l) ++ str")")
  | Evar (e,l) -> hov 1
      (str"Evar#" ++ int (Evar.repr e) ++ str"{" ++
       prlist_with_sep spc debug_print l ++str"}")
  | Const ((c,u), ans) -> str"Cst(" ++
      pr_puniverses (Constant.debug_print c) u ++
      debug_print_annots ans ++ str ")"
  | Ind (((sp,i),u), stg) -> str"Ind(" ++ pr_puniverses (MutInd.print sp ++ str"," ++ int i) u ++ str"," ++ Annot.pr stg ++ str")"
  | Construct (((sp,i),j),u) ->
      str"Constr(" ++ pr_puniverses (MutInd.print sp ++ str"," ++ int i ++ str"," ++ int j) u ++ str")"
  | Proj (p,c) -> str"Proj(" ++ Constant.debug_print (Projection.constant p) ++ str"," ++ bool (Projection.unfolded p) ++ debug_print c ++ str")"
  | Case (_ci,p,c,bl) -> v 0
      (hv 0 (str"<"++debug_print p++str">"++ cut() ++ str"Case " ++
             debug_print c ++ str"of") ++ cut() ++
       prlist_with_sep (fun _ -> brk(1,2)) debug_print (Array.to_list bl) ++
      cut() ++ str"end")
  | Fix f -> debug_print_fix debug_print f
  | CoFix(i,(lna,tl,bl)) ->
      let fixl = Array.mapi (fun i na -> (na,tl.(i),bl.(i))) lna in
      hov 1
        (str"cofix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,ty,bd) ->
           Name.print na.binder_name ++ str":" ++ debug_print ty ++
           cut() ++ str":=" ++ debug_print bd) (Array.to_list fixl)) ++
         str"}")
  | Int i -> str"Int("++str (Uint63.to_string i) ++ str")"
  | Float i -> str"Float("++str (Float64.to_string i) ++ str")"
