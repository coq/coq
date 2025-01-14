(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open UVars
open Context

type existential_key = Evar.t
type metavariable = int

(* This defines the strategy to use for verifiying a Cast *)
type cast_kind = VMcast | NATIVEcast | DEFAULTcast

(* This defines Cases annotations *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle
type case_printing =
  { style     : case_style }

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
    ci_pp_info    : case_printing   (* not interpreted by the kernel *)
  }

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr SList.t
type ('constr, 'types, 'r) prec_declaration =
    (Name.t,'r) pbinder_annot array * 'types array * 'constr array
type ('constr, 'types, 'r) pfixpoint =
    (int array * int) * ('constr, 'types, 'r) prec_declaration
type ('constr, 'types, 'r) pcofixpoint =
    int * ('constr, 'types, 'r) prec_declaration
type 'a puniverses = 'a UVars.puniverses
type pconstant = Constant.t puniverses
type pinductive = inductive puniverses
type pconstructor = constructor puniverses

type 'constr pcase_invert =
  | NoInvert
  | CaseInvert of { indices : 'constr array }

type ('constr,'r) pcase_branch = (Name.t,'r) Context.pbinder_annot array * 'constr
type ('types,'r) pcase_return = ((Name.t,'r) Context.pbinder_annot array * 'types) * 'r

type ('constr, 'types, 'univs, 'r) pcase =
  case_info * 'univs * 'constr array * ('types,'r) pcase_return * 'constr pcase_invert * 'constr * ('constr, 'r) pcase_branch array

(* [Var] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)
type ('constr, 'types, 'sort, 'univs, 'r) kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of 'sort
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of (Name.t,'r) pbinder_annot * 'types * 'types
  | Lambda    of (Name.t,'r) pbinder_annot * 'types * 'constr
  | LetIn     of (Name.t,'r) pbinder_annot * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of (Constant.t * 'univs)
  | Ind       of (inductive * 'univs)
  | Construct of (constructor * 'univs)
  | Case      of case_info * 'univs * 'constr array * ('types,'r) pcase_return * 'constr pcase_invert * 'constr * ('constr,'r) pcase_branch array
  | Fix       of ('constr, 'types, 'r) pfixpoint
  | CoFix     of ('constr, 'types, 'r) pcofixpoint
  | Proj      of Projection.t * 'r * 'constr
  | Int       of Uint63.t
  | Float     of Float64.t
  | String    of Pstring.t
  | Array     of 'univs * 'constr array * 'constr * 'types

(* constr is the fixpoint of the previous type. *)
type t = T of (t, t, Sorts.t, Instance.t, Sorts.relevance) kind_of_term [@@unboxed]
type constr = t
type types = constr

type existential = existential_key * constr SList.t

type case_invert = constr pcase_invert
type case_return = (types,Sorts.relevance) pcase_return
type case_branch = (constr,Sorts.relevance) pcase_branch
type case = (constr, types, Instance.t, Sorts.relevance) pcase
type rec_declaration = (constr, types, Sorts.relevance) prec_declaration
type fixpoint = (constr, types, Sorts.relevance) pfixpoint
type cofixpoint = (constr, types, Sorts.relevance) pcofixpoint
type 'a binder_annot = ('a,Sorts.relevance) Context.pbinder_annot

(************************************************************************)
(*    kind_of_term = constructions as seen by the user                 *)
(************************************************************************)

(* User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

let kind (T c) = c

let rec kind_nocast_gen kind c =
  match kind c with
  | Cast (c, _, _) -> kind_nocast_gen kind c
  | App (h, outer) as k ->
    (match kind_nocast_gen kind h with
     | App (h, inner) -> App (h, Array.append inner outer)
     | _ -> k)
  | k -> k

let kind_nocast c = kind_nocast_gen kind c

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
  match kind c with Rel n' -> Int.equal n n' | _ -> false
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
  | ConstRef c, Const (c', _) -> Constant.CanOrd.equal c c'
  | IndRef i, Ind (i', _) -> Ind.CanOrd.equal i i'
  | ConstructRef i, Construct (i', _) -> Construct.CanOrd.equal i i'
  | VarRef id, Var id' -> Id.equal id id'
  | _ -> false

(* Destructs a de Bruijn index *)
let destRel c = match kind c with
  | Rel n -> n
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
  | Const kn -> kn
  | _ -> raise DestKO

(* Destructs an existential variable *)
let destEvar c = match kind c with
  | Evar (_kn, _a as r) -> r
  | _ -> raise DestKO

(* Destructs a (co)inductive type named kn *)
let destInd c = match kind c with
  | Ind (_kn, _a as r) -> r
  | _ -> raise DestKO

(* Destructs a constructor *)
let destConstruct c = match kind c with
  | Construct (_kn, _a as r) -> r
  | _ -> raise DestKO

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
let destCase c = match kind c with
  | Case (ci,u,params,p,iv,c,v) -> (ci,u,params,p,iv,c,v)
  | _ -> raise DestKO

let destProj c = match kind c with
  | Proj (p, r, c) -> (p, r, c)
  | _ -> raise DestKO

let destFix c = match kind c with
  | Fix fix -> fix
  | _ -> raise DestKO

let destCoFix c = match kind c with
  | CoFix cofix -> cofix
  | _ -> raise DestKO

let destRef c = let open GlobRef in match kind c with
  | Var x -> VarRef x, UVars.Instance.empty
  | Const (c,u) -> ConstRef c, u
  | Ind (ind,u) -> IndRef ind, u
  | Construct (c,u) -> ConstructRef c, u
  | _ -> raise DestKO

let destArray c = match kind c with
  | Array (u,ar,def,ty) -> u,ar,def,ty
  | _ -> raise DestKO

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

let decompose_app_list c =
  match kind c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])

let decompose_app c =
  match kind c with
    | App (f,cl) -> (f, cl)
    | _ -> (c,[||])

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a de Bruijn index with number n *)
let rels = Array.init 17 (fun i -> T (Rel i))

let mkRel n = if 0<=n && n<=16 then rels.(n) else T (Rel n)

let mkSProp = T (Sort Sorts.sprop)
let mkProp  = T (Sort Sorts.prop)
let mkSet   = T (Sort Sorts.set)

(* Enforces:
   - applicative terms have at least one argument and the
     function is not itself an applicative term
   - stacks of VM or native casts are collapsed
   - small rels are shared
   - small sorts are shared
*)
let of_kind = function
| Rel n when 0 <= n && n < Array.length rels -> rels.(n)
| App (f, [||]) -> f
| App (f, a) as k -> begin match kind f with
    | App (g, cl) -> T (App (g, Array.append cl a))
    | _ -> T k
  end
| Cast (c, knd, t) as k -> begin match kind c with
    | Cast (c, knd', _) when (knd == VMcast || knd == NATIVEcast) && knd == knd' ->
      T (Cast (c, knd, t))
    | _ -> T k
  end
| Sort Sorts.SProp -> mkSProp
| Sort Sorts.Prop -> mkProp
| Sort Sorts.Set -> mkSet
| k -> T k

(* Construct a type *)
let mkType u = of_kind @@ Sort (Sorts.sort_of_univ u)
let mkSort s = of_kind @@ Sort s

(* Constructs the product (x:t1)t2 *)
let mkProd (x,t1,t2) = of_kind @@ Prod (x,t1,t2)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda (x,t1,t2) = of_kind @@ Lambda (x,t1,t2)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn (x,c1,t,c2) = of_kind @@ LetIn (x,c1,t,c2)

let mkApp (f, a) = of_kind (App (f, a))

(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
let mkCast (t1,k,t2) = of_kind @@ Cast (t1,k,t2)

let map_puniverses f (x,u) = (f x, u)
let in_punivs a = (a, UVars.Instance.empty)

(* Constructs a constant *)
let mkConst c = of_kind @@ Const (in_punivs c)
let mkConstU c = of_kind @@ Const c

(* Constructs an applied projection *)
let mkProj (p,r,c) = of_kind @@ Proj (p,r,c)

(* Constructs an existential variable *)
let mkEvar e = of_kind @@ Evar e

(* Constructs the ith (co)inductive type of the block named kn *)
let mkInd m = of_kind @@ Ind (in_punivs m)
let mkIndU m = of_kind @@ Ind m

(* Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. *)
let mkConstruct c = of_kind @@ Construct (in_punivs c)
let mkConstructU c = of_kind @@ Construct c
let mkConstructUi ((ind,u),i) = of_kind @@ Construct ((ind,i),u)

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkCase (ci, u, params, p, iv, c, ac) = of_kind @@ Case (ci, u, params, p, iv, c, ac)

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

let mkFix fix = of_kind @@ Fix fix

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
let mkCoFix cofix= of_kind @@ CoFix cofix

(* Constructs an existential variable named "?n" *)
let mkMeta  n = of_kind @@  Meta n

(* Constructs a Variable named id *)
let mkVar id = of_kind @@ Var id

let mkRef (gr,u) = let open GlobRef in match gr with
  | ConstRef c -> mkConstU (c,u)
  | IndRef ind -> mkIndU (ind,u)
  | ConstructRef c -> mkConstructU (c,u)
  | VarRef x -> mkVar x

(* Constructs a primitive integer *)
let mkInt i = of_kind @@ Int i

(* Constructs an array *)
let mkArray (u,t,def,ty) = of_kind @@ Array (u,t,def,ty)

(* Constructs a primitive float number *)
let mkFloat f = of_kind @@ Float f

(* Constructs a primitive string. *)
let mkString s = of_kind @@ String s

module UnsafeMonomorphic = struct
  let mkConst = mkConst
  let mkInd = mkInd
  let mkConstruct = mkConstruct
end

(****************************************************************************)
(*              Functions to recur through subterms                         *)
(****************************************************************************)

(* [fold f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

let fold_invert f acc = function
  | NoInvert -> acc
  | CaseInvert {indices} ->
    Array.fold_left f acc indices

let fold f acc c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> acc
  | Cast (c,_,t) -> f (f acc c) t
  | Prod (_,t,c) -> f (f acc t) c
  | Lambda (_,t,c) -> f (f acc t) c
  | LetIn (_,b,t,c) -> f (f (f acc b) t) c
  | App (c,l) -> Array.fold_left f (f acc c) l
  | Proj (_p,_r,c) -> f acc c
  | Evar (_,l) -> SList.Skip.fold f acc l
  | Case (_,_,pms,((_,p),_),iv,c,bl) ->
    Array.fold_left (fun acc (_, b) -> f acc b) (f (fold_invert f (f (Array.fold_left f acc pms) p) iv) c) bl
  | Fix (_,(_lna,tl,bl)) ->
    Array.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl
  | CoFix (_,(_lna,tl,bl)) ->
    Array.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl
  | Array(_u,t,def,ty) ->
    f (f (Array.fold_left f acc t) def) ty

(* [iter f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let iter_invert f = function
  | NoInvert -> ()
  | CaseInvert {indices;} ->
    Array.iter f indices

let iter f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> ()
  | Cast (c,_,t) -> f c; f t
  | Prod (_,t,c) -> f t; f c
  | Lambda (_,t,c) -> f t; f c
  | LetIn (_,b,t,c) -> f b; f t; f c
  | App (c,l) -> f c; Array.iter f l
  | Proj (_p,_r,c) -> f c
  | Evar (_,l) -> SList.Skip.iter f l
  | Case (_,_,pms,p,iv,c,bl) ->
    Array.iter f pms; f (snd @@ fst p); iter_invert f iv; f c; Array.iter (fun (_, b) -> f b) bl
  | Fix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl
  | CoFix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl
  | Array(_u,t,def,ty) -> Array.iter f t; f def; f ty

(* [iter_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_with_binders g f n c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (_,t,c) -> f n t; f (g n) c
  | Lambda (_,t,c) -> f n t; f (g n) c
  | LetIn (_,b,t,c) -> f n b; f n t; f (g n) c
  | App (c,l) -> f n c; Array.Fun1.iter f n l
  | Evar (_,l) -> SList.Skip.iter (fun c -> f n c) l
  | Case (_,_,pms,(p,_),iv,c,bl) ->
    Array.Fun1.iter f n pms;
    f (iterate g (Array.length (fst p)) n) (snd p);
    iter_invert (f n) iv;
    f n c;
    Array.Fun1.iter (fun n (ctx, b) -> f (iterate g (Array.length ctx) n) b) n bl
  | Proj (_p,_r,c) -> f n c
  | Fix (_,(_,tl,bl)) ->
      Array.Fun1.iter f n tl;
      Array.Fun1.iter f (iterate g (Array.length tl) n) bl
  | CoFix (_,(_,tl,bl)) ->
      Array.Fun1.iter f n tl;
      Array.Fun1.iter f (iterate g (Array.length tl) n) bl
  | Array(_u,t,def,ty) ->
    Array.iter (f n) t; f n def; f n ty

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

let fold_constr_with_binders g f n acc c =
  match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (_na,t,c) -> f (g  n) (f n acc t) c
  | Lambda (_na,t,c) -> f (g  n) (f n acc t) c
  | LetIn (_na,b,t,c) -> f (g  n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (_p,_r,c) -> f n acc c
  | Evar (_,l) -> SList.Skip.fold (f n) acc l
  | Case (_,_,pms,(p,_),iv,c,bl) ->
    let fold_ctx n accu (nas, c) =
      f (iterate g (Array.length nas) n) accu c
    in
    Array.fold_left (fold_ctx n) (f n (fold_invert (f n) (fold_ctx n (Array.fold_left (f n) acc pms) p) iv) c) bl
  | Fix (_,(_,tl,bl)) ->
      let n' = iterate g (Array.length tl) n in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(_,tl,bl)) ->
      let n' = iterate g (Array.length tl) n in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | Array(_u,t,def,ty) ->
    f n (f n (Array.fold_left (f n) acc t) def) ty

(* [map f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let map_under_context f d =
  let (nas, p) = d in
  let p' = f p in
  if p' == p then d else (nas, p')

let map_branches f bl =
  let bl' = Array.map (map_under_context f) bl in
  if Array.for_all2 (==) bl' bl then bl else bl'

let map_return_predicate f (p,r as v) =
  let p' = map_under_context f p in
  if p == p' then v else p', r

let map_under_context_with_binders g f l d =
  let (nas, p) = d in
  let l = iterate g (Array.length nas) l in
  let p' = f l p in
  if p' == p then d else (nas, p')

let map_branches_with_binders g f l bl =
  let bl' = Array.map (map_under_context_with_binders g f l) bl in
  if Array.for_all2 (==) bl' bl then bl else bl'

let map_return_predicate_with_binders g f l (p,r as v) =
  let p' = map_under_context_with_binders g f l p in
  if p == p' then v else p',r

let map_invert f = function
  | NoInvert -> NoInvert
  | CaseInvert {indices;} as orig ->
    let indices' = Array.Smart.map f indices in
    if indices == indices' then orig
    else CaseInvert {indices=indices';}

let map f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> c
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
  | Proj (p,r,t) ->
      let t' = f t in
      if t' == t then c
      else mkProj (p, r, t')
  | Evar (e,l) ->
      let l' = SList.Smart.map f l in
      if l'==l then c
      else mkEvar (e, l')
  | Case (ci,u,pms,p,iv,b,bl) ->
      let pms' = Array.Smart.map f pms in
      let b' = f b in
      let iv' = map_invert f iv in
      let p' = map_return_predicate f p in
      let bl' = map_branches f bl in
      if b'==b && iv'==iv && p'==p && bl'==bl && pms'==pms then c
      else mkCase (ci, u, pms', p', iv', b', bl')
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
  | Array(u,t,def,ty) ->
    let t' = Array.Smart.map f t in
    let def' = f def in
    let ty' = f ty in
    if def'==def && t==t' && ty==ty' then c
    else mkArray(u,t',def',ty')

(* Like {!map} but with an accumulator. *)

let fold_map_invert f acc = function
  | NoInvert -> acc, NoInvert
  | CaseInvert {indices;} as orig ->
    let acc, indices' = Array.Smart.fold_left_map f acc indices in
    if indices==indices' then acc, orig
    else acc, CaseInvert {indices=indices';}

let fold_map_under_context f accu d =
  let (nas, p) = d in
  let accu, p' = f accu p in
  if p' == p then accu, d else accu, (nas, p')

let fold_map_branches f accu bl =
  let accu, bl' = Array.Smart.fold_left_map (fold_map_under_context f) accu bl in
  if Array.for_all2 (==) bl' bl then accu, bl else accu, bl'

let fold_map_return_predicate f accu (p,r as v) =
  let accu, p' = fold_map_under_context f accu p in
  let v = if p == p' then v else p', r in
  accu, v

let fold_map f accu c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> accu, c
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
  | Proj (p,r,t) ->
      let accu, t' = f accu t in
      if t' == t then accu, c
      else accu, mkProj (p, r, t')
  | Evar (e,l) ->
      let accu, l' = SList.Smart.fold_left_map f accu l in
      if l'==l then accu, c
      else accu, mkEvar (e, l')
  | Case (ci,u,pms,p,iv,b,bl) ->
      let accu, pms' = Array.Smart.fold_left_map f accu pms in
      let accu, p' = fold_map_return_predicate f accu p in
      let accu, iv' = fold_map_invert f accu iv in
      let accu, b' = f accu b in
      let accu, bl' = fold_map_branches f accu bl in
      if pms'==pms && p'==p && iv'==iv && b'==b && bl'==bl then accu, c
      else accu, mkCase (ci, u, pms', p', iv', b', bl')
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
  | Array(u,t,def,ty) ->
    let accu, t' = Array.Smart.fold_left_map f accu t in
    let accu, def' = f accu def in
    let accu, ty' = f accu ty in
    if def'==def && t==t' && ty==ty' then accu, c
    else accu, mkArray(u,t',def',ty')

(* [map_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let map_with_binders g f l c0 = match kind c0 with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> c0
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
  | Proj (p, r, t) ->
    let t' = f l t in
    if t' == t then c0
    else mkProj (p, r, t')
  | Evar (e, al) ->
    let al' = SList.Smart.map (fun c -> f l c) al in
    if al' == al then c0
    else mkEvar (e, al')
  | Case (ci, u, pms, p, iv, c, bl) ->
    let pms' = Array.Fun1.Smart.map f l pms in
    let p' = map_return_predicate_with_binders g f l p in
    let iv' = map_invert (f l) iv in
    let c' = f l c in
    let bl' = map_branches_with_binders g f l bl in
    if pms' == pms && p' == p && iv' == iv && c' == c && bl' == bl then c0
    else mkCase (ci, u, pms', p', iv', c', bl')
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
  | Array(u,t,def,ty) ->
    let t' = Array.Fun1.Smart.map f l t in
    let def' = f l def in
    let ty' = f l ty in
    if def'==def && t==t' && ty==ty' then c0
    else mkArray(u,t',def',ty')

(*********************)
(*      Lifting      *)
(*********************)

(* The generic lifting function *)
let rec exliftn el c =
  let open Esubst in
  match kind c with
  | Rel i ->
    let j = reloc_rel i el in
    if Int.equal i j then c else mkRel j
  | _ -> map_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn n k c =
  let open Esubst in
  match el_liftn (pred k) (el_shft n el_id) with
    | ELID -> c
    | el -> exliftn el c

let lift n = liftn n 1

type 'univs instance_compare_fn = (GlobRef.t * int) option ->
  'univs -> 'univs -> bool

type 'constr constr_compare_fn = int -> 'constr -> 'constr -> bool

(* [compare_head_gen_evar k1 k2 u s e eq leq c1 c2] compare [c1] and
   [c2] (using [k1] to expose the structure of [c1] and [k2] to expose
   the structure [c2]) using [eq] to compare the immediate subterms of
   [c1] of [c2] for conversion if needed, [leq] for cumulativity, [u]
   to compare universe instances, and [s] to compare sorts; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account. Note that as [kind1] and [kind2] are
   potentially different, we cannot use, in recursive case, the
   optimisation that physically equal arrays are equals (hence the
   calls to {!Array.equal_norefl}). *)

let eq_invert eq iv1 iv2 =
  match iv1, iv2 with
  | NoInvert, NoInvert -> true
  | NoInvert, CaseInvert _ | CaseInvert _, NoInvert -> false
  | CaseInvert {indices}, CaseInvert iv2 ->
    Array.equal eq indices iv2.indices

let eq_under_context eq (_nas1, p1) (_nas2, p2) =
  eq p1 p2

let compare_head_gen_leq_with kind1 kind2 leq_universes leq_sorts eq_evars eq leq nargs t1 t2 =
  match kind_nocast_gen kind1 t1, kind_nocast_gen kind2 t2 with
  | Cast _, _ | _, Cast _ -> assert false (* kind_nocast *)
  | Rel n1, Rel n2 -> Int.equal n1 n2
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Int i1, Int i2 -> Uint63.equal i1 i2
  | Float f1, Float f2 -> Float64.equal f1 f2
  | String s1, String s2 -> Pstring.equal s1 s2
  | Sort s1, Sort s2 -> leq_sorts s1 s2
  | Prod (_,t1,c1), Prod (_,t2,c2) -> eq 0 t1 t2 && leq 0 c1 c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) -> eq 0 t1 t2 && eq 0 c1 c2
  | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> eq 0 b1 b2 && eq 0 t1 t2 && leq nargs c1 c2
  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    Int.equal len (Array.length l2) &&
    leq (nargs+len) c1 c2 && Array.equal_norefl (eq 0) l1 l2
  | Proj (p1,_,c1), Proj (p2,_,c2) ->
    Projection.CanOrd.equal p1 p2 && eq 0 c1 c2
  | Evar (e1,l1), Evar (e2,l2) -> eq_evars (e1, l1) (e2, l2)
  | Const (c1,u1), Const (c2,u2) ->
    (* The args length currently isn't used but may as well pass it. *)
    Constant.CanOrd.equal c1 c2 && leq_universes (Some (GlobRef.ConstRef c1, nargs)) u1 u2
  | Ind (c1,u1), Ind (c2,u2) -> Ind.CanOrd.equal c1 c2 && leq_universes (Some (GlobRef.IndRef c1, nargs)) u1 u2
  | Construct (c1,u1), Construct (c2,u2) ->
    Construct.CanOrd.equal c1 c2 && leq_universes (Some (GlobRef.ConstructRef c1, nargs)) u1 u2
  | Case (ci1,u1,pms1,(p1,_r1),iv1,c1,bl1), Case (ci2,u2,pms2,(p2,_r2),iv2,c2,bl2) ->
    (* Ignore _r1/_r2: implied by comparing p1/p2 *)
    (** FIXME: what are we doing with u1 = u2 ? *)
    Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind && leq_universes (Some (GlobRef.IndRef ci1.ci_ind, 0)) u1 u2 &&
    Array.equal (eq 0) pms1 pms2 && eq_under_context (eq 0) p1 p2 &&
    eq_invert (eq 0) iv1 iv2 &&
    eq 0 c1 c2 && Array.equal (eq_under_context (eq 0)) bl1 bl2
  | Fix ((ln1, i1),(_,tl1,bl1)), Fix ((ln2, i2),(_,tl2,bl2)) ->
    Int.equal i1 i2 && Array.equal Int.equal ln1 ln2
    && Array.equal_norefl (eq 0) tl1 tl2 && Array.equal_norefl (eq 0) bl1 bl2
  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
    Int.equal ln1 ln2 && Array.equal_norefl (eq 0) tl1 tl2 && Array.equal_norefl (eq 0) bl1 bl2
  | Array(u1,t1,def1,ty1), Array(u2,t2,def2,ty2) ->
    leq_universes None u1 u2 &&
    Array.equal_norefl (eq 0) t1 t2 &&
    eq 0 def1 def2 && eq 0 ty1 ty2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false

(* [compare_head_gen_leq u s eq leq c1 c2] compare [c1] and [c2] using [eq] to compare
   the immediate subterms of [c1] of [c2] for conversion if needed, [leq] for cumulativity,
   [u] to compare universe instances and [s] to compare sorts; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account *)

let compare_head_gen_leq leq_universes leq_sorts eq_evars eq leq t1 t2 =
  compare_head_gen_leq_with kind kind leq_universes leq_sorts eq_evars eq leq t1 t2

(* [compare_head_gen u s f c1 c2] compare [c1] and [c2] using [f] to
   compare the immediate subterms of [c1] of [c2] if needed, [u] to
   compare universe instances and [s] to compare sorts; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account.

   [compare_head_gen_with] is a variant taking kind-of-term functions,
   to expose subterms of [c1] and [c2], as arguments. *)

let compare_head_gen_with kind1 kind2 eq_universes eq_sorts eq_evars eq t1 t2 =
  compare_head_gen_leq_with kind1 kind2 eq_universes eq_sorts eq_evars eq eq t1 t2

let compare_head_gen eq_universes eq_sorts eq_evars eq t1 t2 =
  compare_head_gen_leq eq_universes eq_sorts eq_evars eq eq t1 t2

let compare_head = compare_head_gen (fun _ -> UVars.Instance.equal) Sorts.equal

(*******************************)
(*  alpha conversion functions *)
(*******************************)

(* alpha conversion : ignore print names and casts *)

let eq_existential eq (evk1, args1) (evk2, args2) =
  Evar.equal evk1 evk2 && SList.equal eq args1 args2

let rec eq_constr nargs m n =
  (m == n) || compare_head_gen (fun _ -> Instance.equal) Sorts.equal (eq_existential (eq_constr 0)) eq_constr nargs m n

let equal n m = eq_constr 0 m n (* to avoid tracing a recursive fun *)

let eq_constr_univs univs m n =
  if m == n then true
  else
    let eq_universes _ = UGraph.check_eq_instances univs in
    let eq_sorts s1 s2 = s1 == s2 || UGraph.check_eq_sort univs s1 s2 in
    let rec eq_constr' nargs m n =
      m == n ||	compare_head_gen eq_universes eq_sorts (eq_existential (eq_constr' 0)) eq_constr' nargs m n
    in compare_head_gen eq_universes eq_sorts (eq_existential (eq_constr' 0)) eq_constr' 0 m n

let leq_constr_univs univs m n =
  if m == n then true
  else
    let eq_universes _ = UGraph.check_eq_instances univs in
    let eq_sorts s1 s2 = s1 == s2 ||
      UGraph.check_eq_sort univs s1 s2 in
    let leq_sorts s1 s2 = s1 == s2 ||
      UGraph.check_leq_sort univs s1 s2 in
    let rec eq_constr' nargs m n =
      m == n || compare_head_gen eq_universes eq_sorts (eq_existential (eq_constr' 0)) eq_constr' nargs m n
    in
    let rec compare_leq nargs m n =
      compare_head_gen_leq eq_universes leq_sorts (eq_existential (eq_constr' 0)) eq_constr' leq_constr' nargs m n
    and leq_constr' nargs m n = m == n || compare_leq nargs m n in
    compare_leq 0 m n

let rec eq_constr_nounivs m n =
  (m == n) || compare_head_gen (fun _ _ _ -> true) (fun _ _ -> true) (eq_existential eq_constr_nounivs) (fun _ -> eq_constr_nounivs) 0 m n

let compare_invert f iv1 iv2 =
  match iv1, iv2 with
  | NoInvert, NoInvert -> 0
  | NoInvert, CaseInvert _ -> -1
  | CaseInvert _, NoInvert -> 1
  | CaseInvert iv1, CaseInvert iv2 ->
    Array.compare f iv1.indices iv2.indices

let constr_ord_int f t1 t2 =
  let open! Compare in
  let fix_cmp (a1, i1) (a2, i2) =
    compare [(Array.compare Int.compare,a1,a2); (Int.compare,i1,i2)]
  in
  let ctx_cmp f (_n1, p1) (_n2, p2) = f p1 p2 in
  match kind t1, kind t2 with
    | Cast (c1,_,_), _ -> f c1 t2
    | _, Cast (c2,_,_) -> f t1 c2
    (* Why this special case? *)
    | App (c1,l1), _ when isCast c1 -> let c1 = pi1 (destCast c1) in f (mkApp (c1,l1)) t2
    | _, App (c2,l2) when isCast c2 -> let c2 = pi1 (destCast c2) in f t1 (mkApp (c2,l2))
    | Rel n1, Rel n2 -> Int.compare n1 n2
    | Rel _, _ -> -1 | _, Rel _ -> 1
    | Var id1, Var id2 -> Id.compare id1 id2
    | Var _, _ -> -1 | _, Var _ -> 1
    | Meta m1, Meta m2 -> Int.compare m1 m2
    | Meta _, _ -> -1 | _, Meta _ -> 1
    | Evar (e1,l1), Evar (e2,l2) ->
      compare [(Evar.compare, e1, e2); (SList.compare f, l1, l2)]
    | Evar _, _ -> -1 | _, Evar _ -> 1
    | Sort s1, Sort s2 -> Sorts.compare s1 s2
    | Sort _, _ -> -1 | _, Sort _ -> 1
    | Prod (_,t1,c1), Prod (_,t2,c2)
    | Lambda (_,t1,c1), Lambda (_,t2,c2) -> compare [(f,t1,t2); (f,c1,c2)]
    | Prod _, _ -> -1 | _, Prod _ -> 1
    | Lambda _, _ -> -1 | _, Lambda _ -> 1
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> compare [(f,b1,b2); (f,t1,t2); (f,c1,c2)]
    | LetIn _, _ -> -1 | _, LetIn _ -> 1
    | App (c1,l1), App (c2,l2) -> compare [(f,c1,c2); (Array.compare f, l1, l2)]
    | App _, _ -> -1 | _, App _ -> 1
    | Const (c1,_u1), Const (c2,_u2) -> Constant.CanOrd.compare c1 c2
    | Const _, _ -> -1 | _, Const _ -> 1
    | Ind (ind1, _u1), Ind (ind2, _u2) -> Ind.CanOrd.compare ind1 ind2
    | Ind _, _ -> -1 | _, Ind _ -> 1
    | Construct (ct1,_u1), Construct (ct2,_u2) -> Construct.CanOrd.compare ct1 ct2
    | Construct _, _ -> -1 | _, Construct _ -> 1
    | Case (_,_u1,pms1,(p1,_r1),iv1,c1,bl1), Case (_,_u2,pms2,(p2,_r2),iv2,c2,bl2) ->
      compare [
        (Array.compare f, pms1, pms2);
        (ctx_cmp f, p1, p2);
        (compare_invert f, iv1, iv2);
        (f, c1, c2);
        (Array.compare (ctx_cmp f), bl1, bl2);
      ]
    | Case _, _ -> -1 | _, Case _ -> 1
    | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
      compare [(fix_cmp, ln1, ln2); (Array.compare f, tl1, tl2); (Array.compare f, bl1, bl2)]
    | Fix _, _ -> -1 | _, Fix _ -> 1
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      compare [(Int.compare, ln1, ln2); (Array.compare f, tl1, tl2); (Array.compare f, bl1, bl2)]
    | CoFix _, _ -> -1 | _, CoFix _ -> 1
    | Proj (p1,_r1,c1), Proj (p2,_r2,c2) -> compare [(Projection.CanOrd.compare, p1, p2); (f, c1, c2)]
    | Proj _, _ -> -1 | _, Proj _ -> 1
    | Int i1, Int i2 -> Uint63.compare i1 i2
    | Int _, _ -> -1 | _, Int _ -> 1
    | Float f1, Float f2 -> Float64.total_compare f1 f2
    | Float _, _ -> -1 | _, Float _ -> 1
    | String s1, String s2 -> Pstring.compare s1 s2
    | String _, _ -> -1 | _, String _ -> 1
    | Array(_u1,t1,def1,ty1), Array(_u2,t2,def2,ty2) ->
      compare [(Array.compare f, t1, t2); (f, def1, def2); (f, ty1, ty2)]
    (*| Array _, _ -> -1 | _, Array _ -> 1*)

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
   by the use of generic equality in Rocq source code. (Indeed, this forces
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
   structure for our daily use of Rocq.
*)

let array_eqeq t1 t2 =
  t1 == t2 ||
  (Int.equal (Array.length t1) (Array.length t2) &&
   let rec aux i =
     (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
   in aux 0)

let invert_eqeq iv1 iv2 =
  match iv1, iv2 with
  | NoInvert, NoInvert -> true
  | NoInvert, CaseInvert _ | CaseInvert _, NoInvert -> false
  | CaseInvert {indices=i1}, CaseInvert {indices=i2} ->
    i1 == i2

let hasheq_ctx (nas1, c1) (nas2, c2) =
  array_eqeq nas1 nas2 && c1 == c2

let hasheq_kind t1 t2 =
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
    | Proj (p1,r1,c1), Proj(p2,r2,c2) -> p1 == p2 && r1 == r2 && c1 == c2
    | Evar (e1,l1), Evar (e2,l2) -> e1 == e2 && SList.equal (==) l1 l2
    | Const (c1,u1), Const (c2,u2) -> c1 == c2 && u1 == u2
    | Ind (ind1,u1), Ind (ind2,u2) -> ind1 == ind2 && u1 == u2
    | Construct (cstr1,u1), Construct (cstr2,u2) -> cstr1 == cstr2 && u1 == u2
    | Case (ci1,u1,pms1,(p1,r1),iv1,c1,bl1), Case (ci2,u2,pms2,(p2,r2),iv2,c2,bl2) ->
      (** FIXME: use deeper equality for contexts *)
      u1 == u2 && array_eqeq pms1 pms2 &&
      ci1 == ci2 && hasheq_ctx p1 p2 && r1 == r2 &&
      invert_eqeq iv1 iv2 && c1 == c2 && Array.equal hasheq_ctx bl1 bl2
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
    | Int i1, Int i2 -> i1 == i2
    | Float f1, Float f2 -> Float64.equal f1 f2
    | String s1, String s2 -> Pstring.equal s1 s2
    | Array(u1,t1,def1,ty1), Array(u2,t2,def2,ty2) ->
      u1 == u2 && def1 == def2 && ty1 == ty2 && array_eqeq t1 t2
    | (Rel _ | Meta _ | Var _ | Sort _ | Cast _ | Prod _ | Lambda _ | LetIn _
      | App _ | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _
      | Fix _ | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false

let hasheq t1 t2 = hasheq_kind (kind t1) (kind t2)

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

(* Exported hashing fonction on constr, used mainly in plugins.
   Slight differences from [snd (hash_term t)] above: it ignores binders. *)

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
    | App (c,l) -> begin match kind c with
        | Cast (c, _, _) -> hash (mkApp (c,l)) (* WTF *)
        | _ -> combinesmall 7 (combine (hash_term_array l) (hash c))
      end
    | Evar (e,l) ->
      combinesmall 8 (combine (Evar.hash e) (hash_term_list l))
    | Const (c,u) ->
      combinesmall 9 (combine (Constant.CanOrd.hash c) (Instance.hash u))
    | Ind (ind,u) ->
      combinesmall 10 (combine (Ind.CanOrd.hash ind) (Instance.hash u))
    | Construct (c,u) ->
      combinesmall 11 (combine (Construct.CanOrd.hash c) (Instance.hash u))
    | Case (_ , u, pms, (p,r), iv, c, bl) ->
      combinesmall 12 (combine5 (hash c) (hash_invert iv) (hash_term_array pms) (Instance.hash u)
                         (combine3 (hash_under_context p) (Sorts.relevance_hash r) (hash_branches bl)))
    | Fix (_ln ,(_, tl, bl)) ->
      combinesmall 13 (combine (hash_term_array bl) (hash_term_array tl))
    | CoFix(_ln, (_, tl, bl)) ->
       combinesmall 14 (combine (hash_term_array bl) (hash_term_array tl))
    | Meta n -> combinesmall 15 n
    | Rel n -> combinesmall 16 n
    | Proj (p,r, c) ->
      combinesmall 17 (combine3 (Projection.CanOrd.hash p) (Sorts.relevance_hash r) (hash c))
    | Int i -> combinesmall 18 (Uint63.hash i)
    | Float f -> combinesmall 19 (Float64.hash f)
    | String s -> combinesmall 20 (Pstring.hash s)
    | Array(u,t,def,ty) ->
      combinesmall 21 (combine4 (Instance.hash u) (hash_term_array t) (hash def) (hash ty))

and hash_invert = function
  | NoInvert -> 0
  | CaseInvert {indices;} ->
    combinesmall 1 (hash_term_array indices)

and hash_term_array t =
  Array.fold_left (fun acc t -> combine acc (hash t)) 0 t

and hash_term_list t =
  SList.Skip.fold (fun acc t -> combine (hash t) acc) 0 t

and hash_under_context (_, t) = hash t

and hash_branches bl =
  Array.fold_left (fun acc t -> combine acc (hash_under_context t)) 0 bl

module CaseinfoHash =
struct
  type t = case_info
  type u = inductive -> inductive
  let hashcons hind ci = { ci with ci_ind = hind ci.ci_ind }
  let pp_info_equal info1 info2 =
    info1.style == info2.style
  let eq ci ci' =
    ci.ci_ind == ci'.ci_ind &&
    Int.equal ci.ci_npar ci'.ci_npar &&
    Array.equal Int.equal ci.ci_cstr_ndecls ci'.ci_cstr_ndecls && (* we use [Array.equal] on purpose *)
    Array.equal Int.equal ci.ci_cstr_nargs ci'.ci_cstr_nargs && (* we use [Array.equal] on purpose *)
    pp_info_equal ci.ci_pp_info ci'.ci_pp_info  (* we use (=) on purpose *)
  open Hashset.Combine
  let hash_pp_info info =
    let h1 = match info.style with
    | LetStyle -> 0
    | IfStyle -> 1
    | LetPatternStyle -> 2
    | MatchStyle -> 3
    | RegularStyle -> 4 in
    h1
  let hash ci =
    let h1 = Ind.CanOrd.hash ci.ci_ind in
    let h2 = Int.hash ci.ci_npar in
    let h3 = Array.fold_left combine 0 ci.ci_cstr_ndecls in
    let h4 = Array.fold_left combine 0 ci.ci_cstr_nargs in
    let h5 = hash_pp_info ci.ci_pp_info in
    combine5 h1 h2 h3 h4 h5
end

module Hcaseinfo = Hashcons.Make(CaseinfoHash)

let case_info_hash = CaseinfoHash.hash

let hcons_caseinfo = Hashcons.simple_hcons Hcaseinfo.generate Hcaseinfo.hcons hcons_ind

module Hannotinfo = struct
    type t = Name.t binder_annot
    type u = Name.t -> Name.t
    let hash = hash_annot Name.hash
    let eq = eq_annot (fun na1 na2 -> na1 == na2) Sorts.relevance_equal
    let hashcons h {binder_name=na;binder_relevance} =
      {binder_name=h na;binder_relevance}
  end
module Hannot = Hashcons.Make(Hannotinfo)

let hcons_annot = Hashcons.simple_hcons Hannot.generate Hannot.hcons Name.hcons

let dbg = CDebug.create ~name:"hcons" ()

module GenHCons(C:sig
    type t
    val kind : t -> (t, t, Sorts.t, Instance.t, Sorts.relevance) kind_of_term
    val self : t -> constr
    val refcount : t -> int

    val via_hconstr : bool

    module Tbl : sig
      val find_opt : t -> (constr * int) option
      val add : t -> constr * int -> unit
    end
  end) = struct
open C

let steps = ref 0

let rec hash_term (t : t) =
  match kind t with
  | Var i ->
    (Var (Id.hcons i), combinesmall 1 (Id.hash i))
  | Sort s ->
    (Sort (Sorts.hcons s), combinesmall 2 (Sorts.hash s))
  | Cast (c, k, t) ->
    let c, hc = sh_rec c in
    let t, ht = sh_rec t in
    (Cast (c, k, t), combinesmall 3 (combine3 hc (hash_cast_kind k) ht))
  | Prod (na,t,c) ->
    let t, ht = sh_rec t
    and c, hc = sh_rec c in
    (Prod (hcons_annot na, t, c), combinesmall 4 (combine3 (hash_annot Name.hash na) ht hc))
  | Lambda (na,t,c) ->
    let t, ht = sh_rec t
    and c, hc = sh_rec c in
    (Lambda (hcons_annot na, t, c), combinesmall 5 (combine3 (hash_annot Name.hash na) ht hc))
  | LetIn (na,b,t,c) ->
    let b, hb = sh_rec b in
    let t, ht = sh_rec t in
    let c, hc = sh_rec c in
    (LetIn (hcons_annot na, b, t, c), combinesmall 6 (combine4 (hash_annot Name.hash na) hb ht hc))
  | App (c,l) ->
    let _, cl = destApp (self t) in
    let c, hc = sh_rec c in
    let l, hl = hash_term_array cl l in
    (App (c,l), combinesmall 7 (combine hl hc))
  | Evar _ -> assert false
  | Const (c,u) ->
    let c' = hcons_con c in
    let u', hu = Instance.share u in
    (Const (c', u'), combinesmall 9 (combine (Constant.SyntacticOrd.hash c) hu))
  | Ind (ind,u) ->
    let u', hu = Instance.share u in
    (Ind (hcons_ind ind, u'),
     combinesmall 10 (combine (Ind.SyntacticOrd.hash ind) hu))
  | Construct (c,u) ->
    let u', hu = Instance.share u in
    (Construct (hcons_construct c, u'),
     combinesmall 11 (combine (Construct.SyntacticOrd.hash c) hu))
  | Case (ci,u,pms,(p,r),iv,c,bl) ->
    (** FIXME: use a dedicated hashconsing structure *)
    let hcons_ctx (lna, c) =
      let () = Array.iteri (fun i x -> Array.unsafe_set lna i (hcons_annot x)) lna in
      let fold accu na = combine (hash_annot Name.hash na) accu in
      let hna = Array.fold_left fold 0 lna in
      let c, hc = sh_rec c in
      (lna, c), combine hna hc
    in
    let u, hu = Instance.share u in
    let _,_,cpms,_,civ,_,_ = destCase (self t) in
    let pms,hpms = hash_term_array cpms pms in
    let p, hp = hcons_ctx p in
    let iv, hiv = sh_invert civ iv in
    let c, hc = sh_rec c in
    let fold accu c =
      let c, h = hcons_ctx c in
      combine accu h, c
    in
    let hbl, bl = Array.fold_left_map fold 0 bl in
    let hbl = combine (combine hc (combine hiv (combine hpms (combine hu hp)))) hbl in
    (Case (hcons_caseinfo ci, u, pms, (p,r), iv, c, bl), combinesmall 12 hbl)
  | Fix (ln,(lna,tl,bl)) ->
    let _, (_,ctl,cbl) = destFix (self t) in
    let bl,hbl = hash_term_array cbl bl in
    let tl,htl = hash_term_array ctl tl in
    let () = Array.iteri (fun i x -> Array.unsafe_set lna i (hcons_annot x)) lna in
    let fold accu na = combine (hash_annot Name.hash na) accu in
    let hna = Array.fold_left fold 0 lna in
    let h = combine3 hna hbl htl in
    (Fix (ln,(lna,tl,bl)), combinesmall 13 h)
  | CoFix(ln,(lna,tl,bl)) ->
    let _, (_,ctl,cbl) = destCoFix (self t) in
    let bl,hbl = hash_term_array cbl bl in
    let tl,htl = hash_term_array ctl tl in
    let () = Array.iteri (fun i x -> Array.unsafe_set lna i (hcons_annot x)) lna in
    let fold accu na = combine (hash_annot Name.hash na) accu in
    let hna = Array.fold_left fold 0 lna in
    let h = combine3 hna hbl htl in
    (CoFix (ln,(lna,tl,bl)), combinesmall 14 h)
  | Meta n as t ->
    (t, combinesmall 15 n)
  | Rel n as t ->
    (t, combinesmall 16 n)
  | Proj (p,r,c) ->
    let c, hc = sh_rec c in
    let p' = Projection.hcons p in
    (Proj (p', r, c), combinesmall 17 (combine (Projection.SyntacticOrd.hash p') hc))
  | Int i as t ->
    let (h,l) = Uint63.to_int2 i in
    (t, combinesmall 18 (combine h l))
  | Float f as t -> (t, combinesmall 19 (Float64.hash f))
  | String s as t -> (t, combinesmall 20 (Pstring.hash s))
  | Array (u,ar,def,ty) ->
    let _,car,_,_ = destArray (self t) in
    let u, hu = Instance.share u in
    let t, ht = hash_term_array car ar in
    let def, hdef = sh_rec def in
    let ty, hty = sh_rec ty in
    let h = combine4 hu ht hdef hty in
    (Array(u,t,def,ty), combinesmall 21 h)

and sh_invert civ iv = match civ, iv with
  | NoInvert, NoInvert -> NoInvert, 0
  | CaseInvert {indices=cindices}, CaseInvert {indices;} ->
    let indices, ha = hash_term_array cindices indices in
    CaseInvert {indices;}, combinesmall 1 ha
  | (NoInvert | CaseInvert _), _ -> assert false

and sh_rec_main t =
  let (y, h) = hash_term t in
  (HashsetTerm.repr h (T y) term_table, h)

and sh_rec t =
  incr steps;
  if refcount t = 1 then sh_rec_main t
  else match Tbl.find_opt t with
    | Some res -> res
    | None ->
      let res = sh_rec_main t in
      Tbl.add t res;
      res

(* Note : During hash-cons of arrays, we modify them *in place* *)

and hash_term_array ct t =
  let accu = ref 0 in
  for i = 0 to Array.length t - 1 do
    let x, h = sh_rec (Array.unsafe_get t i) in
    accu := combine !accu h;
    Array.unsafe_set ct i x
  done;
  let h = !accu in
  (HashsetTermArray.repr h ct term_array_table, h)

let hcons t = NewProfile.profile "Constr.hcons" (fun () -> fst (sh_rec t)) ()

let hcons t =
  steps := 0;
  let t = hcons t in
  dbg Pp.(fun () ->
      let open Hashset in
      let stats = HashsetTerm.stats term_table in
      v 0 (
        str "via hconstr = " ++ bool via_hconstr ++ spc() ++
        str "steps = " ++ int !steps ++ spc() ++
        str "num_bindings = " ++ int stats.num_bindings ++ spc() ++
        str "num_buckets = " ++ int stats.num_buckets ++ spc() ++
        str "max_bucket_length = " ++ int stats.max_bucket_length
      )
    );
  t

end

module HCons = GenHCons(struct
    type t = constr
    let kind = kind
    let self x = x
    let refcount _ = 1

    let via_hconstr = false

    module Tbl = struct
      let find_opt _ = None
      let add _ _ : unit = assert false
    end
  end)

  (* Make sure our statically allocated Rels (1 to 16) are considered
     as canonical, and hence hash-consed to themselves *)
let () = ignore (HCons.hash_term_array rels rels)

let hcons = HCons.hcons

(* let hcons_types = hcons_constr *)

type rel_declaration = (constr, types, Sorts.relevance) Context.Rel.Declaration.pt
type named_declaration = (constr, types, Sorts.relevance) Context.Named.Declaration.pt
type compacted_declaration = (constr, types, Sorts.relevance) Context.Compacted.Declaration.pt
type rel_context = rel_declaration list
type named_context = named_declaration list
type compacted_context = compacted_declaration list

(** Minimalistic constr printer, typically for debugging *)

let debug_print_fix pr_constr ((t,i),(lna,tl,bl)) =
  let open Pp in
  let fixl = Array.mapi (fun i na -> (na.binder_name,t.(i),tl.(i),bl.(i))) lna in
  hov 1
      (str"fix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,i,ty,bd) ->
           Name.print na ++ str"/" ++ int i ++ str":" ++ pr_constr ty ++
           cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")

let pr_puniverses p u =
  if UVars.Instance.is_empty u then p
  else Pp.(p ++ str"(*" ++ UVars.Instance.pr Sorts.QVar.raw_pr Univ.Level.raw_pr u ++ str"*)")

let rec debug_print c =
  let open Pp in
  match kind c with
  | Rel n -> str "#"++int n
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
  | Evar (e,l) ->
    let pro = function None -> str "?" | Some c -> debug_print c in
    hov 1
      (str"Evar#" ++ int (Evar.repr e) ++ str"{" ++
       prlist_with_sep spc pro (SList.to_list l) ++str"}")
  | Const (c,u) -> str"Cst(" ++ pr_puniverses (Constant.debug_print c) u ++ str")"
  | Ind ((sp,i),u) -> str"Ind(" ++ pr_puniverses (MutInd.print sp ++ str"," ++ int i) u ++ str")"
  | Construct (((sp,i),j),u) ->
      str"Constr(" ++ pr_puniverses (MutInd.print sp ++ str"," ++ int i ++ str"," ++ int j) u ++ str")"
  | Proj (p,_r,c) ->
    str"Proj(" ++ Projection.debug_print p ++ str"," ++ debug_print c ++ str")"
  | Case (_ci,_u,pms,(p,_),iv,c,bl) ->
    let pr_ctx (nas, c) =
      hov 2 (hov 0 (prvect (fun na -> Name.print na.binder_name ++ spc ()) nas ++ str "|-") ++ spc () ++
        debug_print c)
    in
    v 0 (hv 0 (str"Case" ++ brk (1,1) ++
             debug_print c ++ spc () ++ str "params" ++ brk (1,1) ++ prvect (fun x -> spc () ++ debug_print x) pms ++
             spc () ++ str"return"++ brk (1,1) ++ pr_ctx p ++ debug_invert iv ++ spc () ++ str"with") ++
       prvect (fun b -> spc () ++ pr_ctx b) bl ++
       spc () ++ str"end")
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
  | String s -> str"String("++str (Printf.sprintf "%S" (Pstring.to_string s)) ++ str")"
  | Array(u,t,def,ty) -> str"Array(" ++ prlist_with_sep pr_comma debug_print (Array.to_list t) ++ str" | "
      ++ debug_print def ++ str " : " ++ debug_print ty
      ++ str")@{" ++ UVars.Instance.pr Sorts.QVar.raw_pr Univ.Level.raw_pr u ++ str"}"

and debug_invert = let open Pp in function
  | NoInvert -> mt()
  | CaseInvert {indices;} ->
    spc() ++ str"Invert {indices=" ++
    prlist_with_sep spc debug_print (Array.to_list indices) ++ str "} "
