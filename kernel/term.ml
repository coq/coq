(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open CErrors
open Names
open Vars

(**********************************************************************)
(**         Redeclaration of types from module Constr                 *)
(**********************************************************************)

type contents = Sorts.contents = Pos | Null

type sorts = Sorts.t =
  | Prop of contents       (** Prop and Set *)
  | Type of Univ.universe  (** Type *)

type sorts_family = Sorts.family = InProp | InSet | InType

type constr = Constr.t
(** Alias types, for compatibility. *)

type types = Constr.t
(** Same as [constr], for documentation purposes. *)

type existential_key = Constr.existential_key
type existential = Constr.existential

type metavariable = Constr.metavariable

type case_style = Constr.case_style =
  LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle

type case_printing = Constr.case_printing =
  { ind_tags : bool list; cstr_tags : bool list array; style : case_style }

type case_info = Constr.case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array;
    ci_cstr_nargs : int array;
    ci_pp_info    : case_printing
  }

type cast_kind = Constr.cast_kind =
  VMcast | NATIVEcast | DEFAULTcast | REVERTcast

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

type rec_declaration = Constr.rec_declaration
type fixpoint = Constr.fixpoint
type cofixpoint = Constr.cofixpoint
type 'constr pexistential = 'constr Constr.pexistential
type ('constr, 'types) prec_declaration =
  ('constr, 'types) Constr.prec_declaration
type ('constr, 'types) pfixpoint = ('constr, 'types) Constr.pfixpoint
type ('constr, 'types) pcofixpoint = ('constr, 'types) Constr.pcofixpoint
type 'a puniverses = 'a Univ.puniverses

(** Simply type aliases *)
type pconstant = constant puniverses
type pinductive = inductive puniverses
type pconstructor = constructor puniverses

type ('constr, 'types, 'sort, 'univs) kind_of_term =
  ('constr, 'types, 'sort, 'univs) Constr.kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of 'sort
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of (constant * 'univs)
  | Ind       of (inductive * 'univs)
  | Construct of (constructor * 'univs)
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | Proj      of projection * 'constr

type values = Constr.values

(**********************************************************************)
(**         Redeclaration of functions from module Constr             *)
(**********************************************************************)

let set_sort  = Sorts.set
let prop_sort = Sorts.prop
let type1_sort  = Sorts.type1
let sorts_ord = Sorts.compare
let is_prop_sort = Sorts.is_prop
let family_of_sort = Sorts.family
let univ_of_sort = Sorts.univ_of_sort
let sort_of_univ = Sorts.sort_of_univ

(** {6 Term constructors. } *)

let mkRel = Constr.mkRel
let mkVar = Constr.mkVar
let mkMeta = Constr.mkMeta
let mkEvar = Constr.mkEvar
let mkSort = Constr.mkSort
let mkProp = Constr.mkProp
let mkSet  = Constr.mkSet 
let mkType = Constr.mkType
let mkCast = Constr.mkCast
let mkProd = Constr.mkProd
let mkLambda = Constr.mkLambda
let mkLetIn = Constr.mkLetIn
let mkApp = Constr.mkApp
let mkConst = Constr.mkConst
let mkProj = Constr.mkProj
let mkInd = Constr.mkInd
let mkConstruct = Constr.mkConstruct
let mkConstU = Constr.mkConstU
let mkIndU = Constr.mkIndU
let mkConstructU = Constr.mkConstructU
let mkConstructUi = Constr.mkConstructUi
let mkCase = Constr.mkCase
let mkFix = Constr.mkFix
let mkCoFix = Constr.mkCoFix

(**********************************************************************)
(**         Aliases of functions from module Constr                   *)
(**********************************************************************)

let eq_constr = Constr.equal
let eq_constr_univs = Constr.eq_constr_univs
let leq_constr_univs = Constr.leq_constr_univs
let eq_constr_nounivs = Constr.eq_constr_nounivs

let kind_of_term = Constr.kind
let constr_ord = Constr.compare
let fold_constr = Constr.fold
let map_puniverses = Constr.map_puniverses
let map_constr = Constr.map
let map_constr_with_binders = Constr.map_with_binders
let iter_constr = Constr.iter
let iter_constr_with_binders = Constr.iter_with_binders
let compare_constr = Constr.compare_head
let hash_constr = Constr.hash
let hcons_sorts = Sorts.hcons
let hcons_constr = Constr.hcons
let hcons_types = Constr.hcons

(**********************************************************************)
(**         HERE BEGINS THE INTERESTING STUFF                         *)
(**********************************************************************)

(**********************************************************************)
(*          Non primitive term destructors                            *)
(**********************************************************************)

(* Destructor operations : partial functions
   Raise [DestKO] if the const has not the expected form *)

exception DestKO

(* Destructs a de Bruijn index *)
let destRel c = match kind_of_term c with
  | Rel n -> n
  | _ -> raise DestKO

(* Destructs an existential variable *)
let destMeta c = match kind_of_term c with
  | Meta n -> n
  | _ -> raise DestKO

let isMeta c = match kind_of_term c with Meta _ -> true | _ -> false

(* Destructs a variable *)
let destVar c = match kind_of_term c with
  | Var id -> id
  | _ -> raise DestKO

(* Destructs a type *)
let isSort c = match kind_of_term c with
  | Sort _ -> true
  | _ -> false

let destSort c = match kind_of_term c with
  | Sort s -> s
  | _ -> raise DestKO

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

let is_small = Sorts.is_small

let iskind c = isprop c || is_Type c

(* Tests if an evar *)
let isEvar c = match kind_of_term c with Evar _ -> true | _ -> false

let isEvar_or_Meta c = match kind_of_term c with
  | Evar _ | Meta _ -> true
  | _ -> false

(* Destructs a casted term *)
let destCast c = match kind_of_term c with
  | Cast (t1,k,t2) -> (t1,k,t2)
  | _ -> raise DestKO

let isCast c = match kind_of_term c with Cast _ -> true | _ -> false


(* Tests if a de Bruijn index *)
let isRel c = match kind_of_term c with Rel _ -> true | _ -> false
let isRelN n c =
  match kind_of_term c with Rel n' -> Int.equal n n' | _ -> false

(* Tests if a variable *)
let isVar c = match kind_of_term c with Var _ -> true | _ -> false
let isVarId id c =
  match kind_of_term c with Var id' -> Id.equal id id' | _ -> false

(* Tests if an inductive *)
let isInd c = match kind_of_term c with Ind _ -> true | _ -> false

(* Destructs the product (x:t1)t2 *)
let destProd c = match kind_of_term c with
  | Prod (x,t1,t2) -> (x,t1,t2)
  | _ -> raise DestKO

let isProd c = match kind_of_term c with | Prod _ -> true | _ -> false

(* Destructs the abstraction [x:t1]t2 *)
let destLambda c = match kind_of_term c with
  | Lambda (x,t1,t2) -> (x,t1,t2)
  | _ -> raise DestKO

let isLambda c = match kind_of_term c with | Lambda _ -> true | _ -> false

(* Destructs the let [x:=b:t1]t2 *)
let destLetIn c = match kind_of_term c with
  | LetIn (x,b,t1,t2) -> (x,b,t1,t2)
  | _ -> raise DestKO

let isLetIn c =  match kind_of_term c with LetIn _ -> true | _ -> false

(* Destructs an application *)
let destApp c = match kind_of_term c with
  | App (f,a) -> (f, a)
  | _ -> raise DestKO

let destApplication = destApp

let isApp c = match kind_of_term c with App _ -> true | _ -> false

(* Destructs a constant *)
let destConst c = match kind_of_term c with
  | Const kn -> kn
  | _ -> raise DestKO

let isConst c = match kind_of_term c with Const _ -> true | _ -> false

(* Destructs an existential variable *)
let destEvar c = match kind_of_term c with
  | Evar (kn, a as r) -> r
  | _ -> raise DestKO

(* Destructs a (co)inductive type named kn *)
let destInd c = match kind_of_term c with
  | Ind (kn, a as r) -> r
  | _ -> raise DestKO

(* Destructs a constructor *)
let destConstruct c = match kind_of_term c with
  | Construct (kn, a as r) -> r
  | _ -> raise DestKO

let isConstruct c = match kind_of_term c with Construct _ -> true | _ -> false

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
let destCase c = match kind_of_term c with
  | Case (ci,p,c,v) -> (ci,p,c,v)
  | _ -> raise DestKO

let isCase c =  match kind_of_term c with Case _ -> true | _ -> false

let isProj c =  match kind_of_term c with Proj _ -> true | _ -> false

let destProj c = match kind_of_term c with
  | Proj (p, c) -> (p, c)
  | _ -> raise DestKO

let destFix c = match kind_of_term c with
  | Fix fix -> fix
  | _ -> raise DestKO

let isFix c =  match kind_of_term c with Fix _ -> true | _ -> false

let destCoFix c = match kind_of_term c with
  | CoFix cofix -> cofix
  | _ -> raise DestKO

let isCoFix c =  match kind_of_term c with CoFix _ -> true | _ -> false

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

let decompose_app c =
  match kind_of_term c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])

let decompose_appvect c =
  match kind_of_term c with
    | App (f,cl) -> (f, cl)
    | _ -> (c,[||])

(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(***************************)
(* Other term constructors *)
(***************************)

let mkNamedProd id typ c = mkProd (Name id, typ, subst_var id c)
let mkNamedLambda id typ c = mkLambda (Name id, typ, subst_var id c)
let mkNamedLetIn id c1 t c2 = mkLetIn (Name id, c1, t, subst_var id c2)

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
let mkProd_or_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkProd (na, t, c)
  | LocalDef (na,b,t) -> mkLetIn (na, b, t, c)

let mkNamedProd_or_LetIn decl c =
  let open Context.Named.Declaration in
  match decl with
    | LocalAssum (id,t) -> mkNamedProd id t c
    | LocalDef (id,b,t) -> mkNamedLetIn id b t c

(* Constructs either [(x:t)c] or [c] where [x] is replaced by [b] *)
let mkProd_wo_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkProd (na, t, c)
  | LocalDef (na,b,t) -> subst1 b c

let mkNamedProd_wo_LetIn decl c =
  let open Context.Named.Declaration in
  match decl with
    | LocalAssum (id,t) -> mkNamedProd id t c
    | LocalDef (id,b,t) -> subst1 b (subst_var id c)

(* non-dependent product t1 -> t2 *)
let mkArrow t1 t2 = mkProd (Anonymous, t1, t2)

(* Constructs either [[x:t]c] or [[x=b:t]c] *)
let mkLambda_or_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
    | LocalAssum (na,t) -> mkLambda (na, t, c)
    | LocalDef (na,b,t) -> mkLetIn (na, b, t, c)

let mkNamedLambda_or_LetIn decl c =
  let open Context.Named.Declaration in
  match decl with
    | LocalAssum (id,t) -> mkNamedLambda id t c
    | LocalDef (id,b,t) -> mkNamedLetIn id b t c

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
  if Int.equal n 0 then
    prod
  else
    match kind_of_term prod with
      | Prod (na,ty,bd) -> mkLambda (na,ty,to_lambda (n-1) bd)
      | Cast (c,_,_) -> to_lambda n c
      | _   -> user_err ~hdr:"to_lambda" (mt ())

let rec to_prod n lam =
  if Int.equal n 0 then
    lam
  else
    match kind_of_term lam with
      | Lambda (na,ty,bd) -> mkProd (na,ty,to_prod (n-1) bd)
      | Cast (c,_,_) -> to_prod n c
      | _   -> user_err ~hdr:"to_prod" (mt ())

let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)
let it_mkLambda_or_LetIn = List.fold_left (fun c d -> mkLambda_or_LetIn d c)

(* Application with expected on-the-fly reduction *)

let lambda_applist c l =
  let rec app subst c l =
    match kind_of_term c, l with
    | Lambda(_,_,c), arg::l -> app (arg::subst) c l
    | _, [] -> substl subst c
    | _ -> anomaly (Pp.str "Not enough lambda's") in
  app [] c l

let lambda_appvect c v = lambda_applist c (Array.to_list v)

let lambda_applist_assum n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Not enough arguments")
    else match kind_of_term t, l with
    | Lambda(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _ -> anomaly (Pp.str "Not enough lambda/let's") in
  app n [] c l

let lambda_appvect_assum n c v = lambda_applist_assum n c (Array.to_list v)

(* prod_applist T [ a1 ; ... ; an ] -> (T a1 ... an) *)
let prod_applist c l =
  let rec app subst c l =
    match kind_of_term c, l with
    | Prod(_,_,c), arg::l -> app (arg::subst) c l
    | _, [] -> substl subst c
    | _ -> anomaly (Pp.str "Not enough prod's") in
  app [] c l

(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_appvect c v = prod_applist c (Array.to_list v)

let prod_applist_assum n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Not enough arguments")
    else match kind_of_term t, l with
    | Prod(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _ -> anomaly (Pp.str "Not enough prod/let's") in
  app n [] c l

let prod_appvect_assum n c v = prod_applist_assum n c (Array.to_list v)

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
    if Int.equal n 0 then l,c
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
    if Int.equal n 0 then l,c
    else match kind_of_term c with
      | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_)     -> lamdec_rec l n c
      | _ -> error "decompose_lam_n: not enough abstractions"
  in
  lamdec_rec [] n

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod_assum =
  let open Context.Rel.Declaration in
  let rec prodec_rec l c =
    match kind_of_term c with
    | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)      -> prodec_rec l c
    | _               -> l,c
  in
  prodec_rec Context.Rel.empty

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam_assum =
  let rec lamdec_rec l c =
    let open Context.Rel.Declaration in
    match kind_of_term c with
    | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)      -> lamdec_rec l c
    | _               -> l,c
  in
  lamdec_rec Context.Rel.empty

(* Given a positive integer n, decompose a product or let-in term
   of the form [forall (x1:T1)..(xi:=ci:Ti)..(xn:Tn), T] into the pair
   of the quantifying context [(xn,None,Tn);..;(xi,Some
   ci,Ti);..;(x1,None,T1)] and of the inner type [T]) *)
let decompose_prod_n_assum n =
  if n < 0 then
    error "decompose_prod_n_assum: integer parameter must be positive";
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind_of_term c with
      | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> prodec_rec l n c
      | c -> error "decompose_prod_n_assum: not enough assumptions"
  in
  prodec_rec Context.Rel.empty n

(* Given a positive integer n, decompose a lambda or let-in term [fun
   (x1:T1)..(xi:=ci:Ti)..(xn:Tn) => T] into the pair of the abstracted
   context [(xn,None,Tn);...;(xi,Some ci,Ti);...;(x1,None,T1)] and of
   the inner body [T].
   Lets in between are not expanded but turn into local definitions,
   but n is the actual number of destructurated lambdas. *)
let decompose_lam_n_assum n =
  if n < 0 then
    error "decompose_lam_n_assum: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind_of_term c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) n c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> error "decompose_lam_n_assum: not enough abstractions"
  in
  lamdec_rec Context.Rel.empty n

(* Same, counting let-in *)
let decompose_lam_n_decls n =
  if n < 0 then
    error "decompose_lam_n_decls: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind_of_term c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> error "decompose_lam_n_decls: not enough abstractions"
  in
  lamdec_rec Context.Rel.empty n

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

type arity = Context.Rel.t * sorts

let destArity =
  let open Context.Rel.Declaration in
  let rec prodec_rec l c =
    match kind_of_term c with
    | Prod (x,t,c)    -> prodec_rec (LocalAssum (x,t) :: l) c
    | LetIn (x,b,t,c) -> prodec_rec (LocalDef (x,b,t) :: l) c
    | Cast (c,_,_)      -> prodec_rec l c
    | Sort s          -> l,s
    | _               -> anomaly ~label:"destArity" (Pp.str "not an arity")
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

(** Kind of type *)

(* Experimental, used in Presburger contrib *)
type ('constr, 'types) kind_of_type =
  | SortType   of sorts
  | CastType   of 'types * 'types
  | ProdType   of Name.t * 'types * 'types
  | LetInType  of Name.t * 'constr * 'types * 'types
  | AtomicType of 'constr * 'constr array

let kind_of_type t = match kind_of_term t with
  | Sort s -> SortType s
  | Cast (c,_,t) -> CastType (c, t)
  | Prod (na,t,c) -> ProdType (na, t, c)
  | LetIn (na,b,t,c) -> LetInType (na, b, t, c)
  | App (c,l) -> AtomicType (c, l)
  | (Rel _ | Meta _ | Var _ | Evar _ | Const _ 
  | Proj _ | Case _ | Fix _ | CoFix _ | Ind _)
    -> AtomicType (t,[||])
  | (Lambda _ | Construct _) -> failwith "Not a type"
