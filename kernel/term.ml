(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors
open Names
open Vars
open Constr

(* Deprecated *)
type sorts_family = Sorts.family = InProp | InSet | InType
[@@ocaml.deprecated "Alias for Sorts.family"]

type sorts = Sorts.t =
  | Prop | Set
  | Type of Univ.Universe.t  (** Type *)
[@@ocaml.deprecated "Alias for Sorts.t"]

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
    match kind prod with
      | Prod (na,ty,bd) -> mkLambda (na,ty,to_lambda (n-1) bd)
      | Cast (c,_,_) -> to_lambda n c
      | _   -> user_err ~hdr:"to_lambda" (mt ())

let rec to_prod n lam =
  if Int.equal n 0 then
    lam
  else
    match kind lam with
      | Lambda (na,ty,bd) -> mkProd (na,ty,to_prod (n-1) bd)
      | Cast (c,_,_) -> to_prod n c
      | _   -> user_err ~hdr:"to_prod" (mt ())

let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)
let it_mkLambda_or_LetIn = List.fold_left (fun c d -> mkLambda_or_LetIn d c)

(* Application with expected on-the-fly reduction *)

let lambda_applist c l =
  let rec app subst c l =
    match kind c, l with
    | Lambda(_,_,c), arg::l -> app (arg::subst) c l
    | _, [] -> substl subst c
    | _ -> anomaly (Pp.str "Not enough lambda's.") in
  app [] c l

let lambda_appvect c v = lambda_applist c (Array.to_list v)

let lambda_applist_assum n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Too many arguments.")
    else match kind t, l with
    | Lambda(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _, [] -> anomaly (Pp.str "Not enough arguments.")
    | _ -> anomaly (Pp.str "Not enough lambda/let's.") in
  app n [] c l

let lambda_appvect_assum n c v = lambda_applist_assum n c (Array.to_list v)

(* prod_applist T [ a1 ; ... ; an ] -> (T a1 ... an) *)
let prod_applist c l =
  let rec app subst c l =
    match kind c, l with
    | Prod(_,_,c), arg::l -> app (arg::subst) c l
    | _, [] -> substl subst c
    | _ -> anomaly (Pp.str "Not enough prod's.") in
  app [] c l

(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_appvect c v = prod_applist c (Array.to_list v)

let prod_applist_assum n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Too many arguments.")
    else match kind t, l with
    | Prod(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _, [] -> anomaly (Pp.str "Not enough arguments.")
    | _ -> anomaly (Pp.str "Not enough prod/let's.") in
  app n [] c l

let prod_appvect_assum n c v = prod_applist_assum n c (Array.to_list v)

(*********************************)
(* Other term destructors        *)
(*********************************)

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod =
  let rec prodec_rec l c = match kind c with
    | Prod (x,t,c) -> prodec_rec ((x,t)::l) c
    | Cast (c,_,_)   -> prodec_rec l c
    | _              -> l,c
  in
  prodec_rec []

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam =
  let rec lamdec_rec l c = match kind c with
    | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | Cast (c,_,_)     -> lamdec_rec l c
    | _                -> l,c
  in
  lamdec_rec []

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n n =
  if n < 0 then user_err (str "decompose_prod_n: integer parameter must be positive");
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else match kind c with
      | Prod (x,t,c) -> prodec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_)   -> prodec_rec l n c
      | _ -> user_err (str "decompose_prod_n: not enough products")
  in
  prodec_rec [] n

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n n =
  if n < 0 then user_err (str "decompose_lam_n: integer parameter must be positive");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else match kind c with
      | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_)     -> lamdec_rec l n c
      | _ -> user_err (str "decompose_lam_n: not enough abstractions")
  in
  lamdec_rec [] n

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod_assum =
  let open Context.Rel.Declaration in
  let rec prodec_rec l c =
    match kind c with
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
    match kind c with
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
    user_err (str "decompose_prod_n_assum: integer parameter must be positive");
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind c with
      | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> prodec_rec l n c
      | c -> user_err (str  "decompose_prod_n_assum: not enough assumptions")
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
    user_err (str  "decompose_lam_n_assum: integer parameter must be positive");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) n c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> user_err (str "decompose_lam_n_assum: not enough abstractions")
  in
  lamdec_rec Context.Rel.empty n

(* Same, counting let-in *)
let decompose_lam_n_decls n =
  if n < 0 then
    user_err (str "decompose_lam_n_decls: integer parameter must be positive");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> user_err (str "decompose_lam_n_decls: not enough abstractions")
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

type arity = Constr.rel_context * Sorts.t

let destArity =
  let open Context.Rel.Declaration in
  let rec prodec_rec l c =
    match kind c with
    | Prod (x,t,c)    -> prodec_rec (LocalAssum (x,t) :: l) c
    | LetIn (x,b,t,c) -> prodec_rec (LocalDef (x,b,t) :: l) c
    | Cast (c,_,_)      -> prodec_rec l c
    | Sort s          -> l,s
    | _               -> anomaly ~label:"destArity" (Pp.str "not an arity.")
  in
  prodec_rec []

let mkArity (sign,s) = it_mkProd_or_LetIn (mkSort s) sign

let rec isArity c =
  match kind c with
  | Prod (_,_,c)    -> isArity c
  | LetIn (_,b,_,c) -> isArity (subst1 b c)
  | Cast (c,_,_)      -> isArity c
  | Sort _          -> true
  | _               -> false

(** Kind of type *)

(* Experimental, used in Presburger contrib *)
type ('constr, 'types) kind_of_type =
  | SortType   of Sorts.t
  | CastType   of 'types * 'types
  | ProdType   of Name.t * 'types * 'types
  | LetInType  of Name.t * 'constr * 'types * 'types
  | AtomicType of 'constr * 'constr array

let kind_of_type t = match kind t with
  | Sort s -> SortType s
  | Cast (c,_,t) -> CastType (c, t)
  | Prod (na,t,c) -> ProdType (na, t, c)
  | LetIn (na,b,t,c) -> LetInType (na, b, t, c)
  | App (c,l) -> AtomicType (c, l)
  | (Rel _ | Meta _ | Var _ | Evar _ | Const _ 
  | Proj _ | Case _ | Fix _ | CoFix _ | Ind _)
    -> AtomicType (t,[||])
  | (Lambda _ | Construct _) -> failwith "Not a type"
