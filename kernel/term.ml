(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Context

(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(***************************)
(* Other term constructors *)
(***************************)

let name_annot = map_annot Name.mk_name

let mkNamedProd id typ c = mkProd (name_annot id, typ, subst_var id.binder_name c)
let mkNamedLambda id typ c = mkLambda (name_annot id, typ, subst_var id.binder_name c)
let mkNamedLetIn id c1 t c2 = mkLetIn (name_annot id, c1, t, subst_var id.binder_name c2)

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
  | LocalDef (_na,b,_t) -> subst1 b c

let mkNamedProd_wo_LetIn decl c =
  let open Context.Named.Declaration in
  match decl with
    | LocalAssum (id,t) -> mkNamedProd id t c
    | LocalDef (id,b,_) -> subst1 b (subst_var id.binder_name c)

(* non-dependent product t1 -> t2 *)
let mkArrow t1 r t2 = mkProd (make_annot Anonymous r, t1, t2)
let mkArrowR t1 t2 = mkArrow t1 Sorts.Relevant t2

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
    | (0, _env, b)        -> b
    | (n, ((v,t)::l), b) -> prodrec (n-1,  l, mkProd (v,t,b))
    | _ -> assert false
  in
  prodrec (n,env,b)

(* compose_prod [xn:Tn;..;x1:T1] b = (x1:T1)..(xn:Tn)b *)
let compose_prod l b = prodn (List.length l) l b

(* lamn n [xn:Tn;..;x1:T1;Gamma] b = [x1:T1]..[xn:Tn]b *)
let lamn n env b =
  let rec lamrec = function
    | (0, _env, b)        -> b
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
      | _   -> anomaly Pp.(str "Not enough lambda's.")

let rec to_prod n lam =
  if Int.equal n 0 then
    lam
  else
    match kind lam with
      | Lambda (na,ty,bd) -> mkProd (na,ty,to_prod (n-1) bd)
      | Cast (c,_,_) -> to_prod n c
      | _   -> anomaly Pp.(str "Not enough prod's.")

let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)
let it_mkProd_wo_LetIn   = List.fold_left (fun c d -> mkProd_wo_LetIn d c)
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

let lambda_applist_decls n c l =
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

let lambda_appvect_decls n c v = lambda_applist_decls n c (Array.to_list v)

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

let prod_applist_decls n c l =
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

let prod_appvect_decls n c v = prod_applist_decls n c (Array.to_list v)

(*********************************)
(* Other term destructors        *)
(*********************************)

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod =
  let rec prodec_rec l c = match kind c with
    | Prod (x,t,c) -> prodec_rec ((x,t)::l) c
    | Cast (c,_,_) -> prodec_rec l c
    | _            -> l,c
  in
  prodec_rec []

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lambda =
  let rec lamdec_rec l c = match kind c with
    | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | Cast (c,_,_)   -> lamdec_rec l c
    | _              -> l,c
  in
  lamdec_rec []

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n n =
  if n < 0 then anomaly (str "decompose_prod_n: integer parameter must be positive.");
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else match kind c with
      | Prod (x,t,c) -> prodec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_) -> prodec_rec l n c
      | _ -> anomaly (str "decompose_prod_n: not enough products.")
  in
  prodec_rec [] n

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lambda_n n =
  if n < 0 then anomaly (str "decompose_lambda_n: integer parameter must be positive.");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else match kind c with
      | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_)   -> lamdec_rec l n c
      | _ -> anomaly (str "decompose_lambda_n: not enough abstractions.")
  in
  lamdec_rec [] n

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod_decls =
  let open Context.Rel.Declaration in
  let rec prodec_rec l c =
    match kind c with
    | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)    -> prodec_rec l c
    | _               -> l,c
  in
  prodec_rec Context.Rel.empty

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lambda_decls =
  let rec lamdec_rec l c =
    let open Context.Rel.Declaration in
    match kind c with
    | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)    -> lamdec_rec l c
    | _               -> l,c
  in
  lamdec_rec Context.Rel.empty

(* Given a positive integer n, decompose a product or let-in term
   of the form [forall (x1:T1)..(xi:=ci:Ti)..(xn:Tn), T] into the pair
   of the quantifying context [(xn,None,Tn);..;(xi,Some
   ci,Ti);..;(x1,None,T1)] and of the inner type [T]) *)
let decompose_prod_n_decls n =
  if n < 0 then
    anomaly (str "decompose_prod_n_decls: integer parameter must be positive.");
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind c with
      | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)    -> prodec_rec l n c
      | _ -> anomaly (str  "decompose_prod_n_decls: not enough declarations.")
  in
  prodec_rec Context.Rel.empty n

let decompose_lambda_prod_n_decls n =
  if n < 0 then
    anomaly (str "decompose_lambda_prod_n_decls: integer parameter must be positive.");
  let rec lamprodec_rec l n c t =
    if Int.equal n 0 then (l, c, t)
    else
      let open Context.Rel.Declaration in
      match kind c, kind t with
      | Lambda (na, u, c), Prod (_, _, t) -> lamprodec_rec (LocalAssum (na, u) :: l) (n-1) c t
      | LetIn (na, b, u, c), LetIn (_, _, _, t) -> lamprodec_rec (LocalDef (na, b, u) :: l) (n-1) c t
      | _ -> anomaly (str "decompose_lambda_prod_n_decls: not same form.")
  in
  lamprodec_rec Context.Rel.empty n

(** Given a positive integer n, decompose a lambda term [fun
   (x1:T1)..(xn:Tn) => T] (possibly with let-ins before xn) into the pair of the
   abstracted context [(xn,None,Tn);...;(x1,None,T1)] and of the inner body [T]. *)
let decompose_lambda_n_assum n =
  if n < 0 then
    anomaly (str "decompose_lambda_n_assum: integer parameter must be positive.");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) n c
      | Cast (c,_,_)    -> lamdec_rec l n c
      | _c -> anomaly (str "decompose_lambda_n_assum: not enough abstractions.")
  in
  lamdec_rec Context.Rel.empty n

(* Given a positive integer n, decompose a lambda or let-in term [fun
   (x1:T1)..(xi:=ci:Ti)..(xn:Tn) => T] into the pair of the abstracted
   context [(xn,None,Tn);...;(xi,Some ci,Ti);...;(x1,None,T1)] and of
   the inner body [T].
   Lets in between are not expanded but turn into local definitions,
   and n is the number of lambdas and lets to decompose. *)
let decompose_lambda_n_decls n =
  if n < 0 then
    anomaly (str "decompose_lambda_n_decls: integer parameter must be positive.");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      let open Context.Rel.Declaration in
      match kind c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)    -> lamdec_rec l n c
      | _ -> anomaly (str "decompose_lambda_n_decls: not enough declarations.")
  in
  lamdec_rec Context.Rel.empty n

let prod_decls t = fst (decompose_prod_decls t)
let prod_n_decls n t = fst (decompose_prod_n_decls n t)
let strip_prod_decls t = snd (decompose_prod_decls t)
let strip_prod t = snd (decompose_prod t)
let strip_prod_n n t = snd (decompose_prod_n n t)
let lambda_decls t = fst (decompose_lambda_decls t)
let lam_n_assum n t = fst (decompose_lambda_n_assum n t)
let strip_lambda_decls t = snd (decompose_lambda_decls t)
let strip_lam t = snd (decompose_lambda t)
let strip_lam_n n t = snd (decompose_lambda_n n t)

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
    | Cast (c,_,_)    -> prodec_rec l c
    | Sort s          -> l,s
    | _               -> anomaly ~label:"destArity" (Pp.str "not an arity.")
  in
  prodec_rec []

let mkArity (sign,s) = it_mkProd_or_LetIn (mkSort s) sign

let rec isArity c =
  match kind c with
  | Prod (_,_,c)    -> isArity c
  | LetIn (_,_,_,c) -> isArity c
  | Cast (c,_,_)      -> isArity c
  | Sort _          -> true
  | _               -> false

(* Deprecated *)

let decompose_prod_assum = decompose_prod_decls
let decompose_lam_assum = decompose_lambda_decls
let decompose_prod_n_assum = decompose_prod_n_decls
let prod_assum = prod_decls
let lam_assum = lambda_decls
let prod_n_assum = prod_n_decls
let strip_prod_assum = strip_prod_decls
let strip_lam_assum = strip_lambda_decls
let decompose_lam = decompose_lambda
let decompose_lam_n = decompose_lambda_n
let decompose_lam_n_assum = decompose_lambda_n_assum
let decompose_lam_n_decls = decompose_lambda_n_decls

type sorts_family = Sorts.family = InSProp | InProp | InSet | InType | InQSort

type sorts = Sorts.t = private
  | SProp | Prop | Set
  | Type of Univ.Universe.t  (** Type *)
  | QSort of Sorts.QVar.t * Univ.Universe.t
