(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module instantiates the structure of generic de Bruijn terms to Coq *)

open CErrors
open Util
open Names
open Esubst

open Cic

(* Sorts. *)

let family_of_sort = function
  | Prop -> InProp
  | Set -> InSet
  | Type _ -> InType

let family_equal = (==)

let sort_of_univ u =
  if Univ.is_type0m_univ u then Prop
  else if Univ.is_type0_univ u then Set
  else Type u

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

let rec strip_outer_cast c = match c with
  | Cast (c,_,_) -> strip_outer_cast c
  | _ -> c

let collapse_appl c = match c with
  | App (f,cl) ->
      let rec collapse_rec f cl2 =
        match (strip_outer_cast f) with
	| App (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
	| _ -> App (f,cl2)
      in
      collapse_rec f cl
  | _ -> c

let decompose_app c =
  match collapse_appl c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])


let applist (f,l) = App (f, Array.of_list l)


(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(*********************)
(*     Occurring     *)
(*********************)

let iter_constr_with_binders g f n c = match c with
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
  | Proj (p, c) -> f n c

exception LocalOccur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn n c =
  let rec closed_rec n c = match c with
    | Rel m -> if m>n then raise LocalOccur
    | _ -> iter_constr_with_binders succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

(* [closed0 M] is true iff [M] is a (de Bruijn) closed term *)

let closed0 = closedn 0

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term =
  let rec occur_rec n c = match c with
    | Rel m -> if Int.equal m n then raise LocalOccur
    | _ -> iter_constr_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M
  for n <= p < n+m *)

let noccur_between n m term =
  let rec occur_rec n c = match c with
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
  let rec occur_rec n c = match c with
    | Rel p -> if n<=p && p<n+m then raise LocalOccur
    | App(f,cl) ->
	(match f with
           | (Cast (Meta _,_,_)| Meta _) -> ()
	   | _ -> iter_constr_with_binders succ occur_rec n c)
    | Evar (_, _) -> ()
    | _ -> iter_constr_with_binders succ occur_rec n c
  in
  try (occur_rec n term; true) with LocalOccur -> false


(*********************)
(*      Lifting      *)
(*********************)

let map_constr_with_binders g f l c = match c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,k,t) -> Cast (f l c, k, f l t)
  | Prod (na,t,c) -> Prod (na, f l t, f (g l) c)
  | Lambda (na,t,c) -> Lambda (na, f l t, f (g l) c)
  | LetIn (na,b,t,c) -> LetIn (na, f l b, f l t, f (g l) c)
  | App (c,al) -> App (f l c, Array.map (f l) al)
  | Evar (e,al) -> Evar (e, Array.map (f l) al)
  | Case (ci,p,c,bl) -> Case (ci, f l p, f l c, Array.map (f l) bl)
  | Fix (ln,(lna,tl,bl)) ->
      let l' = iterate g (Array.length tl) l in
      Fix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | CoFix(ln,(lna,tl,bl)) ->
      let l' = iterate g (Array.length tl) l in
      CoFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | Proj (p, c) -> Proj (p, f l c)

(* The generic lifting function *)
let rec exliftn el c = match c with
  | Rel i -> Rel(reloc_rel i el)
  | _ -> map_constr_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn k n =
  match el_liftn (pred n) (el_shft k el_id) with
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
  if Int.equal lv 0 then c
  else
    let rec substrec depth c = match c with
      | Rel k     ->
          if k<=depth then c
          else if k-depth <= lv then lift_substituend depth lamv.(k-depth-1)
          else Rel (k-lv)
      | _ -> map_constr_with_binders succ substrec depth c in
    substrec n c

let substnl laml n =
  substn_many (Array.map make_substituend (Array.of_list laml)) n
let substl laml = substnl laml 0
let subst1 lam = substl [lam]


(***************************************************************************)
(*     Type of assumptions and contexts                                    *)
(***************************************************************************)

let empty_rel_context = []
let rel_context_length = List.length
let rel_context_nhyps hyps =
  let rec nhyps acc = function
    | [] -> acc
    | LocalAssum _ :: hyps -> nhyps (1+acc) hyps
    | LocalDef _ :: hyps -> nhyps acc hyps in
  nhyps 0 hyps
let fold_rel_context f l ~init = List.fold_right f l init

let fold_rel_context_outside f l ~init = List.fold_right f l init

let map_rel_decl f = function
  | LocalAssum (n, typ) as decl ->
     let typ' = f typ in
     if typ' == typ then decl else
       LocalAssum (n, typ')
  | LocalDef (n, body, typ) as decl ->
     let body' = f body in
     let typ' = f typ in
     if body' == body && typ' == typ then decl else
       LocalDef (n, body', typ')

let map_rel_context f =
  List.Smart.map (map_rel_decl f)

let extended_rel_list n hyps =
  let rec reln l p = function
    | LocalAssum _ :: hyps -> reln (Rel (n+p) :: l) (p+1) hyps
    | LocalDef _ :: hyps -> reln l (p+1) hyps
    | [] -> l
  in
  reln [] 1 hyps

(* Iterate lambda abstractions *)

(* compose_lam [xn:Tn;..;x1:T1] b = [x1:T1]..[xn:Tn]b *)
let compose_lam l b =
  let rec lamrec = function
    | ([], b)       -> b
    | ((v,t)::l, b) -> lamrec (l, Lambda (v,t,b))
  in
  lamrec (l,b)

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam =
  let rec lamdec_rec l c = match c with
    | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | Cast (c,_,_)     -> lamdec_rec l c
    | _                -> l,c
  in
  lamdec_rec []

(* Decompose lambda abstractions and lets, until finding n
  abstractions *)
let decompose_lam_n_assum n =
  if n < 0 then
    user_err Pp.(str "decompose_lam_n_assum: integer parameter must be positive");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else match c with
    | Lambda (x,t,c)  -> lamdec_rec (LocalAssum (x,t) :: l) (n-1) c
    | LetIn (x,b,t,c) -> lamdec_rec (LocalDef (x,b,t) :: l) n c
    | Cast (c,_,_)      -> lamdec_rec l n c
    | c -> user_err Pp.(str "decompose_lam_n_assum: not enough abstractions")
  in
  lamdec_rec empty_rel_context n

(* Iterate products, with or without lets *)

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
let mkProd_or_LetIn decl c =
  match decl with
    | LocalAssum (na,t) -> Prod (na, t, c)
    | LocalDef (na,b,t) -> LetIn (na, b, t, c)

let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)

let decompose_prod_assum =
  let rec prodec_rec l c =
    match c with
    | Prod (x,t,c)    -> prodec_rec (LocalAssum (x,t) :: l) c
    | LetIn (x,b,t,c) -> prodec_rec (LocalDef (x,b,t) :: l) c
    | Cast (c,_,_)    -> prodec_rec l c
    | _               -> l,c
  in
  prodec_rec empty_rel_context

let decompose_prod_n_assum n =
  if n < 0 then
    user_err Pp.(str "decompose_prod_n_assum: integer parameter must be positive");
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else match c with
    | Prod (x,t,c)    -> prodec_rec (LocalAssum (x,t) :: l) (n-1) c
    | LetIn (x,b,t,c) -> prodec_rec (LocalDef (x,b,t) :: l) (n-1) c
    | Cast (c,_,_)    -> prodec_rec l n c
    | c -> user_err Pp.(str "decompose_prod_n_assum: not enough assumptions")
  in
  prodec_rec empty_rel_context n


(***************************)
(* Other term constructors *)
(***************************)

type arity = rel_context * sorts

let mkArity (sign,s) = it_mkProd_or_LetIn (Sort s) sign

let destArity =
  let rec prodec_rec l c =
    match c with
    | Prod (x,t,c)    -> prodec_rec (LocalAssum (x,t)::l) c
    | LetIn (x,b,t,c) -> prodec_rec (LocalDef (x,b,t)::l) c
    | Cast (c,_,_)    -> prodec_rec l c
    | Sort s          -> l,s
    | _               -> anomaly ~label:"destArity" (Pp.str "not an arity.")
  in
  prodec_rec []

let rec isArity c =
  match c with
  | Prod (_,_,c)    -> isArity c
  | LetIn (_,b,_,c) -> isArity (subst1 b c)
  | Cast (c,_,_)    -> isArity c
  | Sort _          -> true
  | _               -> false

(*******************************)
(*  alpha conversion functions *)
(*******************************)

(* alpha conversion : ignore print names and casts *)

let compare_sorts s1 s2 = match s1, s2 with
| Prop, Prop | Set, Set -> true
| Type u1, Type u2 -> Univ.Universe.equal u1 u2
| Prop, Set | Set, Prop -> false
| (Prop | Set), Type _ -> false
| Type _, (Prop | Set) -> false

let eq_puniverses f (c1,u1) (c2,u2) =
  Univ.Instance.equal u1 u2 && f c1 c2

let compare_constr f t1 t2 =
  match t1, t2 with
  | Rel n1, Rel n2 -> Int.equal n1 n2
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Sort s1, Sort s2 -> compare_sorts s1 s2
  | Cast (c1,_,_), _ -> f c1 t2
  | _, Cast (c2,_,_) -> f t1 c2
  | Prod (_,t1,c1), Prod (_,t2,c2) -> f t1 t2 && f c1 c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) -> f t1 t2 && f c1 c2
  | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> f b1 b2 && f t1 t2 && f c1 c2
  | App (c1,l1), App (c2,l2) ->
      if Int.equal (Array.length l1) (Array.length l2) then
        f c1 c2 && Array.for_all2 f l1 l2
      else
        let (h1,l1) = decompose_app t1 in
        let (h2,l2) = decompose_app t2 in
        if Int.equal (List.length l1) (List.length l2) then
          f h1 h2 && List.for_all2 f l1 l2
        else false
  | Evar (e1,l1), Evar (e2,l2) -> Int.equal e1 e2 && Array.equal f l1 l2
  | Const c1, Const c2 -> eq_puniverses Constant.UserOrd.equal c1 c2
  | Ind c1, Ind c2 -> eq_puniverses eq_ind_chk c1 c2
  | Construct ((c1,i1),u1), Construct ((c2,i2),u2) -> Int.equal i1 i2 && eq_ind_chk c1 c2
    && Univ.Instance.equal u1 u2
  | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
      f p1 p2 && f c1 c2 && Array.equal f bl1 bl2
  | Fix ((ln1, i1),(_,tl1,bl1)), Fix ((ln2, i2),(_,tl2,bl2)) ->
      Int.equal i1 i2 && Array.equal Int.equal ln1 ln2 &&
      Array.equal f tl1 tl2 && Array.equal f bl1 bl2
  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      Int.equal ln1 ln2 && Array.equal f tl1 tl2 && Array.equal f bl1 bl2
  | Proj (p1,c1), Proj(p2,c2) -> Projection.equal p1 p2 && f c1 c2
  | _ -> false

let rec eq_constr m n =
  (m == n) ||
  compare_constr eq_constr m n

let eq_constr m n = eq_constr m n (* to avoid tracing a recursive fun *)

(* Universe substitutions *)

let map_constr f c = map_constr_with_binders (fun x -> x) (fun _ c -> f c) 0 c

let subst_instance_constr subst c =
  if Univ.Instance.is_empty subst then c
  else
    let f u = Univ.subst_instance_instance subst u in
    let rec aux t =
      match t with
      | Const (c, u) ->
       if Univ.Instance.is_empty u then t
       else
          let u' = f u in
           if u' == u then t
           else (Const (c, u'))
      | Ind (i, u) ->
       if Univ.Instance.is_empty u then t
       else
         let u' = f u in
           if u' == u then t
           else (Ind (i, u'))
      | Construct (c, u) ->
       if Univ.Instance.is_empty u then t
       else
          let u' = f u in
           if u' == u then t
           else (Construct (c, u'))
      | Sort (Type u) ->
         let u' = Univ.subst_instance_universe subst u in
          if u' == u then t else
            (Sort (sort_of_univ u'))
      | _ -> map_constr aux t
    in
    aux c

let subst_instance_context s ctx = 
  if Univ.Instance.is_empty s then ctx
  else map_rel_context (fun x -> subst_instance_constr s x) ctx
