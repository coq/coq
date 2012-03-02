(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This module instantiates the structure of generic deBruijn terms to Coq *)

open Errors
open Util
open Pp
open Names
open Univ
open Esubst
open Validate

(* Coq abstract syntax with deBruijn variables; 'a is the type of sorts *)

type existential_key = int
type metavariable = int

(* This defines the strategy to use for verifiying a Cast *)

(* This defines Cases annotations *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle |
  RegularStyle
type case_printing =
  { ind_nargs : int; (* length of the arity of the inductive type *)
    style     : case_style }
type case_info =
  { ci_ind         : inductive;
    ci_npar        : int;
    ci_cstr_ndecls : int array; (* number of pattern var of each constructor *)
    ci_pp_info     : case_printing (* not interpreted by the kernel *)
  }
let val_ci =
  let val_cstyle = val_enum "case_style" 5 in
  let val_cprint = val_tuple ~name:"case_printing" [|val_int;val_cstyle|] in
  val_tuple ~name:"case_info" [|val_ind;val_int;val_array val_int;val_cprint|]

(* Sorts. *)

type contents = Pos | Null

type sorts =
  | Prop of contents                      (* proposition types *)
  | Type of universe

type sorts_family = InProp | InSet | InType

let family_of_sort = function
  | Prop Null -> InProp
  | Prop Pos -> InSet
  | Type _ -> InType

let val_sort = val_sum "sort" 0 [|[|val_enum "cnt" 2|];[|val_univ|]|]
let val_sortfam = val_enum "sorts_family" 3

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr array
type 'constr prec_declaration =
    name array * 'constr array * 'constr array
type 'constr pfixpoint =
    (int array * int) * 'constr prec_declaration
type 'constr pcofixpoint =
    int * 'constr prec_declaration

let val_evar f = val_tuple ~name:"pexistential" [|val_int;val_array f|]
let val_prec f =
  val_tuple ~name:"prec_declaration"
    [|val_array val_name; val_array f; val_array f|]
let val_fix f =
  val_tuple ~name:"pfixpoint"
    [|val_tuple~name:"fix2"[|val_array val_int;val_int|];val_prec f|]
let val_cofix f = val_tuple ~name:"pcofixpoint"[|val_int;val_prec f|]

type cast_kind = VMcast | DEFAULTcast
let val_cast = val_enum "cast_kind" 2

(*s*******************************************************************)
(* The type of constructions *)

type constr =
  | Rel       of int
  | Var       of identifier
  | Meta      of metavariable
  | Evar      of constr pexistential
  | Sort      of sorts
  | Cast      of constr * cast_kind * constr
  | Prod      of name * constr * constr
  | Lambda    of name * constr * constr
  | LetIn     of name * constr * constr * constr
  | App       of constr * constr array
  | Const     of constant
  | Ind       of inductive
  | Construct of constructor
  | Case      of case_info * constr * constr * constr array
  | Fix       of constr pfixpoint
  | CoFix     of constr pcofixpoint

let val_constr = val_rec_sum "constr" 0 (fun val_constr -> [|
  [|val_int|]; (* Rel *)
  [|val_id|]; (* Var *)
  [|val_int|]; (* Meta *)
  [|val_evar val_constr|]; (* Evar *)
  [|val_sort|]; (* Sort *)
  [|val_constr;val_cast;val_constr|]; (* Cast *)
  [|val_name;val_constr;val_constr|]; (* Prod *)
  [|val_name;val_constr;val_constr|]; (* Lambda *)
  [|val_name;val_constr;val_constr;val_constr|]; (* LetIn *)
  [|val_constr;val_array val_constr|]; (* App *)
  [|val_con|]; (* Const *)
  [|val_ind|]; (* Ind *)
  [|val_cstr|]; (* Construct *)
  [|val_ci;val_constr;val_constr;val_array val_constr|]; (* Case *)
  [|val_fix val_constr|]; (* Fix *)
  [|val_cofix val_constr|] (* CoFix *)
|])

type existential = constr pexistential
type rec_declaration = constr prec_declaration
type fixpoint = constr pfixpoint
type cofixpoint = constr pcofixpoint


let rec strip_outer_cast c = match c with
  | Cast (c,_,_) -> strip_outer_cast c
  | _ -> c

let rec collapse_appl c = match c with
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

exception LocalOccur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn n c =
  let rec closed_rec n c = match c with
    | Rel m -> if m>n then raise LocalOccur
    | _ -> iter_constr_with_binders succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)

let closed0 = closedn 0

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term =
  let rec occur_rec n c = match c with
    | Rel m -> if m = n then raise LocalOccur
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
    | Rel p -> if n<=p & p<n+m then raise LocalOccur
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
  if lv = 0 then c
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

let val_ndecl =
  val_tuple ~name:"named_declaration"[|val_id;val_opt val_constr;val_constr|]
let val_rdecl =
  val_tuple ~name:"rel_declaration"[|val_name;val_opt val_constr;val_constr|]
let val_nctxt = val_list val_ndecl
let val_rctxt = val_list val_rdecl

type named_declaration = identifier * constr option * constr
type rel_declaration = name * constr option * constr

type named_context = named_declaration list
let empty_named_context = []
let fold_named_context f l ~init = List.fold_right f l init

type section_context = named_context

type rel_context = rel_declaration list
let empty_rel_context = []
let rel_context_length = List.length
let rel_context_nhyps hyps =
  let rec nhyps acc = function
    | [] -> acc
    | (_,None,_)::hyps -> nhyps (1+acc) hyps
    | (_,Some _,_)::hyps -> nhyps acc hyps in
  nhyps 0 hyps
let fold_rel_context f l ~init = List.fold_right f l init

let map_context f l =
  let map_decl (n, body_o, typ as decl) =
    let body_o' = Option.smartmap f body_o in
    let typ' = f typ in
      if body_o' == body_o && typ' == typ then decl else
	(n, body_o', typ')
  in
    list_smartmap map_decl l

let map_rel_context = map_context

let extended_rel_list n hyps =
  let rec reln l p = function
    | (_,None,_) :: hyps -> reln (Rel (n+p) :: l) (p+1) hyps
    | (_,Some _,_) :: hyps -> reln l (p+1) hyps
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
    error "decompose_lam_n_assum: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if n=0 then l,c
    else match c with
    | Lambda (x,t,c)  -> lamdec_rec ((x,None,t) :: l) (n-1) c
    | LetIn (x,b,t,c) -> lamdec_rec ((x,Some b,t) :: l) n c
    | Cast (c,_,_)      -> lamdec_rec l n c
    | c -> error "decompose_lam_n_assum: not enough abstractions"
  in
  lamdec_rec empty_rel_context n

(* Iterate products, with or without lets *)

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
let mkProd_or_LetIn (na,body,t) c =
  match body with
    | None -> Prod (na, t, c)
    | Some b -> LetIn (na, b, t, c)

let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)

let decompose_prod_assum =
  let rec prodec_rec l c =
    match c with
    | Prod (x,t,c)    -> prodec_rec ((x,None,t) :: l) c
    | LetIn (x,b,t,c) -> prodec_rec ((x,Some b,t) :: l) c
    | Cast (c,_,_)    -> prodec_rec l c
    | _               -> l,c
  in
  prodec_rec empty_rel_context

let decompose_prod_n_assum n =
  if n < 0 then
    error "decompose_prod_n_assum: integer parameter must be positive";
  let rec prodec_rec l n c =
    if n=0 then l,c
    else match c with
    | Prod (x,t,c)    -> prodec_rec ((x,None,t) :: l) (n-1) c
    | LetIn (x,b,t,c) -> prodec_rec ((x,Some b,t) :: l) (n-1) c
    | Cast (c,_,_)    -> prodec_rec l n c
    | c -> error "decompose_prod_n_assum: not enough assumptions"
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
    | Prod (x,t,c)    -> prodec_rec ((x,None,t)::l) c
    | LetIn (x,b,t,c) -> prodec_rec ((x,Some b,t)::l) c
    | Cast (c,_,_)    -> prodec_rec l c
    | Sort s          -> l,s
    | _               -> anomaly "destArity: not an arity"
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

let compare_constr f t1 t2 =
  match t1, t2 with
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
  | Const c1, Const c2 -> eq_con_chk c1 c2
  | Ind c1, Ind c2 -> eq_ind_chk c1 c2
  | Construct (c1,i1), Construct (c2,i2) -> i1=i2 && eq_ind_chk c1 c2
  | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
      f p1 p2 & f c1 c2 & array_for_all2 f bl1 bl2
  | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
      ln1 = ln2 & array_for_all2 f tl1 tl2 & array_for_all2 f bl1 bl2
  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      ln1 = ln2 & array_for_all2 f tl1 tl2 & array_for_all2 f bl1 bl2
  | _ -> false

let rec eq_constr m n =
  (m==n) or
  compare_constr eq_constr m n

let eq_constr m n = eq_constr m n (* to avoid tracing a recursive fun *)
