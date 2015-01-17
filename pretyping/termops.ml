(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Vars
open Context
open Environ
open Locus

(* Sorts and sort family *)

let print_sort = function
  | Prop Pos -> (str "Set")
  | Prop Null -> (str "Prop")
  | Type u -> (str "Type(" ++ Univ.Universe.pr u ++ str ")")

let pr_sort_family = function
  | InSet -> (str "Set")
  | InProp -> (str "Prop")
  | InType -> (str "Type")

let pr_name = function
  | Name id -> pr_id id
  | Anonymous -> str "_"

let pr_con sp = str(string_of_con sp)

let pr_fix pr_constr ((t,i),(lna,tl,bl)) =
  let fixl = Array.mapi (fun i na -> (na,t.(i),tl.(i),bl.(i))) lna in
  hov 1
      (str"fix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,i,ty,bd) ->
           pr_name na ++ str"/" ++ int i ++ str":" ++ pr_constr ty ++
	   cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")

let pr_puniverses p u = 
  if Univ.Instance.is_empty u then p 
  else p ++ str"(*" ++ Univ.Instance.pr Universes.pr_with_global_universes u ++ str"*)"

let rec pr_constr c = match kind_of_term c with
  | Rel n -> str "#"++int n
  | Meta n -> str "Meta(" ++ int n ++ str ")"
  | Var id -> pr_id id
  | Sort s -> print_sort s
  | Cast (c,_, t) -> hov 1
      (str"(" ++ pr_constr c ++ cut() ++
       str":" ++ pr_constr t ++ str")")
  | Prod (Name(id),t,c) -> hov 1
      (str"forall " ++ pr_id id ++ str":" ++ pr_constr t ++ str"," ++
       spc() ++ pr_constr c)
  | Prod (Anonymous,t,c) -> hov 0
      (str"(" ++ pr_constr t ++ str " ->" ++ spc() ++
       pr_constr c ++ str")")
  | Lambda (na,t,c) -> hov 1
      (str"fun " ++ pr_name na ++ str":" ++
       pr_constr t ++ str" =>" ++ spc() ++ pr_constr c)
  | LetIn (na,b,t,c) -> hov 0
      (str"let " ++ pr_name na ++ str":=" ++ pr_constr b ++
       str":" ++ brk(1,2) ++ pr_constr t ++ cut() ++
       pr_constr c)
  | App (c,l) ->  hov 1
      (str"(" ++ pr_constr c ++ spc() ++
       prlist_with_sep spc pr_constr (Array.to_list l) ++ str")")
  | Evar (e,l) -> hov 1
      (str"Evar#" ++ int (Evar.repr e) ++ str"{" ++
       prlist_with_sep spc pr_constr (Array.to_list l) ++str"}")
  | Const (c,u) -> str"Cst(" ++ pr_puniverses (pr_con c) u ++ str")"
  | Ind ((sp,i),u) -> str"Ind(" ++ pr_puniverses (pr_mind sp ++ str"," ++ int i) u ++ str")"
  | Construct (((sp,i),j),u) ->
      str"Constr(" ++ pr_puniverses (pr_mind sp ++ str"," ++ int i ++ str"," ++ int j) u ++ str")"
  | Proj (p,c) -> str"Proj(" ++ pr_con (Projection.constant p) ++ str"," ++ bool (Projection.unfolded p) ++ pr_constr c ++ str")"
  | Case (ci,p,c,bl) -> v 0
      (hv 0 (str"<"++pr_constr p++str">"++ cut() ++ str"Case " ++
             pr_constr c ++ str"of") ++ cut() ++
       prlist_with_sep (fun _ -> brk(1,2)) pr_constr (Array.to_list bl) ++
      cut() ++ str"end")
  | Fix f -> pr_fix pr_constr f
  | CoFix(i,(lna,tl,bl)) ->
      let fixl = Array.mapi (fun i na -> (na,tl.(i),bl.(i))) lna in
      hov 1
        (str"cofix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,ty,bd) ->
           pr_name na ++ str":" ++ pr_constr ty ++
           cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")

let term_printer = ref (fun _ -> pr_constr)
let print_constr_env t = !term_printer t
let print_constr t = !term_printer (Global.env()) t
let set_print_constr f = term_printer := f

let pr_var_decl env (id,c,typ) =
  let pbody = match c with
    | None ->  (mt ())
    | Some c ->
	(* Force evaluation *)
	let pb = print_constr_env env c in
	  (str" := " ++ pb ++ cut () ) in
  let pt = print_constr_env env typ in
  let ptyp = (str" : " ++ pt) in
    (pr_id id ++ hov 0 (pbody ++ ptyp))

let pr_rel_decl env (na,c,typ) =
  let pbody = match c with
    | None -> mt ()
    | Some c ->
	(* Force evaluation *)
	let pb = print_constr_env env c in
	  (str":=" ++ spc () ++ pb ++ spc ()) in
  let ptyp = print_constr_env env typ in
    match na with
      | Anonymous -> hov 0 (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
      | Name id -> hov 0 (pr_id id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)

let print_named_context env =
  hv 0 (fold_named_context
	  (fun env d pps ->
	    pps ++ ws 2 ++ pr_var_decl env d)
          env ~init:(mt ()))

let print_rel_context env =
  hv 0 (fold_rel_context
	  (fun env d pps -> pps ++ ws 2 ++ pr_rel_decl env d)
          env ~init:(mt ()))

let print_env env =
  let sign_env =
    fold_named_context
      (fun env d pps ->
         let pidt =  pr_var_decl env d in
	 (pps ++ fnl () ++ pidt))
      env ~init:(mt ())
  in
  let db_env =
    fold_rel_context
      (fun env d pps ->
         let pnat = pr_rel_decl env d in (pps ++ fnl () ++ pnat))
      env ~init:(mt ())
  in
    (sign_env ++ db_env)

(* [Rel (n+m);...;Rel(n+1)] *)
let rel_vect n m = Array.init m (fun i -> mkRel(n+m-i))

let rel_list n m =
  let rec reln l p =
    if p>m then l else reln (mkRel(n+p)::l) (p+1)
  in
  reln [] 1

(* Same as [rel_list] but takes a context as argument and skips let-ins *)
let extended_rel_list n hyps =
  let rec reln l p = function
    | (_,None,_) :: hyps -> reln (mkRel (n+p) :: l) (p+1) hyps
    | (_,Some _,_) :: hyps -> reln l (p+1) hyps
    | [] -> l
  in
  reln [] 1 hyps

let extended_rel_vect n hyps = Array.of_list (extended_rel_list n hyps)



let push_rel_assum (x,t) env = push_rel (x,None,t) env

let push_rels_assum assums =
  push_rel_context (List.map (fun (x,t) -> (x,None,t)) assums)

let push_named_rec_types (lna,typarray,_) env =
  let ctxt =
    Array.map2_i
      (fun i na t ->
	 match na with
	   | Name id -> (id, None, lift i t)
	   | Anonymous -> anomaly (Pp.str "Fix declarations must be named"))
      lna typarray in
  Array.fold_left
    (fun e assum -> push_named assum e) env ctxt

let lookup_rel_id id sign =
  let rec lookrec n = function
    | []                     -> raise Not_found
    | (Anonymous, _, _) :: l -> lookrec (n + 1) l
    | (Name id', b, t) :: l  ->
      if Names.Id.equal id' id then (n, b, t) else lookrec (n + 1) l
  in
  lookrec 1 sign

(* Constructs either [forall x:t, c] or [let x:=b:t in c] *)
let mkProd_or_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

(* Constructs either [forall x:t, c] or [c] in which [x] is replaced by [b] *)
let mkProd_wo_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na,  t, c)
    | Some b -> subst1 b c

let it_mkProd init = List.fold_left (fun c (n,t)  -> mkProd (n, t, c)) init
let it_mkLambda init = List.fold_left (fun c (n,t)  -> mkLambda (n, t, c)) init

let it_named_context_quantifier f ~init =
  List.fold_left (fun c d -> f d c) init

let it_mkProd_or_LetIn init = it_named_context_quantifier mkProd_or_LetIn ~init
let it_mkProd_wo_LetIn init = it_named_context_quantifier mkProd_wo_LetIn ~init
let it_mkLambda_or_LetIn init = it_named_context_quantifier mkLambda_or_LetIn ~init
let it_mkNamedProd_or_LetIn init = it_named_context_quantifier mkNamedProd_or_LetIn ~init
let it_mkNamedProd_wo_LetIn init = it_named_context_quantifier mkNamedProd_wo_LetIn ~init
let it_mkNamedLambda_or_LetIn init = it_named_context_quantifier mkNamedLambda_or_LetIn ~init

let it_mkLambda_or_LetIn_from_no_LetIn c decls =
  let rec aux k decls c = match decls with
  | [] -> c
  | (na,Some b,t)::decls -> mkLetIn (na,b,t,aux (k-1) decls (liftn 1 k c))
  | (na,None,t)::decls -> mkLambda (na,t,aux (k-1) decls c)
  in aux (List.length decls) (List.rev decls) c

(* *)

(* strips head casts and flattens head applications *)
let rec strip_head_cast c = match kind_of_term c with
  | App (f,cl) ->
      let rec collapse_rec f cl2 = match kind_of_term f with
	| App (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
	| Cast (c,_,_) -> collapse_rec c cl2
	| _ -> if Int.equal (Array.length cl2) 0 then f else mkApp (f,cl2)
      in
      collapse_rec f cl
  | Cast (c,_,_) -> strip_head_cast c
  | _ -> c

let rec drop_extra_implicit_args c = match kind_of_term c with
  (* Removed trailing extra implicit arguments, what improves compatibility
     for constants with recently added maximal implicit arguments *)
  | App (f,args) when isEvar (Array.last args) ->
      drop_extra_implicit_args
	(mkApp (f,fst (Array.chop (Array.length args - 1) args)))
  | _ -> c

(* Get the last arg of an application *)
let last_arg c = match kind_of_term c with
  | App (f,cl) -> Array.last cl
  | _ -> anomaly (Pp.str "last_arg")

(* Get the last arg of an application *)
let decompose_app_vect c =
  match kind_of_term c with
  | App (f,cl) -> (f, cl)
  | _ -> (c,[||])

let adjust_app_list_size f1 l1 f2 l2 =
  let len1 = List.length l1 and len2 = List.length l2 in
  if Int.equal len1 len2 then (f1,l1,f2,l2)
  else if len1 < len2 then
   let extras,restl2 = List.chop (len2-len1) l2 in
    (f1, l1, applist (f2,extras), restl2)
  else
    let extras,restl1 = List.chop (len1-len2) l1 in
    (applist (f1,extras), restl1, f2, l2)

let adjust_app_array_size f1 l1 f2 l2 =
  let len1 = Array.length l1 and len2 = Array.length l2 in
  if Int.equal len1 len2 then (f1,l1,f2,l2)
  else if len1 < len2 then
    let extras,restl2 = Array.chop (len2-len1) l2 in
    (f1, l1, appvect (f2,extras), restl2)
  else
    let extras,restl1 = Array.chop (len1-len2) l1 in
    (appvect (f1,extras), restl1, f2, l2)

(* [map_constr_with_named_binders g f l c] maps [f l] on the immediate
   subterms of [c]; it carries an extra data [l] (typically a name
   list) which is processed by [g na] (which typically cons [na] to
   [l]) at each binder traversal (with name [na]); it is not recursive
   and the order with which subterms are processed is not specified *)

let map_constr_with_named_binders g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,k,t) -> mkCast (f l c, k, f l t)
  | Prod (na,t,c) -> mkProd (na, f l t, f (g na l) c)
  | Lambda (na,t,c) -> mkLambda (na, f l t, f (g na l) c)
  | LetIn (na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g na l) c)
  | App (c,al) -> mkApp (f l c, Array.map (f l) al)
  | Proj (p,c) -> mkProj (p, f l c)
  | Evar (e,al) -> mkEvar (e, Array.map (f l) al)
  | Case (ci,p,c,bl) -> mkCase (ci, f l p, f l c, Array.map (f l) bl)
  | Fix (ln,(lna,tl,bl)) ->
      let l' = Array.fold_left (fun l na -> g na l) l lna in
      mkFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | CoFix(ln,(lna,tl,bl)) ->
      let l' = Array.fold_left (fun l na -> g na l) l lna in
      mkCoFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))

(* [map_constr_with_binders_left_to_right g f n c] maps [f n] on the
   immediate subterms of [c]; it carries an extra data [n] (typically
   a lift index) which is processed by [g] (which typically add 1 to
   [n]) at each binder traversal; the subterms are processed from left
   to right according to the usual representation of the constructions
   (this may matter if [f] does a side-effect); it is not recursive;
   in fact, the usual representation of the constructions is at the
   time being almost those of the ML representation (except for
   (co-)fixpoint) *)

let fold_rec_types g (lna,typarray,_) e =
  let ctxt = Array.map2_i (fun i na t -> (na, None, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> g assum e) e ctxt

let map_left2 f a g b =
  let l = Array.length a in
  if Int.equal l 0 then [||], [||] else begin
    let r = Array.make l (f a.(0)) in
    let s = Array.make l (g b.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i);
      s.(i) <- g b.(i)
    done;
    r, s
  end

let map_constr_with_binders_left_to_right g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (b,k,t) -> 
    let b' = f l b in 
    let t' = f l t in
      if b' == b && t' == t then c
      else mkCast (b',k,t')
  | Prod (na,t,b) ->
      let t' = f l t in
      let b' = f (g (na,None,t) l) b in
	if t' == t && b' == b then c
	else mkProd (na, t', b')
  | Lambda (na,t,b) ->
      let t' = f l t in
      let b' = f (g (na,None,t) l) b in
	if t' == t && b' == b then c
	else mkLambda (na, t', b')
  | LetIn (na,bo,t,b) ->
      let bo' = f l bo in
      let t' = f l t in
      let b' = f (g (na,Some bo,t) l) b in
	if bo' == bo && t' == t && b' == b then c
	else mkLetIn (na, bo', t', b')	    
  | App (c,[||]) -> assert false
  | App (t,al) ->
      (*Special treatment to be able to recognize partially applied subterms*)
      let a = al.(Array.length al - 1) in
      let app = (mkApp (t, Array.sub al 0 (Array.length al - 1))) in
      let app' = f l app in
      let a' = f l a in
	if app' == app && a' == a then c
	else mkApp (app', [| a' |])
  | Proj (p,b) ->
    let b' = f l b in
      if b' == b then c
      else mkProj (p, b')
  | Evar (e,al) -> 
    let al' = Array.map_left (f l) al in
      if Array.for_all2 (==) al' al then c
      else mkEvar (e, al')
  | Case (ci,p,b,bl) ->
      (* In v8 concrete syntax, predicate is after the term to match! *)
      let b' = f l b in
      let p' = f l p in
      let bl' = Array.map_left (f l) bl in
	if b' == b && p' == p && bl' == bl then c
	else mkCase (ci, p', b', bl')
  | Fix (ln,(lna,tl,bl as fx)) ->
      let l' = fold_rec_types g fx l in
      let (tl', bl') = map_left2 (f l) tl (f l') bl in
	if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
	then c
	else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl as fx)) ->
      let l' = fold_rec_types g fx l in
      let (tl', bl') = map_left2 (f l) tl (f l') bl in
	if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
	then c
	else mkCoFix (ln,(lna,tl',bl'))

(* strong *)
let map_constr_with_full_binders g f l cstr = match kind_of_term cstr with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> cstr
  | Cast (c,k, t) ->
      let c' = f l c in
      let t' = f l t in
      if c==c' && t==t' then cstr else mkCast (c', k, t')
  | Prod (na,t,c) ->
      let t' = f l t in
      let c' = f (g (na,None,t) l) c in
      if t==t' && c==c' then cstr else mkProd (na, t', c')
  | Lambda (na,t,c) ->
      let t' = f l t in
      let c' = f (g (na,None,t) l) c in
      if t==t' && c==c' then cstr else  mkLambda (na, t', c')
  | LetIn (na,b,t,c) ->
      let b' = f l b in
      let t' = f l t in
      let c' = f (g (na,Some b,t) l) c in
      if b==b' && t==t' && c==c' then cstr else mkLetIn (na, b', t', c')
  | App (c,al) ->
      let c' = f l c in
      let al' = Array.map (f l) al in
      if c==c' && Array.for_all2 (==) al al' then cstr else mkApp (c', al')
  | Proj (p,c) -> 
      let c' = f l c in
	if c' == c then cstr else mkProj (p, c')
  | Evar (e,al) ->
      let al' = Array.map (f l) al in
      if Array.for_all2 (==) al al' then cstr else mkEvar (e, al')
  | Case (ci,p,c,bl) ->
      let p' = f l p in
      let c' = f l c in
      let bl' = Array.map (f l) bl in
      if p==p' && c==c' && Array.for_all2 (==) bl bl' then cstr else
        mkCase (ci, p', c', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.map (f l) tl in
      let l' =
        Array.fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      let bl' = Array.map (f l') bl in
      if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let tl' = Array.map (f l) tl in
      let l' =
        Array.fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      let bl' = Array.map (f l') bl in
      if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkCoFix (ln,(lna,tl',bl'))

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

let fold_constr_with_binders g f n acc c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (_,t,c) -> f (g n) (f n acc t) c
  | Lambda (_,t,c) -> f (g n) (f n acc t) c
  | LetIn (_,b,t,c) -> f (g n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (p,c) -> f n acc c
  | Evar (_,l) -> Array.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = iterate g (Array.length tl) n in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = iterate g (Array.length tl) n in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd

(* [iter_constr_with_full_binders g f acc c] iters [f acc] on the immediate
   subterms of [c]; it carries an extra data [acc] which is processed by [g] at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_constr_with_full_binders g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_, t) -> f l c; f l t
  | Prod (na,t,c) -> f l t; f (g (na,None,t) l) c
  | Lambda (na,t,c) -> f l t; f (g (na,None,t) l) c
  | LetIn (na,b,t,c) -> f l b; f l t; f (g (na,Some b,t) l) c
  | App (c,args) -> f l c; Array.iter (f l) args
  | Proj (p,c) -> f l c
  | Evar (_,args) -> Array.iter (f l) args
  | Case (_,p,c,bl) -> f l p; f l c; Array.iter (f l) bl
  | Fix (_,(lna,tl,bl)) ->
      let l' = Array.fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      Array.iter (f l) tl;
      Array.iter (f l') bl
  | CoFix (_,(lna,tl,bl)) ->
      let l' = Array.fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      Array.iter (f l) tl;
      Array.iter (f l') bl

(***************************)
(* occurs check functions  *)
(***************************)

exception Occur

let occur_meta c =
  let rec occrec c = match kind_of_term c with
    | Meta _ -> raise Occur
    | _ -> iter_constr occrec c
  in try occrec c; false with Occur -> true

let occur_existential c =
  let rec occrec c = match kind_of_term c with
    | Evar _ -> raise Occur
    | _ -> iter_constr occrec c
  in try occrec c; false with Occur -> true

let occur_meta_or_existential c =
  let rec occrec c = match kind_of_term c with
    | Evar _ -> raise Occur
    | Meta _ -> raise Occur
    | _ -> iter_constr occrec c
  in try occrec c; false with Occur -> true

let occur_evar n c =
  let rec occur_rec c = match kind_of_term c with
    | Evar (sp,_) when Evar.equal sp n -> raise Occur
    | _ -> iter_constr occur_rec c
  in
  try occur_rec c; false with Occur -> true

let occur_in_global env id constr =
  let vars = vars_of_global env constr in
  if Id.Set.mem id vars then raise Occur

let occur_var env id c =
  let rec occur_rec c =
    match kind_of_term c with
    | Var _ | Const _ | Ind _ | Construct _ -> occur_in_global env id c
    | _ -> iter_constr occur_rec c
  in
  try occur_rec c; false with Occur -> true

let occur_var_in_decl env hyp (_,c,typ) =
  match c with
    | None -> occur_var env hyp typ
    | Some body ->
        occur_var env hyp typ ||
        occur_var env hyp body

(* returns the list of free debruijn indices in a term *)

let free_rels m =
  let rec frec depth acc c = match kind_of_term c with
    | Rel n       -> if n >= depth then Int.Set.add (n-depth+1) acc else acc
    | _ -> fold_constr_with_binders succ frec depth acc c
  in
  frec 1 Int.Set.empty m

(* collects all metavar occurences, in left-to-right order, preserving
 * repetitions and all. *)

let collect_metas c =
  let rec collrec acc c =
    match kind_of_term c with
      | Meta mv -> List.add_set Int.equal mv acc
      | _       -> fold_constr collrec acc c
  in
  List.rev (collrec [] c)

(* collects all vars; warning: this is only visible vars, not dependencies in
   all section variables; for the latter, use global_vars_set *)
let collect_vars c =
  let rec aux vars c = match kind_of_term c with
  | Var id -> Id.Set.add id vars
  | _ -> fold_constr aux vars c in
  aux Id.Set.empty c

(* Tests whether [m] is a subterm of [t]:
   [m] is appropriately lifted through abstractions of [t] *)

let dependent_main noevar univs m t =
  let eqc x y = if univs then fst (Universes.eq_constr_universes x y) else eq_constr_nounivs x y in
  let rec deprec m t =
    if eqc m t then
      raise Occur
    else
      match kind_of_term m, kind_of_term t with
	| App (fm,lm), App (ft,lt) when Array.length lm < Array.length lt ->
	    deprec m (mkApp (ft,Array.sub lt 0 (Array.length lm)));
	    CArray.Fun1.iter deprec m
	      (Array.sub lt
		(Array.length lm) ((Array.length lt) - (Array.length lm)))
	| _, Cast (c,_,_) when noevar && isMeta c -> ()
	| _, Evar _ when noevar -> ()
	| _ -> iter_constr_with_binders (fun c -> lift 1 c) deprec m t
  in
  try deprec m t; false with Occur -> true

let dependent = dependent_main false false
let dependent_no_evar = dependent_main true false

let dependent_univs = dependent_main false true
let dependent_univs_no_evar = dependent_main true true

let dependent_in_decl a (_,c,t) =
  match c with
    | None -> dependent a t
    | Some body -> dependent a body || dependent a t

let count_occurrences m t =
  let n = ref 0 in
  let rec countrec m t =
    if eq_constr m t then
      incr n
    else
      match kind_of_term m, kind_of_term t with
	| App (fm,lm), App (ft,lt) when Array.length lm < Array.length lt ->
	    countrec m (mkApp (ft,Array.sub lt 0 (Array.length lm)));
	    Array.iter (countrec m)
	      (Array.sub lt
		(Array.length lm) ((Array.length lt) - (Array.length lm)))
	| _, Cast (c,_,_) when isMeta c -> ()
	| _, Evar _ -> ()
	| _ -> iter_constr_with_binders (lift 1) countrec m t
  in
  countrec m t;
  !n

(* Synonymous *)
let occur_term = dependent

let pop t = lift (-1) t

(***************************)
(*  bindings functions *)
(***************************)

type meta_type_map = (metavariable * types) list

type meta_value_map = (metavariable * constr) list

let rec subst_meta bl c =
  match kind_of_term c with
    | Meta i -> (try Int.List.assoc i bl with Not_found -> c)
    | _ -> map_constr (subst_meta bl) c

(* First utilities for avoiding telescope computation for subst_term *)

let prefix_application eq_fun (k,c) (t : constr) =
  let c' = collapse_appl c and t' = collapse_appl t in
  match kind_of_term c', kind_of_term t' with
    | App (f1,cl1), App (f2,cl2) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2
	   && eq_fun c' (mkApp (f2, Array.sub cl2 0 l1)) then
	  Some (mkApp (mkRel k, Array.sub cl2 l1 (l2 - l1)))
	else
	  None
    | _ -> None

let my_prefix_application eq_fun (k,c) (by_c : constr) (t : constr) =
  let c' = collapse_appl c and t' = collapse_appl t in
  match kind_of_term c', kind_of_term t' with
    | App (f1,cl1), App (f2,cl2) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2
	   && eq_fun c' (mkApp (f2, Array.sub cl2 0 l1)) then
	  Some (mkApp ((lift k by_c), Array.sub cl2 l1 (l2 - l1)))
	else
	  None
    | _ -> None

(* Recognizing occurrences of a given subterm in a term: [subst_term c t]
   substitutes [(Rel 1)] for all occurrences of term [c] in a term [t];
   works if [c] has rels *)

let subst_term_gen eq_fun c t =
  let rec substrec (k,c as kc) t =
    match prefix_application eq_fun kc t with
      | Some x -> x
      | None ->
    if eq_fun c t then mkRel k
    else
      map_constr_with_binders (fun (k,c) -> (k+1,lift 1 c)) substrec kc t
  in
  substrec (1,c) t

let subst_term = subst_term_gen eq_constr

(* Recognizing occurrences of a given subterm in a term :
   [replace_term c1 c2 t] substitutes [c2] for all occurrences of
   term [c1] in a term [t]; works if [c1] and [c2] have rels *)

let replace_term_gen eq_fun c by_c in_t =
  let rec substrec (k,c as kc) t =
    match my_prefix_application eq_fun kc by_c t with
      | Some x -> x
      | None ->
    (if eq_fun c t then (lift k by_c) else
      map_constr_with_binders (fun (k,c) -> (k+1,lift 1 c))
	substrec kc t)
  in
  substrec (0,c) in_t

let replace_term = replace_term_gen eq_constr

let vars_of_env env =
  let s =
    Context.fold_named_context (fun (id,_,_) s -> Id.Set.add id s)
      (named_context env) ~init:Id.Set.empty in
  Context.fold_rel_context
    (fun (na,_,_) s -> match na with Name id -> Id.Set.add id s | _ -> s)
    (rel_context env) ~init:s

let add_vname vars = function
    Name id -> Id.Set.add id vars
  | _ -> vars

(*************************)
(*   Names environments  *)
(*************************)
type names_context = Name.t list
let add_name n nl = n::nl
let lookup_name_of_rel p names =
  try List.nth names (p-1)
  with Invalid_argument _ | Failure _ -> raise Not_found
let lookup_rel_of_name id names =
  let rec lookrec n = function
    | Anonymous :: l  -> lookrec (n+1) l
    | (Name id') :: l -> if Id.equal id' id then n else lookrec (n+1) l
    | []            -> raise Not_found
  in
  lookrec 1 names
let empty_names_context = []

let ids_of_rel_context sign =
  Context.fold_rel_context
    (fun (na,_,_) l -> match na with Name id -> id::l | Anonymous -> l)
    sign ~init:[]

let ids_of_named_context sign =
  Context.fold_named_context (fun (id,_,_) idl -> id::idl) sign ~init:[]

let ids_of_context env =
  (ids_of_rel_context (rel_context env))
  @ (ids_of_named_context (named_context env))


let names_of_rel_context env =
  List.map (fun (na,_,_) -> na) (rel_context env)

let is_section_variable id =
  try let _ = Global.lookup_named id in true
  with Not_found -> false

let isGlobalRef c =
  match kind_of_term c with
  | Const _ | Ind _ | Construct _ | Var _ -> true
  | _ -> false

let is_template_polymorphic env f =
  match kind_of_term f with
  | Ind ind -> Environ.template_polymorphic_pind ind env
  | Const c -> Environ.template_polymorphic_pconstant c env
  | _ -> false

let base_sort_cmp pb s0 s1 =
  match (s0,s1) with
    | (Prop c1, Prop c2) -> c1 == Null || c2 == Pos  (* Prop <= Set *)
    | (Prop c1, Type u)  -> pb == Reduction.CUMUL
    | (Type u1, Type u2) -> true
    | _ -> false

(* eq_constr extended with universe erasure *)
let compare_constr_univ f cv_pb t1 t2 =
  match kind_of_term t1, kind_of_term t2 with
      Sort s1, Sort s2 -> base_sort_cmp cv_pb s1 s2
    | Prod (_,t1,c1), Prod (_,t2,c2) ->
	f Reduction.CONV t1 t2 && f cv_pb c1 c2
    | _ -> compare_constr (fun t1 t2 -> f Reduction.CONV t1 t2) t1 t2

let rec constr_cmp cv_pb t1 t2 = compare_constr_univ constr_cmp cv_pb t1 t2

let eq_constr t1 t2 = constr_cmp Reduction.CONV t1 t2

(* App(c,[t1,...tn]) -> ([c,t1,...,tn-1],tn)
   App(c,[||]) -> ([],c) *)
let split_app c = match kind_of_term c with
    App(c,l) ->
      let len = Array.length l in
      if Int.equal len 0 then ([],c) else
	let last = Array.get l (len-1) in
	let prev = Array.sub l 0 (len-1) in
	c::(Array.to_list prev), last
  | _ -> assert false

type subst = (rel_context*constr) Evar.Map.t

exception CannotFilter

let filtering env cv_pb c1 c2 =
  let evm = ref Evar.Map.empty in
  let define cv_pb e1 ev c1 =
    try let (e2,c2) = Evar.Map.find ev !evm in
    let shift = List.length e1 - List.length e2 in
    if constr_cmp cv_pb c1 (lift shift c2) then () else raise CannotFilter
    with Not_found ->
      evm := Evar.Map.add ev (e1,c1) !evm
  in
  let rec aux env cv_pb c1 c2 =
    match kind_of_term c1, kind_of_term c2 with
      | App _, App _ ->
        let ((p1,l1),(p2,l2)) = (split_app c1),(split_app c2) in
        let () = aux env cv_pb l1 l2 in
        begin match p1, p2 with
        | [], [] -> ()
        | (h1 :: p1), (h2 :: p2) ->
          aux env cv_pb (applistc h1 p1) (applistc h2 p2)
        | _ -> assert false
        end
      | Prod (n,t1,c1), Prod (_,t2,c2) ->
	  aux env cv_pb t1 t2;
	  aux ((n,None,t1)::env) cv_pb c1 c2
      | _, Evar (ev,_) -> define cv_pb env ev c1
      | Evar (ev,_), _ -> define cv_pb env ev c2
      | _ ->
	  if compare_constr_univ
	  (fun pb c1 c2 -> aux env pb c1 c2; true) cv_pb c1 c2 then ()
	  else raise CannotFilter
	  (* TODO: le reste des binders *)
  in
  aux env cv_pb c1 c2; !evm

let decompose_prod_letin : constr -> int * rel_context * constr =
  let rec prodec_rec i l c = match kind_of_term c with
    | Prod (n,t,c)    -> prodec_rec (succ i) ((n,None,t)::l) c
    | LetIn (n,d,t,c) -> prodec_rec (succ i) ((n,Some d,t)::l) c
    | Cast (c,_,_)    -> prodec_rec i l c
    | _               -> i,l,c in
  prodec_rec 0 []

let align_prod_letin c a : rel_context * constr =
  let (lc,_,_) = decompose_prod_letin c in
  let (la,l,a) = decompose_prod_letin a in
  if not (la >= lc) then invalid_arg "align_prod_letin";
  let (l1,l2) = Util.List.chop lc l in
  l2,it_mkProd_or_LetIn a l1

(* We reduce a series of head eta-redex or nothing at all   *)
(* [x1:c1;...;xn:cn]@(f;a1...an;x1;...;xn) --> @(f;a1...an) *)
(* Remplace 2 earlier buggish versions                      *)

let rec eta_reduce_head c =
  match kind_of_term c with
    | Lambda (_,c1,c') ->
	(match kind_of_term (eta_reduce_head c') with
           | App (f,cl) ->
               let lastn = (Array.length cl) - 1 in
               if lastn < 0 then anomaly (Pp.str "application without arguments")
               else
                 (match kind_of_term cl.(lastn) with
                    | Rel 1 ->
			let c' =
                          if Int.equal lastn 0 then f
			  else mkApp (f, Array.sub cl 0 lastn)
			in
			if noccurn 1 c'
                        then lift (-1) c'
                        else c
                    | _   -> c)
           | _ -> c)
    | _ -> c


(* iterator on rel context *)
let process_rel_context f env =
  let sign = named_context_val env in
  let rels = rel_context env in
  let env0 = reset_with_named_context sign env in
  Context.fold_rel_context f rels ~init:env0

let assums_of_rel_context sign =
  Context.fold_rel_context
    (fun (na,c,t) l ->
      match c with
          Some _ -> l
        | None -> (na, t)::l)
    sign ~init:[]

let map_rel_context_in_env f env sign =
  let rec aux env acc = function
    | d::sign ->
	aux (push_rel d env) (map_rel_declaration (f env) d :: acc) sign
    | [] ->
	acc
  in
  aux env [] (List.rev sign)

let map_rel_context_with_binders f sign =
  let rec aux k = function
    | d::sign -> map_rel_declaration (f k) d :: aux (k-1) sign
    | [] -> []
  in
  aux (rel_context_length sign) sign

let substl_rel_context l =
  map_rel_context_with_binders (fun k -> substnl l (k-1))

let lift_rel_context n =
  map_rel_context_with_binders (liftn n)

let smash_rel_context sign =
  let rec aux acc = function
  | [] -> acc
  | (_,None,_ as d) :: l -> aux (d::acc) l
  | (_,Some b,_) :: l ->
      (* Quadratic in the number of let but there are probably a few of them *)
      aux (List.rev (substl_rel_context [b] (List.rev acc))) l
  in List.rev (aux [] sign)

let adjust_subst_to_rel_context sign l =
  let rec aux subst sign l =
    match sign, l with
    | (_,None,_)::sign', a::args' -> aux (a::subst) sign' args'
    | (_,Some c,_)::sign', args' ->
	aux (substl (List.rev subst) c :: subst) sign' args'
    | [], [] -> List.rev subst
    | _ -> anomaly (Pp.str "Instance and signature do not match")
  in aux [] (List.rev sign) l

let fold_named_context_both_sides f l ~init = List.fold_right_and_left f l init

let rec mem_named_context id = function
  | (id',_,_) :: _ when Id.equal id id' -> true
  | _ :: sign -> mem_named_context id sign
  | [] -> false

let compact_named_context_reverse sign =
  let compact l (i1,c1,t1) =
    match l with
    | [] -> [[i1],c1,t1]
    | (l2,c2,t2)::q ->
       if Option.equal Constr.equal c1 c2 && Constr.equal t1 t2
       then (i1::l2,c2,t2)::q
       else ([i1],c1,t1)::l
  in Context.fold_named_context_reverse compact ~init:[] sign

let compact_named_context sign = List.rev (compact_named_context_reverse sign)

let clear_named_body id env =
  let aux _ = function
  | (id',Some c,t) when Id.equal id id' -> push_named (id,None,t)
  | d -> push_named d in
  fold_named_context aux env ~init:(reset_context env)

let global_vars env ids = Id.Set.elements (global_vars_set env ids)

let global_vars_set_of_decl env = function
  | (_,None,t) -> global_vars_set env t
  | (_,Some c,t) ->
      Id.Set.union (global_vars_set env t)
        (global_vars_set env c)

let dependency_closure env sign hyps =
  if Id.Set.is_empty hyps then [] else
    let (_,lh) =
      Context.fold_named_context_reverse
        (fun (hs,hl) (x,_,_ as d) ->
          if Id.Set.mem x hs then
            (Id.Set.union (global_vars_set_of_decl env d) (Id.Set.remove x hs),
            x::hl)
          else (hs,hl))
        ~init:(hyps,[])
        sign in
    List.rev lh

(* Combinators on judgments *)

let on_judgment f j = { uj_val = f j.uj_val; uj_type = f j.uj_type }
let on_judgment_value f j = { j with uj_val = f j.uj_val }
let on_judgment_type f j = { j with uj_type = f j.uj_type }

(* Cut a context ctx in 2 parts (ctx1,ctx2) with ctx1 containing k
     variables; skips let-in's *)
let context_chop k ctx =
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, ((_,Some _,_ as h)::t)) -> chop_aux (h::acc) (n, t)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> anomaly (Pp.str "context_chop")
  in chop_aux [] (k,ctx)

(* Do not skip let-in's *)
let env_rel_context_chop k env =
  let rels = rel_context env in
  let ctx1,ctx2 = List.chop k rels in
  push_rel_context ctx2 (reset_with_named_context (named_context_val env) env),
  ctx1

(*******************************************)
(* Functions to deal with impossible cases *)
(*******************************************)
let impossible_default_case = ref None

let set_impossible_default_clause c = impossible_default_case := Some c

let coq_unit_judge =
  let na1 = Name (Id.of_string "A") in
  let na2 = Name (Id.of_string "H") in
  fun () ->
    match !impossible_default_case with
    | Some fn -> 
        let (id,type_of_id), ctx = fn () in
	  make_judge id type_of_id, ctx
    | None ->
	(* In case the constants id/ID are not defined *)
	make_judge (mkLambda (na1,mkProp,mkLambda(na2,mkRel 1,mkRel 1)))
                 (mkProd (na1,mkProp,mkArrow (mkRel 1) (mkRel 2))), 
       Univ.ContextSet.empty
