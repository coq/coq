(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Sign
open Environ
open Libnames
open Nametab

(* Sorts and sort family *)

let print_sort = function
  | Prop Pos -> (str "Set")
  | Prop Null -> (str "Prop")
  | Type u -> (str "Type(" ++ Univ.pr_uni u ++ str ")")

let pr_sort_family = function
  | InSet -> (str "Set")
  | InProp -> (str "Prop")
  | InType -> (str "Type")

let pr_name = function
  | Name id -> pr_id id
  | Anonymous -> str "_"

let pr_sp sp = str(string_of_kn sp)
let pr_con sp = str(string_of_con sp)

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
      (str"Evar#" ++ int e ++ str"{" ++
       prlist_with_sep spc pr_constr (Array.to_list l) ++str"}")
  | Const c -> str"Cst(" ++ pr_con c ++ str")"
  | Ind (sp,i) -> str"Ind(" ++ pr_sp sp ++ str"," ++ int i ++ str")"
  | Construct ((sp,i),j) ->
      str"Constr(" ++ pr_sp sp ++ str"," ++ int i ++ str"," ++ int j ++ str")"
  | Case (ci,p,c,bl) -> v 0
      (hv 0 (str"<"++pr_constr p++str">"++ cut() ++ str"Case " ++
             pr_constr c ++ str"of") ++ cut() ++
       prlist_with_sep (fun _ -> brk(1,2)) pr_constr (Array.to_list bl) ++
      cut() ++ str"end")
  | Fix ((t,i),(lna,tl,bl)) ->
      let fixl = Array.mapi (fun i na -> (na,t.(i),tl.(i),bl.(i))) lna in
      hov 1
        (str"fix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,i,ty,bd) ->
           pr_name na ++ str"/" ++ int i ++ str":" ++ pr_constr ty ++
           cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")
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
    
(*let current_module = ref empty_dirpath

let set_module m = current_module := m*)

let new_univ = 
  let univ_gen = ref 0 in
  (fun sp ->
    incr univ_gen; 
    Univ.make_univ (Lib.library_dp(),!univ_gen))
let new_Type () = mkType (new_univ ())
let new_Type_sort () = Type (new_univ ())

(* This refreshes universes in types; works only for inferred types (i.e. for
   types of the form (x1:A1)...(xn:An)B with B a sort or an atom in
   head normal form) *)
let refresh_universes_gen strict t =
  let modified = ref false in
  let rec refresh t = match kind_of_term t with
    | Sort (Type u) when strict or u <> Univ.type0m_univ ->
	modified := true; new_Type ()
    | Prod (na,u,v) -> mkProd (na,u,refresh v)
    | _ -> t in
  let t' = refresh t in
  if !modified then t' else t

let refresh_universes = refresh_universes_gen false
let refresh_universes_strict = refresh_universes_gen true

let new_sort_in_family = function 
  | InProp -> prop_sort
  | InSet -> set_sort
  | InType -> Type (new_univ ())



(* prod_it b [xn:Tn;..;x1:T1] = (x1:T1)..(xn:Tn)b *)
let prod_it ~init = List.fold_left (fun c (n,t)  -> mkProd (n, t, c)) init

(* lam_it b [xn:Tn;..;x1:T1] = [x1:T1]..[xn:Tn]b *)
let lam_it ~init = List.fold_left (fun c (n,t)  -> mkLambda (n, t, c)) init

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
    array_map2_i
      (fun i na t ->
	 match na with
	   | Name id -> (id, None, lift i t)
	   | Anonymous -> anomaly "Fix declarations must be named")
      lna typarray in
  Array.fold_left
    (fun e assum -> push_named assum e) env ctxt

let rec lookup_rel_id id sign = 
  let rec lookrec = function
    | (n, (Anonymous,_,_)::l) -> lookrec (n+1,l)
    | (n, (Name id',_,t)::l)  -> if id' = id then (n,t) else lookrec (n+1,l)
    | (_, [])                 -> raise Not_found
  in 
  lookrec (1,sign)

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
let mkProd_or_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

(* Constructs either [(x:t)c] or [c] where [x] is replaced by [b] *)
let mkProd_wo_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na,  t, c)
    | Some b -> subst1 b c

let it_mkProd_wo_LetIn ~init = 
  List.fold_left (fun c d -> mkProd_wo_LetIn d c) init

let it_mkProd_or_LetIn ~init = 
  List.fold_left (fun c d -> mkProd_or_LetIn d c) init

let it_mkLambda_or_LetIn ~init =
  List.fold_left (fun c d -> mkLambda_or_LetIn d c) init

let it_named_context_quantifier f ~init = 
  List.fold_left (fun c d -> f d c) init

let it_mkNamedProd_or_LetIn = it_named_context_quantifier mkNamedProd_or_LetIn
let it_mkNamedLambda_or_LetIn = it_named_context_quantifier mkNamedLambda_or_LetIn

let it_mkNamedProd_wo_LetIn = it_named_context_quantifier mkNamedProd_wo_LetIn

(* *)

(* strips head casts and flattens head applications *)
let rec strip_head_cast c = match kind_of_term c with
  | App (f,cl) -> 
      let rec collapse_rec f cl2 = match kind_of_term f with
	| App (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
	| Cast (c,_,_) -> collapse_rec c cl2
	| _ -> if Array.length cl2 = 0 then f else mkApp (f,cl2)
      in 
      collapse_rec f cl
  | Cast (c,_,_) -> strip_head_cast c
  | _ -> c

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
  let ctxt = array_map2_i (fun i na t -> (na, None, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> g assum e) e ctxt


let map_constr_with_binders_left_to_right g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,k,t) -> let c' = f l c in mkCast (c',k,f l t)
  | Prod (na,t,c) ->
      let t' = f l t in
      mkProd (na, t', f (g (na,None,t) l) c)
  | Lambda (na,t,c) ->
      let t' = f l t in
      mkLambda (na, t', f (g (na,None,t) l) c)
  | LetIn (na,b,t,c) ->
      let b' = f l b in
      let t' = f l t in
      let c' = f (g (na,Some b,t) l) c in
      mkLetIn (na, b', t', c')
  | App (c,[||]) -> assert false
  | App (c,al) ->
      (*Special treatment to be able to recognize partially applied subterms*)
      let a = al.(Array.length al - 1) in
      let hd = f l (mkApp (c, Array.sub al 0 (Array.length al - 1))) in
      mkApp (hd, [| f l a |])
  | Evar (e,al) -> mkEvar (e, array_map_left (f l) al)
  | Case (ci,p,c,bl) ->
      (* In v8 concrete syntax, predicate is after the term to match! *)
      let c' = f l c in
      let p' = f l p in
      mkCase (ci, p', c', array_map_left (f l) bl)
  | Fix (ln,(lna,tl,bl as fx)) ->
      let l' = fold_rec_types g fx l in
      let (tl',bl') = array_map_left_pair (f l) tl (f l') bl in
      mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl as fx)) ->
      let l' = fold_rec_types g fx l in
      let (tl',bl') = array_map_left_pair (f l) tl (f l') bl in
      mkCoFix (ln,(lna,tl',bl'))

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
      if c==c' && array_for_all2 (==) al al' then cstr else mkApp (c', al')
  | Evar (e,al) ->
      let al' = Array.map (f l) al in
      if array_for_all2 (==) al al' then cstr else mkEvar (e, al')
  | Case (ci,p,c,bl) ->
      let p' = f l p in
      let c' = f l c in
      let bl' = Array.map (f l) bl in
      if p==p' && c==c' && array_for_all2 (==) bl bl' then cstr else
        mkCase (ci, p', c', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.map (f l) tl in
      let l' =
        array_fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      let bl' = Array.map (f l') bl in
      if array_for_all2 (==) tl tl' && array_for_all2 (==) bl bl'
      then cstr
      else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let tl' = Array.map (f l) tl in
      let l' =
        array_fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      let bl' = Array.map (f l') bl in
      if array_for_all2 (==) tl tl' && array_for_all2 (==) bl bl'
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
  | Evar (_,l) -> Array.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(lna,tl,bl)) -> 
      let n' = iterate g (Array.length tl) n in
      let fd = array_map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n (f n' acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = iterate g (Array.length tl) n in
      let fd = array_map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n (f n' acc t) b) acc fd

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
  | Evar (_,args) -> Array.iter (f l) args
  | Case (_,p,c,bl) -> f l p; f l c; Array.iter (f l) bl
  | Fix (_,(lna,tl,bl)) -> 
      let l' = array_fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      Array.iter (f l) tl;
      Array.iter (f l') bl
  | CoFix (_,(lna,tl,bl)) ->
      let l' = array_fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
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

let occur_const s c = 
  let rec occur_rec c = match kind_of_term c with
    | Const sp when sp=s -> raise Occur
    | _ -> iter_constr occur_rec c
  in 
  try occur_rec c; false with Occur -> true

let occur_evar n c = 
  let rec occur_rec c = match kind_of_term c with
    | Evar (sp,_) when sp=n -> raise Occur
    | _ -> iter_constr occur_rec c
  in 
  try occur_rec c; false with Occur -> true

let occur_in_global env id constr =
  let vars = vars_of_global env constr in
  if List.mem id vars then raise Occur

let occur_var env s c = 
  let rec occur_rec c =
    occur_in_global env s c;
    iter_constr occur_rec c
  in 
  try occur_rec c; false with Occur -> true

let occur_var_in_decl env hyp (_,c,typ) =
  match c with
    | None -> occur_var env hyp typ
    | Some body ->
        occur_var env hyp typ ||
        occur_var env hyp body

(* Tests that t is a subterm of c *)
let occur_term t c = 
  let eq_constr_fail c = if eq_constr t c then raise Occur
  in let rec occur_rec c = eq_constr_fail c; iter_constr occur_rec c
  in try occur_rec c; false with Occur -> true

(* returns the list of free debruijn indices in a term *)

let free_rels m = 
  let rec frec depth acc c = match kind_of_term c with
    | Rel n       -> if n >= depth then Intset.add (n-depth+1) acc else acc
    | _ -> fold_constr_with_binders succ frec depth acc c
  in 
  frec 1 Intset.empty m

(* collects all metavar occurences, in left-to-right order, preserving
 * repetitions and all. *)

let collect_metas c = 
  let rec collrec acc c =
    match kind_of_term c with
      | Meta mv -> list_add_set mv acc
      | _       -> fold_constr collrec acc c
  in
  List.rev (collrec [] c)

(* (dependent M N) is true iff M is eq_term with a subterm of N 
   M is appropriately lifted through abstractions of N *)

let dependent m t =
  let rec deprec m t =
    if eq_constr m t then
      raise Occur
    else
      match kind_of_term m, kind_of_term t with
	| App (fm,lm), App (ft,lt) when Array.length lm < Array.length lt ->
	    deprec m (mkApp (ft,Array.sub lt 0 (Array.length lm)));
	    Array.iter (deprec m)
	      (Array.sub lt 
		(Array.length lm) ((Array.length lt) - (Array.length lm)))
	| _ -> iter_constr_with_binders (lift 1) deprec m t
  in 
  try deprec m t; false with Occur -> true

let pop t = lift (-1) t

(***************************)
(*  bindings functions *)                         
(***************************)

type metamap = (metavariable * constr) list 

let rec subst_meta bl c = 
  match kind_of_term c with
    | Meta i -> (try List.assoc i bl with Not_found -> c)
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

(* Recognizing occurrences of a given (closed) subterm in a term for Pattern :
   [subst_term c t] substitutes [(Rel 1)] for all occurrences of (closed)
   term [c] in a term [t] *)
(*i Bizarre : si on cherche un sous terme clos, pourquoi le lifter ? i*)

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

(* Recognizing occurrences of a given (closed) subterm in a term :
   [replace_term c1 c2 t] substitutes [c2] for all occurrences of (closed)
   term [c1] in a term [t] *)
(*i Meme remarque : a priori [c] n'est pas forcement clos i*)

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

let subst_term = subst_term_gen eq_constr

let replace_term = replace_term_gen eq_constr

(* Substitute only at a list of locations or excluding a list of
   locations; in the occurrences list (b,l), b=true means no
   occurrence except the ones in l and b=false, means all occurrences
   except the ones in l *)

type occurrences = bool * int list
let all_occurrences = (false,[])
let no_occurrences_in_set = (true,[])

let error_invalid_occurrence l =
  let l = list_uniquize (List.sort Pervasives.compare l) in
  errorlabstrm ""
    (str ("Invalid occurrence " ^ plural (List.length l) "number" ^": ") ++ 
     prlist_with_sep spc int l)

let subst_term_occ_gen (nowhere_except_in,locs) occ c t =
  let maxocc = List.fold_right max locs 0 in
  let pos = ref occ in
  assert (List.for_all (fun x -> x >= 0) locs);
  let rec substrec (k,c as kc) t =
    if nowhere_except_in & !pos > maxocc then t
    else
    if eq_constr c t then
      let r = 
	if nowhere_except_in then
	  if List.mem !pos locs then (mkRel k) else t
	else 
	  if List.mem !pos locs then t else (mkRel k)
      in incr pos; r
    else
      map_constr_with_binders_left_to_right
	(fun d (k,c) -> (k+1,lift 1 c))
        substrec kc t
  in
  let t' = substrec (1,c) t in
  (!pos, t')

let subst_term_occ (nowhere_except_in,locs as plocs) c t = 
  if locs = [] then if nowhere_except_in then t else subst_term c t
  else 
    let (nbocc,t') = subst_term_occ_gen plocs 1 c t in
    let rest = List.filter (fun o -> o >= nbocc) locs in
    if rest <> [] then error_invalid_occurrence rest;
    t'

let subst_term_occ_decl (nowhere_except_in,locs as plocs) c (id,bodyopt,typ as d) =
  match bodyopt with
    | None -> (id,None,subst_term_occ plocs c typ)
    | Some body -> 
	if locs = [] then
	  if nowhere_except_in then d
	  else (id,Some (subst_term c body),subst_term c typ)
	else 
	  let (nbocc,body') = subst_term_occ_gen plocs 1 c body in
	  let (nbocc',t') = subst_term_occ_gen plocs nbocc c typ in
	  let rest = List.filter (fun o -> o >= nbocc') locs in
	  if rest <> [] then error_invalid_occurrence rest;
	  (id,Some body',t')


(* First character of a constr *)

let lowercase_first_char id =
  lowercase_first_char_utf8 (string_of_id id)

let vars_of_env env =
  let s = 
    Sign.fold_named_context (fun (id,_,_) s -> Idset.add id s)
      (named_context env) ~init:Idset.empty in
  Sign.fold_rel_context
    (fun (na,_,_) s -> match na with Name id -> Idset.add id s | _ -> s)
    (rel_context env) ~init:s

let add_vname vars = function
    Name id -> Idset.add id vars
  | _ -> vars

let id_of_global = Nametab.id_of_global

let sort_hdchar = function
  | Prop(_) -> "P"
  | Type(_) -> "T"

let hdchar env c = 
  let rec hdrec k c =
    match kind_of_term c with
    | Prod (_,_,c)       -> hdrec (k+1) c
    | Lambda (_,_,c)     -> hdrec (k+1) c
    | LetIn (_,_,_,c)    -> hdrec (k+1) c
    | Cast (c,_,_)         -> hdrec k c
    | App (f,l)         -> hdrec k f
    | Const kn       ->
	lowercase_first_char (id_of_label (con_label kn))
    | Ind ((kn,i) as x) ->
	if i=0 then 
	  lowercase_first_char (id_of_label (label kn))
	else 
	  lowercase_first_char (id_of_global (IndRef x))
    | Construct ((sp,i) as x) ->
	lowercase_first_char (id_of_global (ConstructRef x))
    | Var id  -> lowercase_first_char id
    | Sort s -> sort_hdchar s
    | Rel n ->
	(if n<=k then "p" (* the initial term is flexible product/function *)
	 else
	   try match Environ.lookup_rel (n-k) env with
	     | (Name id,_,_)   -> lowercase_first_char id
	     | (Anonymous,_,t) -> hdrec 0 (lift (n-k) t)
	   with Not_found -> "y")
    | Fix ((_,i),(lna,_,_)) -> 
	let id = match lna.(i) with Name id -> id | _ -> assert false in
	lowercase_first_char id
    | CoFix (i,(lna,_,_)) -> 
	let id = match lna.(i) with Name id -> id | _ -> assert false in
	lowercase_first_char id
    | Meta _|Evar _|Case (_, _, _, _) -> "y"
  in 
  hdrec 0 c

let id_of_name_using_hdchar env a = function
  | Anonymous -> id_of_string (hdchar env a) 
  | Name id   -> id

let named_hd env a = function
  | Anonymous -> Name (id_of_string (hdchar env a)) 
  | x         -> x

let mkProd_name   env (n,a,b) = mkProd (named_hd env a n, a, b)
let mkLambda_name env (n,a,b) = mkLambda (named_hd env a n, a, b)

let lambda_name = mkLambda_name
let prod_name = mkProd_name

let prod_create   env (a,b) = mkProd (named_hd env a Anonymous, a, b)
let lambda_create env (a,b) =  mkLambda (named_hd env a Anonymous, a, b)

let name_assumption env (na,c,t) =
  match c with
    | None      -> (named_hd env t na, None, t)
    | Some body -> (named_hd env body na, c, t)

let name_context env hyps =
  snd
    (List.fold_left
       (fun (env,hyps) d -> 
	  let d' = name_assumption env d in (push_rel d' env, d' :: hyps))
       (env,[]) (List.rev hyps))

let mkProd_or_LetIn_name env b d = mkProd_or_LetIn (name_assumption env d) b 
let mkLambda_or_LetIn_name env b d = mkLambda_or_LetIn (name_assumption env d)b

let it_mkProd_or_LetIn_name env b hyps =
  it_mkProd_or_LetIn b (name_context env hyps)
let it_mkLambda_or_LetIn_name env b hyps =
  it_mkLambda_or_LetIn b (name_context env hyps)

(*************************)
(*   Names environments  *)
(*************************)
type names_context = name list
let add_name n nl = n::nl
let lookup_name_of_rel p names =
  try List.nth names (p-1)
  with Invalid_argument _ | Failure _ -> raise Not_found
let rec lookup_rel_of_name id names = 
  let rec lookrec n = function
    | Anonymous :: l  -> lookrec (n+1) l
    | (Name id') :: l -> if id' = id then n else lookrec (n+1) l
    | []            -> raise Not_found
  in 
  lookrec 1 names
let empty_names_context = []

let ids_of_rel_context sign =
  Sign.fold_rel_context
    (fun (na,_,_) l -> match na with Name id -> id::l | Anonymous -> l)
    sign ~init:[]

let ids_of_named_context sign =
  Sign.fold_named_context (fun (id,_,_) idl -> id::idl) sign ~init:[]

let ids_of_context env = 
  (ids_of_rel_context (rel_context env))
  @ (ids_of_named_context (named_context env))


let names_of_rel_context env =
  List.map (fun (na,_,_) -> na) (rel_context env)

(**** Globality of identifiers *)

(* TODO temporary hack!!! *)
let rec is_imported_modpath = function
  | MPfile dp -> dp <> (Lib.library_dp ())
(*  | MPdot (mp,_) -> is_imported_modpath mp *)
  | _ -> false

let is_imported_ref = function
  | VarRef _ -> false
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) 
(*  | ModTypeRef ln  *) -> 
      let (mp,_,_) = repr_kn kn in is_imported_modpath mp
(*  | ModRef mp ->
      is_imported_modpath mp
*)
  | ConstRef kn ->
      let (mp,_,_) = repr_con kn in is_imported_modpath mp

let is_global id =
  try 
    let ref = locate (make_short_qualid id) in
    not (is_imported_ref ref)
  with Not_found -> 
    false

let is_constructor id =
  try 
    match locate (make_short_qualid id) with 
      | ConstructRef _ as ref -> not (is_imported_ref ref)
      | _ -> false
  with Not_found -> 
    false

let is_section_variable id =
  try let _ = Global.lookup_named id in true
  with Not_found -> false

let next_global_ident_from allow_secvar id avoid = 
  let rec next_rec id =
    let id = next_ident_away_from id avoid in
    if (allow_secvar && is_section_variable id) || not (is_global id) then
      id
    else  
      next_rec (lift_ident id)
  in 
  next_rec id

let next_global_ident_away allow_secvar id avoid =
  let id  = next_ident_away id avoid in
  if (allow_secvar && is_section_variable id) || not (is_global id) then
    id
  else  
    next_global_ident_from allow_secvar (lift_ident id) avoid

let isGlobalRef c = 
  match kind_of_term c with
  | Const _ | Ind _ | Construct _ | Var _ -> true
  | _ -> false

let has_polymorphic_type c =
  match (Global.lookup_constant c).Declarations.const_type with
  | Declarations.PolymorphicArity _ -> true
  | _ -> false

(* nouvelle version de renommage des variables (DEC 98) *)
(* This is the algorithm to display distinct bound variables 

    - Règle 1 : un nom non anonyme, même non affiché, contribue à la liste
      des noms à éviter 
    - Règle 2 : c'est la dépendance qui décide si on affiche ou pas

    Exemple : 
    si bool_ind = (P:bool->Prop)(f:(P true))(f:(P false))(b:bool)(P b), alors
    il est affiché (P:bool->Prop)(P true)->(P false)->(b:bool)(P b)
    mais f et f0 contribue à la liste des variables à éviter (en supposant 
    que les noms f et f0 ne sont pas déjà pris)
    Intérêt : noms homogènes dans un but avant et après Intro
*)

type used_idents = identifier list

let occur_rel p env id = 
  try lookup_name_of_rel p env = Name id
  with Not_found -> false (* Unbound indice : may happen in debug *)

let occur_id nenv id0 c =
  let rec occur n c = match kind_of_term c with
    | Var id when  id=id0 -> raise Occur
    | Const kn when id_of_global (ConstRef kn) = id0 -> raise Occur
    | Ind ind_sp
	when id_of_global (IndRef ind_sp) = id0 ->
        raise Occur
    | Construct cstr_sp
	when id_of_global (ConstructRef cstr_sp) = id0 ->
        raise Occur
    | Rel p when p>n & occur_rel (p-n) nenv id0 -> raise Occur
    | _ -> iter_constr_with_binders succ occur n c
  in 
  try occur 1 c; false
  with Occur -> true
    | Not_found -> false (* Case when a global is not in the env *)

type avoid_flags = bool option

let next_name_not_occuring avoid_flags name l env_names t =
  let rec next id =
    if List.mem id l or occur_id env_names id t or 
      (* Further restrictions ? *)
      match avoid_flags with None -> false | Some not_only_cstr ->
      (if not_only_cstr then
	(* To be consistent with the intro mechanism *)
	is_global id & not (is_section_variable id)
      else
	(* To avoid constructors in pattern-matchings *)
	is_constructor id)
    then next (lift_ident id)
    else id
  in 
  match name with
    | Name id   -> next id
    | Anonymous -> 
        (* Normally, an anonymous name is not dependent and will not be *)
        (* taken into account by the function concrete_name; just in case *)
        (* invent a valid name *)
        next (id_of_string "H")

let base_sort_cmp pb s0 s1 =
  match (s0,s1) with
    | (Prop c1, Prop c2) -> c1 = Null or c2 = Pos  (* Prop <= Set *)
    | (Prop c1, Type u)  -> pb = Reduction.CUMUL
    | (Type u1, Type u2) -> true
    | _ -> false

(* eq_constr extended with universe erasure *)
let rec constr_cmp cv_pb t1 t2 =
  (match kind_of_term t1, kind_of_term t2 with
      Sort s1, Sort s2 -> base_sort_cmp cv_pb s1 s2
    | _ -> false)
  || compare_constr (constr_cmp cv_pb) t1 t2

let eq_constr = constr_cmp Reduction.CONV

(* On reduit une serie d'eta-redex de tete ou rien du tout  *)
(* [x1:c1;...;xn:cn]@(f;a1...an;x1;...;xn) --> @(f;a1...an) *)
(* Remplace 2 versions précédentes buggées                  *)

let rec eta_reduce_head c =
  match kind_of_term c with
    | Lambda (_,c1,c') ->
	(match kind_of_term (eta_reduce_head c') with
           | App (f,cl) ->
               let lastn = (Array.length cl) - 1 in 
               if lastn < 1 then anomaly "application without arguments"
               else
                 (match kind_of_term cl.(lastn) with
                    | Rel 1 ->
			let c' =
                          if lastn = 1 then f
			  else mkApp (f, Array.sub cl 0 lastn)
			in
			if noccurn 1 c'
                        then lift (-1) c'
                        else c
                    | _   -> c)
           | _ -> c)
    | _ -> c


(* alpha-eta conversion : ignore print names and casts *)
let eta_eq_constr =
  let rec aux t1 t2 =
    let t1 = eta_reduce_head (strip_head_cast t1)
    and t2 = eta_reduce_head (strip_head_cast t2) in
    t1=t2 or compare_constr aux t1 t2
  in aux


(* iterator on rel context *)
let process_rel_context f env =
  let sign = named_context_val env in
  let rels = rel_context env in
  let env0 = reset_with_named_context sign env in
  Sign.fold_rel_context f rels ~init:env0

let assums_of_rel_context sign =
  Sign.fold_rel_context
    (fun (na,c,t) l ->
      match c with
          Some _ -> l
        | None -> (na, t)::l)
    sign ~init:[]

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

let fold_named_context_both_sides f l ~init = list_fold_right_and_left f l init

let rec mem_named_context id = function
  | (id',_,_) :: _ when id=id' -> true
  | _ :: sign -> mem_named_context id sign
  | [] -> false

let make_all_name_different env =
  let avoid = ref (ids_of_named_context (named_context env)) in
  process_rel_context
    (fun (na,c,t) newenv -> 
       let id = next_name_away na !avoid in
       avoid := id::!avoid;
       push_rel (Name id,c,t) newenv)
    env

let global_vars env ids = Idset.elements (global_vars_set env ids)

let global_vars_set_of_decl env = function
  | (_,None,t) -> global_vars_set env t
  | (_,Some c,t) ->
      Idset.union (global_vars_set env t)
        (global_vars_set env c)

let default_x = id_of_string "x"

let rec next_name_away_in_cases_pattern id avoid =
  let id = match id with Name id -> id | Anonymous -> default_x in
  let rec next id =
    if List.mem id avoid or is_constructor id then next (lift_ident id)
    else id in
  next id

(* Remark: Anonymous var may be dependent in Evar's contexts *)
let concrete_name avoid_flags l env_names n c =
  if n = Anonymous & noccurn 1 c then
    (Anonymous,l)
  else
    let fresh_id = next_name_not_occuring avoid_flags n l env_names c in
    let idopt = if noccurn 1 c then Anonymous else Name fresh_id in
    (idopt, fresh_id::l)

let concrete_let_name avoid_flags l env_names n c =
  let fresh_id = next_name_not_occuring avoid_flags n l env_names c in
  (Name fresh_id, fresh_id::l)

let rec rename_bound_var env avoid c =
  let env_names = names_of_rel_context env in
  let rec rename avoid c =
    match kind_of_term c with
    | Prod (na,c1,c2)  ->
	let na',avoid' = concrete_name None avoid env_names na c2 in
	mkProd (na', c1, rename avoid' c2)
    | LetIn (na,c1,t,c2) ->
	let na',avoid' = concrete_let_name None avoid env_names na c2 in
	mkLetIn (na',c1,t, rename avoid' c2)
    | Cast (c,k,t) -> mkCast (rename avoid c, k,t)
    | _ -> c
  in
  rename avoid c

(* Combinators on judgments *)

let on_judgment f j = { uj_val = f j.uj_val; uj_type = f j.uj_type }
let on_judgment_value f j = { j with uj_val = f j.uj_val }
let on_judgment_type f j = { j with uj_type = f j.uj_type }

(* Cut a context ctx in 2 parts (ctx1,ctx2) with ctx1 containing k 
     variables *)
let context_chop k ctx =
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, ((_,Some _,_ as h)::t)) -> chop_aux (h::acc) (n, t)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> anomaly "context_chop"
  in chop_aux [] (k,ctx)

