(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

let print_sort = function
  | Prop Pos -> (str "Set")
  | Prop Null -> (str "Prop")
  | Type u -> (str "Type(" ++ Univ.pr_uni u ++ str ")")

let print_sort_family = function
  | InSet -> (str "Set")
  | InProp -> (str "Prop")
  | InType -> (str "Type")

let current_module = ref empty_dirpath

let set_module m = current_module := m

let new_univ = 
  let univ_gen = ref 0 in
  (fun sp ->
    incr univ_gen; 
    Univ.make_univ (!current_module,!univ_gen))

let new_sort_in_family = function 
  | InProp -> mk_Prop
  | InSet -> mk_Set
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
	   | Name id -> (id, None, type_app (lift i) t)
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
    | None -> mkProd (na, body_of_type t, c)
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

(* *)

(* strips head casts and flattens head applications *)
let rec strip_head_cast c = match kind_of_term c with
  | App (f,cl) -> 
      let rec collapse_rec f cl2 = match kind_of_term f with
	| App (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
	| Cast (c,_) -> collapse_rec c cl2
	| _ -> if cl2 = [||] then f else mkApp (f,cl2)
      in 
      collapse_rec f cl
  | Cast (c,t) -> strip_head_cast c
  | _ -> c

(* [map_constr_with_named_binders g f l c] maps [f l] on the immediate
   subterms of [c]; it carries an extra data [l] (typically a name
   list) which is processed by [g na] (which typically cons [na] to
   [l]) at each binder traversal (with name [na]); it is not recursive
   and the order with which subterms are processed is not specified *)

let map_constr_with_named_binders g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,t) -> mkCast (f l c, f l t)
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

let array_map_left f a = (* Ocaml does not guarantee Array.map is LR *)
  let l = Array.length a in (* (even if so), then we rewrite it *)
  if l = 0 then [||] else begin
    let r = Array.create l (f a.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i)
    done;
    r
  end

let array_map_left_pair f a g b =
  let l = Array.length a in
  if l = 0 then [||],[||] else begin
    let r = Array.create l (f a.(0)) in
    let s = Array.create l (g b.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i);
      s.(i) <- g b.(i)
    done;
    r, s
  end

let fold_rec_types g (lna,typarray,_) e =
  let ctxt =
    array_map2_i
      (fun i na t -> (na, None, type_app (lift i) t)) lna typarray in
  Array.fold_left
    (fun e assum -> g assum e) e ctxt


let map_constr_with_binders_left_to_right g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,t) -> let c' = f l c in mkCast (c', f l t)
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
      let p' = f l p in let c' = f l c in
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
let map_constr_with_full_binders g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,t) -> mkCast (f l c, f l t)
  | Prod (na,t,c) -> mkProd (na, f l t, f (g (na,None,t) l) c)
  | Lambda (na,t,c) -> mkLambda (na, f l t, f (g (na,None,t) l) c)
  | LetIn (na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g (na,Some b,t) l) c)
  | App (c,al) -> mkApp (f l c, Array.map (f l) al)
  | Evar (e,al) -> mkEvar (e, Array.map (f l) al)
  | Case (ci,p,c,bl) -> mkCase (ci, f l p, f l c, Array.map (f l) bl)
  | Fix (ln,(lna,tl,bl)) ->
      let l' =
        array_fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      mkFix (ln,(lna,Array.map (f l) tl, Array.map (f l') bl))
  | CoFix(ln,(lna,tl,bl)) ->
      let l' =
        array_fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      mkCoFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))


(* Equality modulo let reduction *)
let rec zeta_eq_constr m n = 
  (m==n) or
  match kind_of_term m, kind_of_term n with
    | LetIn(_,v1,_,b1),_ -> zeta_eq_constr (subst1 v1 b1) n
    | _,LetIn(_,v2,_,b2) -> zeta_eq_constr m (subst1 v2 b2)
    | _ -> compare_constr zeta_eq_constr m n

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
    | None -> occur_var env hyp (body_of_type typ)
    | Some body ->
        occur_var env hyp (body_of_type typ) ||
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


(* (dependent M N) is true iff M is eq_term with a subterm of N 
   M is appropriately lifted through abstractions of N *)

let dependent m t =
  let rec deprec m t =
    if zeta_eq_constr m t then
      raise Occur
    else
      iter_constr_with_binders (lift 1) deprec m t
  in 
  try deprec m t; false with Occur -> true

let pop t = lift (-1) t

(***************************)
(*  substitution functions *)                         
(***************************)

let rec subst_meta bl c = 
  match kind_of_term c with
    | Meta i -> (try List.assoc i bl with Not_found -> c)
    | _ -> map_constr (subst_meta bl) c

(* Equality modulo let reduction *)
let rec whd_locals env c =
  match kind_of_term c with
      Rel i ->
        (try
          (match lookup_rel i env with
              (_,Some v,_) -> whd_locals env (lift i v)
            | _ -> c)
         with Not_found -> c)
    | Var id ->
        (try
          (match lookup_named id env with
              (_,Some v,_) -> whd_locals env v
            | _ -> c)
         with Not_found -> c)
    | _ -> c

(* Expand de Bruijn indices bound to a value *)
let rec nf_locals env c =
  map_constr_with_full_binders push_rel nf_locals env (whd_locals env c)

(* compare terms modulo expansion of let and local variables *)
let compare_zeta env m n = zeta_eq_constr m (nf_locals env n)

(* First utilities for avoiding telescope computation for subst_term *)

let prefix_application eq_fun (e,k,c) (t : constr) = 
  let c' = collapse_appl c and t' = collapse_appl t in
  match kind_of_term c', kind_of_term t' with
    | App (f1,cl1), App (f2,cl2) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2
	   && eq_fun e c' (mkApp (f2, Array.sub cl2 0 l1)) then
	  Some (mkApp (mkRel k, Array.sub cl2 l1 (l2 - l1)))
	else 
	  None
    | _ -> None

let my_prefix_application eq_fun (e,k,c) (by_c : constr) (t : constr) = 
  let c' = collapse_appl c and t' = collapse_appl t in
  match kind_of_term c', kind_of_term t' with
    | App (f1,cl1), App (f2,cl2) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2
	   && eq_fun e c' (mkApp (f2, Array.sub cl2 0 l1)) then
	  Some (mkApp ((lift k by_c), Array.sub cl2 l1 (l2 - l1)))
	else 
	  None
    | _ -> None

(* Recognizing occurrences of a given (closed) subterm in a term for Pattern :
   [subst_term c t] substitutes [(Rel 1)] for all occurrences of (closed)
   term [c] in a term [t] *)
(*i Bizarre : si on cherche un sous terme clos, pourquoi le lifter ? i*)

let subst_term_gen eq_fun env c t = 
  let rec substrec (e,k,c as kc) t =
    match prefix_application eq_fun kc t with
      | Some x -> x
      | None ->
    (if eq_fun e c t then mkRel k
     else
       map_constr_with_full_binders
         (fun d (e,k,c) -> (push_rel d e,k+1,lift 1 c))
         substrec kc t)
  in 
  substrec (env,1,nf_locals env c) t

(* Recognizing occurrences of a given (closed) subterm in a term :
   [replace_term c1 c2 t] substitutes [c2] for all occurrences of (closed)
   term [c1] in a term [t] *)
(*i Meme remarque : a priori [c] n'est pas forcement clos i*)

let replace_term_gen eq_fun env c by_c in_t = 
  let rec substrec (e,k,c as kc) t =
    match my_prefix_application eq_fun kc by_c t with
      | Some x -> x
      | None ->
    (if eq_fun e c t then (lift k by_c) else
      map_constr_with_full_binders
	(fun d (e,k,c) -> (push_rel d e,k+1,lift 1 c))
	substrec kc t)
  in 
  substrec (env,0,nf_locals env c) in_t

let subst_term = subst_term_gen (fun _ -> eq_constr) empty_env

let replace_term = replace_term_gen (fun _ -> eq_constr) empty_env

(* Substitute only a list of locations locs, the empty list is
   interpreted as substitute all, if 0 is in the list then no
   substitution is done. The list may contain only negative occurrences
   that will not be substituted. *)

let subst_term_occ_gen env locs occ c t =
  let maxocc = List.fold_right max locs 0 in
  let pos = ref occ in
  let check = ref true in
  let except = List.exists (fun n -> n<0) locs in
  if except & (List.exists (fun n -> n>=0) locs) 
  then error "mixing of positive and negative occurences"
  else
   let rec substrec (e,k,c as kc) t =
    if (not except) & (!pos > maxocc) then t
    else
    if compare_zeta e c t then
      let r = 
	if except then 
	  if List.mem (- !pos) locs then t else (mkRel k)
	else 
	  if List.mem !pos locs then (mkRel k) else t
      in incr pos; r
    else
      map_constr_with_binders_left_to_right
	(fun d (e,k,c) -> (push_rel d e,k+1,lift 1 c))
        substrec kc t
  in
  let t' = substrec (env,1,nf_locals env c) t in
  (!pos, t')

let subst_term_occ env locs c t = 
  if locs = [] then
    subst_term_gen compare_zeta env c t
  else if List.mem 0 locs then 
    t
  else 
    let (nbocc,t') = subst_term_occ_gen env locs 1 c t in
    if List.exists (fun o -> o >= nbocc or o <= -nbocc) locs then
      errorlabstrm "subst_term_occ" (str "Too few occurences");
    t'

let subst_term_occ_decl env locs c (id,bodyopt,typ as d) =
  match bodyopt with
    | None -> (id,None,subst_term_occ env locs c typ)
    | Some body -> 
	if locs = [] then
	  (id,Some (subst_term c body),type_app (subst_term c) typ)
	else if List.mem 0 locs then 
	  d
	else 
	  let (nbocc,body') = subst_term_occ_gen env locs 1 c body in
	  let (nbocc',t') = subst_term_occ_gen env locs nbocc c typ in
	  if List.exists (fun o -> o >= nbocc' or o <= -nbocc') locs then
	    errorlabstrm "subst_term_occ_decl" (str "Too few occurences");
	  (id,Some body',t')


(* First character of a constr *)

let first_char id =
  let id = string_of_id id in
  assert (id <> "");
  String.make 1 id.[0]

let lowercase_first_char id = String.lowercase (first_char id)

let id_of_global env ref = Nametab.id_of_global (Some (named_context env)) ref

let sort_hdchar = function
  | Prop(_) -> "P"
  | Type(_) -> "T"

let hdchar env c = 
  let rec hdrec k c =
    match kind_of_term c with
    | Prod (_,_,c)       -> hdrec (k+1) c
    | Lambda (_,_,c)     -> hdrec (k+1) c
    | LetIn (_,_,_,c)    -> hdrec (k+1) c
    | Cast (c,_)         -> hdrec k c
    | App (f,l)         -> hdrec k f
    | Const kn       ->
	let c = lowercase_first_char (id_of_label (label kn)) in
	if c = "?" then "y" else c
    | Ind ((kn,i) as x) ->
	if i=0 then 
	  lowercase_first_char (id_of_label (label kn))
	else 
	  lowercase_first_char (id_of_global env (IndRef x))
    | Construct ((sp,i) as x) ->
	lowercase_first_char (id_of_global env (ConstructRef x))
    | Var id  -> lowercase_first_char id
    | Sort s -> sort_hdchar s
    | Rel n ->
	(if n<=k then "p" (* the initial term is flexible product/function *)
	 else
	   try match Environ.lookup_rel (n-k) env with
	     | (Name id,_,_)   -> lowercase_first_char id
	     | (Anonymous,_,t) -> hdrec 0 (lift (n-k) (body_of_type t))
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

let named_hd_type env a = named_hd env (body_of_type a)

let prod_name   env (n,a,b) = mkProd (named_hd_type env a n, a, b)
let lambda_name env (n,a,b) = mkLambda (named_hd_type env a n, a, b)

let prod_create   env (a,b) = mkProd (named_hd_type env a Anonymous, a, b)
let lambda_create env (a,b) =  mkLambda (named_hd_type env a Anonymous, a, b)

let name_assumption env (na,c,t) =
  match c with
    | None      -> (named_hd_type env t na, None, t)
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

(* Nouvelle version de renommage des variables (DEC 98) *)
(* This is the algorithm to display distinct bound variables 

    - R�gle 1 : un nom non anonyme, m�me non affich�, contribue � la liste
      des noms � �viter 
    - R�gle 2 : c'est la d�pendance qui d�cide si on affiche ou pas

    Exemple : 
    si bool_ind = (P:bool->Prop)(f:(P true))(f:(P false))(b:bool)(P b), alors
    il est affich� (P:bool->Prop)(P true)->(P false)->(b:bool)(P b)
    mais f et f0 contribue � la liste des variables � �viter (en supposant 
    que les noms f et f0 ne sont pas d�j� pris)
    Int�r�t : noms homog�nes dans un but avant et apr�s Intro
*)

type used_idents = identifier list

let occur_rel p env id = 
  try lookup_name_of_rel p env = Name id
  with Not_found -> false (* Unbound indice : may happen in debug *)

let occur_id env nenv id0 c =
  let rec occur n c = match kind_of_term c with
    | Var id when  id=id0 -> raise Occur
    | Const kn when id_of_global env (ConstRef kn) = id0 -> raise Occur
    | Ind ind_sp
	when id_of_global env (IndRef ind_sp) = id0 ->
        raise Occur
    | Construct cstr_sp
	when id_of_global env (ConstructRef cstr_sp) = id0 ->
        raise Occur
    | Rel p when p>n & occur_rel (p-n) nenv id0 -> raise Occur
    | _ -> iter_constr_with_binders succ occur n c
  in 
  try occur 1 c; false
  with Occur -> true
    | Not_found -> false (* Case when a global is not in the env *)

let next_name_not_occuring env name l env_names t =
  let rec next id =
    if List.mem id l or occur_id env env_names id t then next (lift_ident id)
    else id
  in 
  match name with
    | Name id   -> next id
    | Anonymous -> id_of_string "_"

(* On reduit une serie d'eta-redex de tete ou rien du tout  *)
(* [x1:c1;...;xn:cn]@(f;a1...an;x1;...;xn) --> @(f;a1...an) *)
(* Remplace 2 versions pr�c�dentes bugg�es                  *)

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
  let sign = named_context env in
  let rels = rel_context env in
  let env0 = reset_with_named_context sign env in
  Sign.fold_rel_context f rels ~init:env0

let assums_of_rel_context sign =
  Sign.fold_rel_context
    (fun (na,c,t) l ->
      match c with
          Some _ -> l
        | None -> (na,body_of_type t)::l)
    sign ~init:[]

let lift_rel_context n sign =
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,option_app (liftn n k) c,type_app (liftn n k) t)
	::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (rel_context_length sign) sign

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
  | (_,None,t) -> global_vars_set env (body_of_type t)
  | (_,Some c,t) ->
      Idset.union (global_vars_set env (body_of_type t))
        (global_vars_set env c)

(* Remark: Anonymous var may be dependent in Evar's contexts *)
let concrete_name env l env_names n c =
  if n = Anonymous & noccurn 1 c then
    (None,l)
  else
    let fresh_id = next_name_not_occuring env n l env_names c in
    let idopt = if noccurn 1 c then None else (Some fresh_id) in
    (idopt, fresh_id::l)

let concrete_let_name env l env_names n c =
  let fresh_id = next_name_not_occuring env n l env_names c in
  (Name fresh_id, fresh_id::l)

let rec rename_bound_var env l c =
  match kind_of_term c with
  | Prod (Name s,c1,c2)  ->
      if noccurn 1 c2 then
        let env' = push_rel (Name s,None,c1) env in
	mkProd (Name s, c1, rename_bound_var env' l c2)
      else 
        let s' = next_ident_away s (global_vars env c2@l) in
        let env' = push_rel (Name s',None,c1) env in
        mkProd (Name s', c1, rename_bound_var env' (s'::l) c2)
  | Prod (Anonymous,c1,c2) ->
        let env' = push_rel (Anonymous,None,c1) env in
        mkProd (Anonymous, c1, rename_bound_var env' l c2)
  | Cast (c,t) -> mkCast (rename_bound_var env l c, t)
  | x -> c
