(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Names
open Term
open Declarations
open Util
open Miniml
open Nametab
open Table
open Options

(*s Exceptions. *)

exception Found
exception Impossible

(*s Dummy names. *)

let anonymous = id_of_string "x"
let prop_name = id_of_string "_"

let no_prop_name = 
  List.map (fun i -> if i=prop_name then anonymous else i)

(*s In an ML type, update the arguments to all inductive types [(sp,_)] *)  

let rec update_args sp vl = function  
  | Tapp ( Tglob r :: l ) -> 
      (match r with 
	| IndRef (s,_) when s = sp -> Tapp ( Tglob r :: l @ vl )
	| _ -> Tapp (Tglob r :: (List.map (update_args sp vl) l)))
  | Tapp l -> Tapp (List.map (update_args sp vl) l) 
  | Tarr (a,b)-> 
      Tarr (update_args sp vl a, update_args sp vl b)
  | a -> a

(*s Informative singleton optimization *)

(* We simplify informative singleton inductive, i.e. an inductive with one 
   constructor which has one informative argument. *) 

let rec type_mem r0 = function 
    | Tglob r when r=r0 -> true
    | Tapp l -> List.exists (type_mem r0) l
    | Tarr (a,b) -> (type_mem r0 a) || (type_mem r0 b)
    | _ -> false

let singletons = ref Refset.empty

let is_singleton r = Refset.mem r !singletons 

let add_singleton r = singletons:= Refset.add r !singletons

let clear_singletons () = singletons:= Refset.empty

(*s [collect_lams MLlam(id1,...MLlam(idn,t)...)] returns
    the list [idn;...;id1] and the term [t]. *)

let collect_lams = 
  let rec collect acc = function
    | MLlam(id,t) -> collect (id::acc) t
    | x           -> acc,x
  in collect []

(* [collect_n_lams] does the same for a precise number of [MLlam] *)

let collect_n_lams = 
  let rec collect acc n t = 
    if n = 0 then acc,t 
    else match t with 
      | MLlam(id,t) -> collect (id::acc) (n-1) t
      | _ -> assert false
  in collect [] 

(* [remove_n_lams] just remove some [MLlam] *)

let rec remove_n_lams n t = 
  if n = 0 then t  
  else match t with 
      | MLlam(_,t) -> remove_n_lams (n-1) t
      | _ -> assert false

(* [nb_lams] gives the number of head [MLlam] *)

let rec nb_lams = function 
  | MLlam(_,t) -> succ (nb_lams t)
  | _ -> 0 

(*s [named_lams] does the converse of [collect_lams] *)

let rec named_lams a = function 
  | [] -> a 
  | id :: ids -> named_lams (MLlam(id,a)) ids

(* The same in anonymous version. *)

let rec anonym_lams a = function 
  | 0 -> a 
  | n -> anonym_lams (MLlam(anonymous,a)) (pred n)

(*s The following function create [MLrel n;...;MLrel 1] *)

let rec make_eta_args n = 
  if n = 0 then [] else (MLrel n)::(make_eta_args (pred n))

(* This one tests [MLrel (n+k); ... ;MLrel (1+k)] *)

let rec test_eta_args_lift k n = function 
  | [] -> n=0
  | a :: q -> (a = (MLrel (k+n))) && (test_eta_args_lift k (pred n) q)
  
(*s Generic functions overs [ml_ast]. *)

(* [ast_iter_rel f t] applies [f] on every [MLrel] in t. It takes care 
   of the number of bingings crossed before reaching the [MLrel]. *)

let ast_iter f = 
  let rec iter n = function
    | MLrel i -> f (i-n)
    | MLlam (_,a) -> iter (n+1) a
    | MLletin (_,a,b) -> iter n a; iter (n+1) b
    | MLcase (a,v) ->
	iter n a; Array.iter (fun (_,l,t) -> iter (n + (List.length l)) t) v
    | MLfix (_,ids,v) -> let k = Array.length ids in Array.iter (iter (n+k)) v
    | MLapp (a,l) -> iter n a; List.iter (iter n) l
    | MLcons (_,l) ->  List.iter (iter n) l
    | MLcast (a,_) -> iter n a
    | MLmagic a -> iter n a
    | MLglob _ | MLexn _ | MLprop | MLarity -> ()
  in iter 0 

(* Map over asts. *)

let ast_map_case f (c,ids,a) = (c,ids,f a)

let ast_map f = function
  | MLlam (i,a) -> MLlam (i, f a)
  | MLletin (i,a,b) -> MLletin (i, f a, f b)
  | MLcase (a,v) -> MLcase (f a, Array.map (ast_map_case f) v)
  | MLfix (i,ids,v) -> MLfix (i, ids, Array.map f v)
  | MLapp (a,l) -> MLapp (f a, List.map f l)
  | MLcons (c,l) -> MLcons (c, List.map f l)
  | MLcast (a,t) -> MLcast (f a, t)
  | MLmagic a -> MLmagic (f a)
  | MLrel _ | MLglob _ | MLexn _ | MLprop | MLarity as a -> a

(* Map over asts, with binding depth as parameter. *)

let ast_map_lift_case f n (c,ids,a) = (c,ids, f (n+(List.length ids)) a)

let ast_map_lift f n = function 
  | MLlam (i,a) -> MLlam (i, f (n+1) a)
  | MLletin (i,a,b) -> MLletin (i, f n a, f (n+1) b)
  | MLcase (a,v) -> MLcase (f n a,Array.map (ast_map_lift_case f n) v)
  | MLfix (i,ids,v) -> 
      let k = Array.length ids in MLfix (i,ids,Array.map (f (k+n)) v)
  | MLapp (a,l) -> MLapp (f n a, List.map (f n) l)
  | MLcons (c,l) -> MLcons (c, List.map (f n) l)
  | MLcast (a,t) -> MLcast (f n a, t)
  | MLmagic a -> MLmagic (f n a)
  | MLrel _ | MLglob _ | MLexn _ | MLprop | MLarity as a -> a	

(*s [occurs k t] returns true if [(Rel k)] occurs in [t]. *)

let occurs k t = 
  try ast_iter (fun i -> if i = k then raise Found) t; false with Found -> true

(*s [occurs_itvl k k' t] return true if there is a [(Rel i)] 
   in [t] with [k<=i<=k'] *)

let occurs_itvl k k' t = 
  try 
    ast_iter (fun i -> if (k <= i) && (i <= k') then raise Found) t; false 
  with Found -> true

(*s Number of occurences of [Rel k] and [Rel 1] in [t]. *)

let nb_occur_k k t =
  let cpt = ref 0 in 
  ast_iter (fun i -> if i = k then incr cpt) t;
  !cpt

let nb_occur t = nb_occur_k 1 t

(*s Lifting on terms.
    [ml_lift k t] lifts the binding depth of [t] across [k] bindings. *)

let ml_lift k t = 
  let rec liftrec n = function
    | MLrel i as a -> if i-n < 1 then a else MLrel (i+k)
    | a -> ast_map_lift liftrec n a
  in if k = 0 then t else liftrec 0 t

let ml_pop t = ml_lift (-1) t

(*s [permut_rels k k' c] translates [Rel 1 ... Rel k] to [Rel (k'+1) ... 
  Rel (k'+k)] and [Rel (k+1) ... Rel (k+k')] to [Rel 1 ... Rel k'] *)

let permut_rels k k' = 
  let rec permut n = function
    | MLrel i as a ->
	let i' = i-n in
	if i'<1 || i'>k+k' then a 
	else if i'<=k then MLrel (i+k')
	else MLrel (i-k)
    | a -> ast_map_lift permut n a
  in permut 0  

(*s Substitution. [ml_subst e t] substitutes [e] for [Rel 1] in [t]. 
    Lifting (of one binder) is done at the same time. *)

let rec ml_subst e =
  let rec subst n = function
    | MLrel i as a ->
	let i' = i-n in 
	if i'=1 then ml_lift n e
	else if i'<1 then a 
	else MLrel (i-1)
    | a -> ast_map_lift subst n a
  in subst 0

(*s Simplification of any [MLapp (MLapp (_,_),_)] *)

let rec merge_app = function 
  | MLapp (f,l) -> 
      let f = merge_app f in 
      let l = List.map merge_app l in 
      (match f with 
	 | MLapp (f',l') -> MLapp (f',l' @ l)
	 | _ -> MLapp (f,l))
  | a -> ast_map merge_app a

(*s [check_and_generalize (r0,l,c)] transforms any [MLcons(r0,l)] in [MLrel 1]
  and raises [Impossible] if any variable in [l] occurs outside such a 
  [MLcons] *)

let check_and_generalize (r0,l,c) = 
  let nargs = List.length l in 
  let rec genrec n = function 
    | MLrel i as c -> 
	let i' = i-n in 
	if i'<1 then c 
	else if i'>nargs then MLrel (i-nargs+1) 
	else raise Impossible
    | MLcons(r,args) when r=r0 && (test_eta_args_lift n nargs args) -> MLrel (n+1) 
    | a -> ast_map_lift genrec n a
  in genrec 0 c  

(*s Auxialiary functions used during simplifications of [MLcase]. *)

let check_generalizable_case br = 
  let f = check_and_generalize br.(0) in 
  for i = 1 to Array.length br - 1 do 
    if check_and_generalize br.(i) <> f then raise Impossible 
  done; f

let check_constant_case br = 
  if br = [||] then raise Impossible; 
  let (r,l,t) = br.(0) in
  let n = List.length l in 
  if occurs_itvl 1 n t then raise Impossible; 
  let cst = ml_lift (-n) t in 
  for i = 1 to Array.length br - 1 do 
    let (r,l,t) = br.(i) in
    let n = List.length l in
    if (occurs_itvl 1 n t) || (cst <> (ml_lift (-n) t)) 
    then raise Impossible
  done; cst

let rec permut_case_fun br acc = 
  let (_,_,t0) = br.(0) in 
  let nb = ref (nb_lams t0) in 
  Array.iter (fun (_,_,t) -> let n = nb_lams t in if n < !nb then nb:=n) br;
  let ids,_ = collect_n_lams !nb t0 in 
  for i = 0 to Array.length br - 1 do 
    let (r,l,t) = br.(i) in 
    let t = permut_rels !nb (List.length l) (remove_n_lams !nb t) 
    in br.(i) <- (r,l,t)
  done; ids

(*s Generalized iota-reduction. *)

(* Definition of a generalized iota-redex: it's a [MLcase(e,_)] 
   with [(is_iota_gen e)=true]. *)

let rec is_iota_gen = function 
  | MLcons _ -> true
  | MLcase(_,br)-> array_for_all (fun (_,_,t)->is_iota_gen t) br
  | _ -> false

let constructor_index = function
  | ConstructRef (_,j) -> pred j
  | _ -> assert false

(* Any generalized iota-redex is transformed into beta-redexes. *)

let iota_gen br = 
  let rec iota k = function 
    | MLcons (r,a) ->
	let (_,ids,c) = br.(constructor_index r) in
	let c = List.fold_right (fun id t -> MLlam (id,t)) ids c in
	let c = ml_lift k c in 
	MLapp (c,a)
    | MLcase(e,br') -> 
	let new_br = 
	  Array.map (fun (n,i,c)->(n,i,iota (k+(List.length i)) c)) br'
	in MLcase(e, new_br)
    | _ -> assert false
  in iota 0 

(*s Some beta-iota reductions + simplifications. *)

let is_atomic = function 
  | MLrel _ | MLglob _ | MLexn _ | MLprop | MLarity -> true
  | _ -> false

let rec simplify o = function
  | MLapp (f, []) ->
      simplify o f
  | MLapp (f, a) -> 
      simplify_app o (List.map (simplify o) a) (simplify o f)
  | MLcons (r,[t]) when is_singleton r -> simplify o t 
	(* Informative singleton *) 
  | MLcase (e,[||]) ->
      MLexn "empty inductive"
  | MLcase (e,[|r,[i],c|]) when is_singleton r -> (* Informative singleton *)
      simplify o (MLletin (i,e,c))
  | MLcase (e,br) ->
      let br = Array.map (fun (n,l,t) -> (n,l,simplify o t)) br in 
      simplify_case o br (simplify o e) 
  | MLletin(_,c,e) when (is_atomic c) || (nb_occur e <= 1) -> 
      (* Expansion of a letin in special cases *)
      simplify o (ml_subst c e)
  | MLfix(i,ids,c) as t when o -> 
      let n = Array.length ids in 
      if occurs_itvl 1 n c.(i) then 
	MLfix (i, ids, Array.map (simplify o) c)
      else simplify o (ml_lift (-n) c.(i)) (* Dummy fixpoint *)
  | a -> ast_map (simplify o) a 
	
and simplify_app o a = function  
  | MLlam (id,t) -> (* Beta redex *)
      (match nb_occur t with
	 | 0 -> simplify o (MLapp (ml_pop t, List.tl a))
	 | 1 when o -> 
	     simplify o (MLapp (ml_subst (List.hd a) t, List.tl a))
	 | _ -> 
	     let a' = List.map (ml_lift 1) (List.tl a) in
	     simplify o (MLletin (id, List.hd a, MLapp (t, a'))))
  | MLletin (id,e1,e2) -> 
      (* Application of a letin: we push arguments inside *)
      MLletin (id, e1, simplify o (MLapp (e2, List.map (ml_lift 1) a)))
  | MLcase (e,br) -> (* Application of a case: we push arguments inside *)
      let br' = 
	Array.map 
      	  (fun (n,l,t) -> 
	     let k = List.length l in
	     let a' = List.map (ml_lift k) a in
      	     (n, l, simplify o (MLapp (t,a')))) br 
      in simplify o (MLcase (e,br'))
  | f -> MLapp (f,a)

and simplify_case o br e = 
  if (not o) then MLcase (e,br)
  else 
    if (is_iota_gen e) then (* Generalized iota-redex *)
      simplify o (iota_gen br e)
    else 
      try (* Does a term [f] exist such as each branch is [(f e)] ? *)
	let f = check_generalizable_case br in 
	simplify o (MLapp (MLlam (anonymous,f),[e]))
      with Impossible -> 
	try (* Is each branch independant of [e] ? *) 
	  check_constant_case br 
	with Impossible ->
	  if (is_atomic e) then (* Swap the case and the lam if possible *)
	    let ids = no_prop_name (permut_case_fun br []) in 
	    let n = List.length ids in 
	    if n = 0 then MLcase (e, br) 
	    else named_lams (MLcase (ml_lift n e, br)) ids
	  else MLcase (e, br)

let normalize a = simplify (optim()) (merge_app a)

(*s Special treatment of non-mutual fixpoint for pretty-printing purpose. *)

let optimize_fix a = 
  if not (optim()) then a 
  else
    let ids,a' = collect_lams a in 
    let n = List.length ids in 
    if n = 0 then a 
    else  
      (match a' with 
	 | MLfix(_,[|f|],[|c|]) ->
	     let new_f = MLapp (MLrel (n+1),make_eta_args n) in 
	     let new_c = named_lams (ml_subst new_f c) ids
	     in MLfix(0,[|f|],[|new_c|])
	 | MLapp(a',args) ->
	     let m = List.length args in 
	     (match a' with 
		| MLfix(_,[|_|],[|_|]) when 
		    (test_eta_args_lift 0 n args) && not (occurs_itvl 1 m a') 
		    -> a'
		| MLfix(_,[|f|],[|c|]) -> 
		    let v = Array.make n 0 in 
		    for i=0 to (n-1) do v.(i)<-i done;
		    let aux i = function 
			MLrel j when v.(j-1)>=0 -> v.(j-1)<-(-i-1)
		      | _ -> raise Impossible
		    in
		    (try 
		       list_iter_i aux args; 
		       let args_f = 
			 List.rev_map 
			   (fun i -> MLrel (i+m+1)) (Array.to_list v) in
		       let new_f = 
			 anonym_lams (MLapp (MLrel (n+m+1),args_f)) m in  
		       let new_c = 
			 named_lams 
			   (normalize (MLapp ((ml_subst new_f c),args))) ids
		       in MLfix(0,[|f|],[|new_c|])
		     with Impossible -> a) 
		| _ -> a)
	 | _ -> a)


(*s Utility functions used for the decision of expansion. *)

let rec ml_size = function
  | MLapp(t,l) -> List.length l + ml_size t + ml_size_list l
  | MLlam(_,t) -> 1 + ml_size t
  | MLcons(_,l) -> ml_size_list l
  | MLcase(t,pv) -> 
      1 + ml_size t + (Array.fold_right (fun (_,_,t) a -> a + ml_size t) pv 0)
  | MLfix(_,_,f) -> ml_size_array f
  | MLletin (_,_,t) -> ml_size t
  | MLcast (t,_) -> ml_size t
  | MLmagic t -> ml_size t
  | _ -> 0

and ml_size_list l = List.fold_left (fun a t -> a + ml_size t) 0 l

and ml_size_array l = Array.fold_left (fun a t -> a + ml_size t) 0 l

let is_fix = function MLfix _ -> true | _ -> false

let rec is_constr = function
  | MLcons _   -> true
  | MLlam(_,t) -> is_constr t
  | _          -> false

(*s Strictness *)

(* A variable is strict if the evaluation of the whole term implies
   the evaluation of this variable. Non-strict variables can be found 
   behind Match, for example. Expanding a term [t] is a good idea when 
   it begins by at least one non-strict lambda, since the corresponding 
   argument to [t] might be unevaluated in the expanded code. *)

exception Toplevel

let lift n l = List.map ((+) n) l

let pop n l = List.map (fun x -> if x<=n then raise Toplevel else x-n) l 

(* This function returns a list of de Bruijn indices of non-strict variables,
   or raises [Toplevel] if it has an internal non-strict variable. 
   In fact, not all variables are checked for strictness, only the ones which 
   de Bruijn index is in the candidates list [cand]. The flag [add] controls 
   the behaviour when going through a lambda: should we add the corresponding 
   variable to the candidates?  We use this flag to check only the external 
   lambdas, those that will correspond to arguments. *)

let rec non_stricts add cand = function 
  | MLlam (id,t) -> 
      let cand = lift 1 cand in
      let cand = if add then 1::cand else cand in
      pop 1 (non_stricts add cand t)
  | MLrel n -> 
      List.filter ((<>) n) cand  
  | MLapp (MLrel n, _) -> 
      List.filter ((<>) n) cand
	(* In [(x y)] we say that only x is strict. Cf [sig_rec]. 
	   We may gain something if x is replaced by a function like
	   a projection *)
  | MLapp (t,l)-> 
      let cand = non_stricts false cand t in 
      List.fold_left (non_stricts false) cand l 
  | MLcons (_,l) -> 
      List.fold_left (non_stricts false) cand l
  | MLletin (_,t1,t2) -> 
      let cand = non_stricts false cand t1 in 
      pop 1 (non_stricts add (lift 1 cand) t2)
  | MLfix (_,i,f)-> 
      let n = Array.length i in
      let cand = lift n cand in 
      let cand = Array.fold_left (non_stricts false) cand f in 
      pop n cand
  | MLcase (t,v) -> 
      (* The only interesting case: for a variable to be non-strict, 
	 it is sufficient that it appears non-strict in at least one branch,
	 so he make an union (in fact a merge). *)
      let cand = non_stricts false cand t in 
      Array.fold_left 
	(fun c (_,i,t)-> 
	   let n = List.length i in 
	   let cand = lift n cand in 
	   let cand = pop n (non_stricts add cand t) in
	   Sort.merge (<=) cand c) [] v
	(* [merge] may duplicates some indices, but I don't mind. *)
  | MLcast (t,_) -> 
      non_stricts add cand t
  | MLmagic t -> 
      non_stricts add cand t
  | _ -> 
      cand

(* The real test: we are looking for internal non-strict variables, so we start
   with no candidates, and the only positive answer is via the [Toplevel] 
   exception. *)

let is_not_strict t = 
  try 
    let _ = non_stricts true [] t in false
  with 
    | Toplevel -> true

(*s Expansion decision *)

(* [expansion_test] answers the following question: 
   If we could expand [t] (the user said nothing special), 
   should we expand ? 
   
   We don't expand fixpoints, but always inductive constructors
   and small terms.
   Last case of expansion is a term with at least one non-strict 
   variable (i.e. a variable that may not be evaluated). *)

let expansion_test t = 
  (not (is_fix t))
  &&
  ((is_constr t) ||
   (ml_size t < 3) ||
   ((ml_size t < 12) && (is_not_strict t)))

(* If the user doesn't say he wants to keep [t], we expand in two cases:
   \begin{itemize}
   \item the user explicitly requests it 
   \item [expansion_test] answers that the expansion is a good idea, and 
   we are free to act (AutoInline is set)
   \end{itemize} *)

let expand strict_lang r t = 
  (not (to_keep r)) (* The user DOES want to keep it *)
  &&
  ((to_inline r) (* The user DOES want to expand it *) 
   || 
   (auto_inline () && strict_lang && expansion_test t)) 

(*s Optimization *)

let subst_glob_ast r m = 
  let rec substrec = function
    | MLglob r' as t -> if r = r' then m else t
    | t -> ast_map substrec t
  in
  substrec

let subst_glob_decl r m = function
  | Dglob(r',t') -> Dglob(r', subst_glob_ast r m t')
  | d -> d

let warning_expansion r = 
  wARN (hOV 0 [< 'sTR "The constant"; 'sPC;
		 Printer.pr_global r; 
(*i    'sTR (" of size "^ (string_of_int (ml_size t))); i*)
    'sPC; 'sTR "is expanded." >])

let warning_expansion_must r = 
  wARN (hOV 0 [< 'sTR "The constant"; 'sPC;
		 Printer.pr_global r; 
    'sPC; 'sTR "must be expanded." >])

let print_ml_decl prm (r,_) = 
  not (to_inline r) || List.mem r prm.to_appear

let add_ml_decls prm decls = 
  let l = sorted_ml_extractions () in 
  let l = List.filter (print_ml_decl prm) l in 
  let l = List.map (fun (r,s)-> Dcustom (r,s)) l in 
  (List.rev l @ decls)

let strict_language = function
  | "ocaml" -> true
  | "haskell" -> false
  | _ -> assert false

let rec empty_ind = function 
  | [] -> [],[]
  | t :: q -> let l,l' = empty_ind q in 
    (match t with 
       | ids,r,[] -> Dabbrev (r,ids,Texn "empty inductive") :: l,l'
       | _ -> l,t::l')

let is_exn = function 
  | MLexn _ -> true
  | _ -> false

let rec optimize prm = function
  | [] -> 
      []
  | ( Dabbrev (r,_,Tarity) |
	Dabbrev(r,_,Tprop) | 
	  Dglob(r,MLarity) | 
	    Dglob(r,MLprop) ) as d :: l ->
      if List.mem r prm.to_appear then
	d :: (optimize prm l) 
      else optimize prm l
  | Dglob (r,t) :: l ->
      let t = normalize t in
      let b = expand (strict_language prm.lang) r t
      and b' = is_exn t in 
      let l = if b then 
	begin
	  if not (prm.toplevel) then if_verbose warning_expansion r;
	  List.map (subst_glob_decl r t) l
	end
      else if b' then 
	begin 
	  if not (prm.toplevel) then if_verbose warning_expansion_must r;
          List.map (subst_glob_decl r t) l
	end
      else l in 
      if not b' && 
	(not b || prm.mod_name <> None || List.mem r prm.to_appear) then 
	let t = optimize_fix t in
	Dglob (r,t) :: (optimize prm l)
      else 
	optimize prm l
  | (Dtype ([],_) | Dabbrev _ | Dcustom _) as d :: l -> 
      d :: (optimize prm l)
  | Dtype ([ids,r,[r0,[t0]]],false) :: l when not (type_mem r t0) ->
      (* Detection of informative singleton. *)
      add_singleton r0; 
      Dabbrev (r, ids, t0) :: (optimize prm l)
  | Dtype(il,b) :: l -> 
      (* Detection of empty inductives. *)
      let l1,l2 = empty_ind il in 
      if l2 = [] then l1 @ (optimize prm l) 
      else l1 @ (Dtype(l2,b) :: (optimize prm l))


