(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Term
open Declarations
open Util
open Miniml
open Nametab
open Table
open Options
open Nameops
(*i*)

(*s Exceptions. *)

exception Found
exception Impossible

(*S Names operations. *)

let anonymous = id_of_string "x"
let dummy_name = id_of_string "_"
let flex_name = id_of_string "flex"

let id_of_name = function
  | Anonymous -> anonymous
  | Name id when id = dummy_name -> anonymous
  | Name id -> id 

(*S Operations upon ML types. *)

(*s Get all type variables from a ML type *)

let get_tvars t = 
  let rec get_rec s = function 
  | Tvar i -> Idset.add i s
  | Tapp l -> List.fold_left get_rec s l 
  | Tarr (a,b) -> get_rec (get_rec s a) b
  | a -> s
  in Idset.elements (get_rec Idset.empty t)

(*s Does a section path occur in a ML type ? *)

let sp_of_r r = match r with 
    | ConstRef sp -> sp
    | IndRef (sp,_) -> sp
    | ConstructRef ((sp,_),_) -> sp
    | _ -> assert false

let rec type_mem_sp sp = function 
  | Tglob r when (sp_of_r r)=sp -> true
  | Tapp l -> List.exists (type_mem_sp sp) l
  | Tarr (a,b) -> (type_mem_sp sp a) || (type_mem_sp sp b)
  | _ -> false

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
  
(*S Generic functions over ML ast terms. *)

(*s [ast_iter_rel f t] applies [f] on every [MLrel] in t. It takes care 
   of the number of bingings crossed before reaching the [MLrel]. *)

let ast_iter_rel f = 
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
    | MLglob _ | MLexn _ | MLdummy -> ()
  in iter 0 

(*s Map over asts. *)

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
  | MLrel _ | MLglob _ | MLexn _ | MLdummy as a -> a

(*s Map over asts, with binding depth as parameter. *)

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
  | MLrel _ | MLglob _ | MLexn _ | MLdummy as a -> a	

(*s Iter over asts. *) 

let ast_iter_case f (c,ids,a) = f a

let ast_iter f = function
  | MLlam (i,a) -> f a
  | MLletin (i,a,b) -> f a; f b
  | MLcase (a,v) -> f a; Array.iter (ast_iter_case f) v
  | MLfix (i,ids,v) -> Array.iter f v
  | MLapp (a,l) -> f a; List.iter f l
  | MLcons (c,l) -> List.iter f l
  | MLcast (a,t) -> f a
  | MLmagic a -> f a
  | MLrel _ | MLglob _ | MLexn _ | MLdummy as a -> ()

(*S Operations concerning De Bruijn indices. *)

(*s [occurs k t] returns [true] if [(Rel k)] occurs in [t]. *)

let occurs k t = 
  try 
    ast_iter_rel (fun i -> if i = k then raise Found) t; false 
  with Found -> true

(*s [occurs_itvl k k' t] returns [true] if there is a [(Rel i)] 
   in [t] with [k<=i<=k'] *)

let occurs_itvl k k' t = 
  try 
    ast_iter_rel (fun i -> if (k <= i) && (i <= k') then raise Found) t; false 
  with Found -> true

(*s Number of occurences of [Rel k] and [Rel 1] in [t]. *)

let nb_occur_k k t =
  let cpt = ref 0 in 
  ast_iter_rel (fun i -> if i = k then incr cpt) t;
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

(*s Generalized substitution. 
   [gensubst v m d t] applies to [t] the substitution coded in the 
   [v] array: [(Rel i)] becomes [(Rel v.(i))]. [d] is the correction applies 
   to [Rel] greater than [m]. *)

let gen_subst v d t = 
  let rec subst n = function
    | MLrel i as a -> 
	let i'= i-n in 
	if i' < 1 then a 
	else if i' < Array.length v then MLrel (v.(i')+n) 
	else MLrel (i+d) 
    | a -> ast_map_lift subst n a
  in subst 0 t

(*S Operations concerning lambdas. *)

(*s [collect_lams MLlam(id1,...MLlam(idn,t)...)] returns
    [[idn;...;id1]] and the term [t]. *)

let collect_lams = 
  let rec collect acc = function
    | MLlam(id,t) -> collect (id::acc) t
    | x           -> acc,x
  in collect []

(*s [collect_n_lams] does the same for a precise number of [MLlam]. *)

let collect_n_lams = 
  let rec collect acc n t = 
    if n = 0 then acc,t 
    else match t with 
      | MLlam(id,t) -> collect (id::acc) (n-1) t
      | _ -> assert false
  in collect [] 

(*s [remove_n_lams] just removes some [MLlam]. *)

let rec remove_n_lams n t = 
  if n = 0 then t  
  else match t with 
      | MLlam(_,t) -> remove_n_lams (n-1) t
      | _ -> assert false

(*s [nb_lams] gives the number of head [MLlam]. *)

let rec nb_lams = function 
  | MLlam(_,t) -> succ (nb_lams t)
  | _ -> 0 

(*s [named_lams] does the converse of [collect_lams]. *)

let rec named_lams ids a = match ids with 
  | [] -> a 
  | id :: ids -> named_lams ids (MLlam (id,a))

(*s The same in anonymous version. *)

let rec anonym_lams a = function 
  | 0 -> a 
  | n -> anonym_lams (MLlam (anonymous,a)) (pred n)

(*s Idem for [dummy_name]. *)

let rec dummy_lams a = function 
  | 0 -> a 
  | n -> anonym_lams (MLlam (dummy_name,a)) (pred n)

(*S Operations concerning eta. *)

(*s The following function creates [MLrel n;...;MLrel 1] *)

let rec eta_args n = 
  if n = 0 then [] else (MLrel n)::(eta_args (pred n))

(*s This one tests [MLrel (n+k); ... ;MLrel (1+k)] *)

let rec test_eta_args_lift k n = function 
  | [] -> n=0
  | a :: q -> (a = (MLrel (k+n))) && (test_eta_args_lift k (pred n) q)

(*s Computes an eta-reduction. *)

let eta_red e = 
  let ids,t = collect_lams e in 
  let n = List.length ids in
  if n = 0 then e 
  else match t with 
    | MLapp (f,a) -> 
	let m = (List.length a) - n in 
	if m < 0 then e 
	else
	  let a1,a2 = list_chop m a in 
	  let f = if m = 0 then f else MLapp (f,a1) in 
	  if test_eta_args_lift 0 n a2 && not (occurs_itvl 1 n f)
	  then ml_lift (-n) f
	  else e 
    | _ -> e

(*S Auxiliary functions used in simplification of ML cases. *)

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
    | MLcons(r,args) when r=r0 && (test_eta_args_lift n nargs args) -> 
	MLrel (n+1) 
    | a -> ast_map_lift genrec n a
  in genrec 0 c  

(*s [check_generalizable_case] checks if all branches can be seen as the 
  same function [f] applied to the term matched. It is a generalized version 
  of the identity case optimization. *)

let check_generalizable_case br = 
  let f = check_and_generalize br.(0) in 
  for i = 1 to Array.length br - 1 do 
    if check_and_generalize br.(i) <> f then raise Impossible 
  done; f

(*s Do all branches correspond to the same thing? *)

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

(*s If all branches are functions, try to permut the case and the functions. *)

let rec merge_ids ids ids' = match ids,ids' with 
  | [],[] -> [] 
  | i::ids, i'::ids' -> 
      (if i = dummy_name then i' else i) :: (merge_ids ids ids')
  | _ -> assert false 

let rec permut_case_fun br acc = 
  let br = Array.copy br in 
  let (_,_,t0) = br.(0) in 
  let nb = ref (nb_lams t0) in 
  Array.iter (fun (_,_,t) -> let n = nb_lams t in if n < !nb then nb:=n) br;
  let ids = ref (fst (collect_n_lams !nb t0)) in  
  Array.iter 
    (fun (_,_,t) -> ids := merge_ids !ids (fst (collect_n_lams !nb t))) br; 
  for i = 0 to Array.length br - 1 do 
    let (r,l,t) = br.(i) in 
    let t = permut_rels !nb (List.length l) (remove_n_lams !nb t) 
    in br.(i) <- (r,l,t)
  done; 
  (!ids,br)
  
(*S Generalized iota-reduction. *)

(* Definition of a generalized iota-redex: it's a [MLcase(e,_)] 
   with [(is_iota_gen e)=true]. Any generalized iota-redex is 
   transformed into beta-redexes. *)

let rec is_iota_gen = function 
  | MLcons _ -> true
  | MLcase(_,br)-> array_for_all (fun (_,_,t)->is_iota_gen t) br
  | _ -> false

let constructor_index = function
  | ConstructRef (_,j) -> pred j
  | _ -> assert false

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

let is_atomic = function 
  | MLrel _ | MLglob _ | MLexn _ | MLdummy -> true
  | _ -> false

(*S The main simplification function. *)

(* Some beta-iota reductions + simplifications. *)

let rec simpl o = function
  | MLapp (f, []) ->
      simpl o f
  | MLapp (f, a) -> 
      simpl_app o (List.map (simpl o) a) (simpl o f)
  | MLcase (e,br) ->
      let br = Array.map (fun (n,l,t) -> (n,l,simpl o t)) br in 
      simpl_case o br (simpl o e) 
  | MLletin(id,c,e) when 
      (id = dummy_name) || (is_atomic c) || (nb_occur e <= 1) -> 
	simpl o (ml_subst c e)
  | MLletin(_,c,e) when (is_atomic (eta_red c)) -> 
      simpl o (ml_subst (eta_red c) e)
  | MLfix(i,ids,c) as t when o -> 
      let n = Array.length ids in 
      if occurs_itvl 1 n c.(i) then 
	MLfix (i, ids, Array.map (simpl o) c)
      else simpl o (ml_lift (-n) c.(i)) (* Dummy fixpoint *)
  | a -> ast_map (simpl o) a 

and simpl_app o a = function  
  | MLapp (f',a') -> simpl_app o (a'@a) f'
  | MLlam (id,t) when id = dummy_name -> 
      simpl o (MLapp (ml_pop t, List.tl a))
  | MLlam (id,t) -> (* Beta redex *)
      (match nb_occur t with
	 | 0 -> simpl o (MLapp (ml_pop t, List.tl a))
	 | 1 when o -> 
	     simpl o (MLapp (ml_subst (List.hd a) t, List.tl a))
	 | _ -> 
	     let a' = List.map (ml_lift 1) (List.tl a) in
	     simpl o (MLletin (id, List.hd a, MLapp (t, a'))))
  | MLletin (id,e1,e2) -> 
      (* Application of a letin: we push arguments inside *)
      MLletin (id, e1, simpl o (MLapp (e2, List.map (ml_lift 1) a)))
  | MLcase (e,br) -> (* Application of a case: we push arguments inside *)
      let br' = 
	Array.map 
      	  (fun (n,l,t) -> 
	     let k = List.length l in
	     let a' = List.map (ml_lift k) a in
      	     (n, l, simpl o (MLapp (t,a')))) br 
      in simpl o (MLcase (e,br')) 
  | (MLdummy | MLexn _) as e -> e 
	(* We just discard arguments in those cases. *)
  | f -> MLapp (f,a)

and simpl_case o br e = 
  if (not o) then MLcase (e,br)
  else 
    if (is_iota_gen e) then (* Generalized iota-redex *)
      simpl o (iota_gen br e)
    else 
      try (* Does a term [f] exist such as each branch is [(f e)] ? *)
	let f = check_generalizable_case br in 
	simpl o (MLapp (MLlam (anonymous,f),[e]))
      with Impossible -> 
	try (* Is each branch independant of [e] ? *) 
	  check_constant_case br 
	with Impossible ->
	  (* Swap the case and the lam if possible *)
	  let ids,br = permut_case_fun br [] in 
	  let n = List.length ids in 
	  if n = 0 then MLcase (e, br) 
	  else named_lams ids (MLcase (ml_lift n e, br))

(*S Local prop elimination. *) 
(* We try to eliminate as many [prop] as possible inside an [ml_ast]. *)

(*s In a list, it selects only the elements corresponding to a [true] 
   in the boolean list [l]. *)

let rec select_via_bl l args = match l,args with 
  | [],_ -> args
  | true::l,a::args -> a :: (select_via_bl l args)
  | false::l,a::args -> select_via_bl l args
  | _ -> assert false 

(*s [kill_some_lams] removes some head lambdas according to the bool list [bl].
   This list is build on the identifier list model: outermost lambda
   is on the right. [true] means "to keep" and [false] means "to eliminate". 
   [Rels] corresponding to removed lambdas are supposed not to occur, and 
   the other [Rels] are made correct via a [gen_subst].
   Output is not directly a [ml_ast], compose with [named_lams] if needed. *)

let kill_some_lams bl (ids,c) =
  let n = List.length bl in
  let n' = List.fold_left (fun n b -> if b then (n+1) else n) 0 bl in 
  if n = n' then ids,c
  else if n' = 0 then [],ml_lift (-n) c 
  else begin 
    let v = Array.make (n+1) 0 in 
    let rec parse_ids i j = function 
      | [] -> ()
      | true :: q -> 
	  v.(i) <- j; parse_ids (i+1) (j+1) q
      | false :: q -> parse_ids (i+1) j q
    in parse_ids 1 1 bl ; 
    select_via_bl bl ids, gen_subst v (n'-n) c
  end

(*s [kill_dummy_lams] uses the last function to kill the lambdas corresponding 
  to a [dummy_name]. It can raise [Impossible] if there is nothing to do, or 
  if there is no lambda left at all. *)

let kill_dummy_lams c = 
  let ids,c = collect_lams c in 
  let bl = List.map ((<>) dummy_name) ids in 
  if (List.mem true bl) && (List.mem false bl) then 
    let ids',c = kill_some_lams bl (ids,c) in 
    ids, named_lams ids' c
  else raise Impossible
      
(*s [kill_dummy_args ids t0 t] looks for occurences of [t0] in [t] and 
  purge the args of [t0] corresponding to a [dummy_name]. 
  It makes eta-expansion if needed. *) 

let kill_dummy_args ids t0 t =
  let m = List.length ids in 
  let bl = List.rev_map ((<>) dummy_name) ids in
  let rec killrec n = function 
    | MLapp(e, a) when e = ml_lift n t0 -> 
	let k = max 0 (m - (List.length a)) in 
	let a = List.map (killrec n) a in  
	let a = List.map (ml_lift k) a in 
	let a = select_via_bl bl (a @ (eta_args k)) in 
	named_lams (list_firstn k ids) (MLapp (ml_lift k e, a)) 
    | e when e = ml_lift n t0 -> 
	let a = select_via_bl bl (eta_args m) in 
	named_lams ids (MLapp (ml_lift m e, a))
    | e -> ast_map_lift killrec n e 
  in killrec 0 t 

(*s The main function for local [dummy] elimination. *)

let rec kill_dummy = function 
  | MLfix(i,fi,c) -> 
      (try 
	 let ids,c = kill_dummy_fix i fi c in 
	 ml_subst (MLfix (i,fi,c)) (kill_dummy_args ids (MLrel 1) (MLrel 1))
       with Impossible -> MLfix (i,fi,Array.map kill_dummy c))
  | MLapp (MLfix (i,fi,c),a) -> 
      (try 
	 let ids,c = kill_dummy_fix i fi c in 
	 let a = List.map (fun t -> ml_lift 1 (kill_dummy t)) a in 
	 let e = kill_dummy_args ids (MLrel 1) (MLapp (MLrel 1,a)) in
	 ml_subst (MLfix (i,fi,c)) e  
       with Impossible -> 
	 MLapp(MLfix(i,fi,Array.map kill_dummy c),List.map kill_dummy a))
  | MLletin(id, MLfix (i,fi,c),e) -> 
      (try 
	 let ids,c = kill_dummy_fix i fi c in
	 let e = kill_dummy (kill_dummy_args ids (MLrel 1) e) in 
	 MLletin(id, MLfix(i,fi,c),e)
      with Impossible -> 
	MLletin(id, MLfix(i,fi,Array.map kill_dummy c),kill_dummy e))
  | MLletin(id,c,e) -> 
      (try 
	 let ids,c = kill_dummy_lams c in 
	 let e = kill_dummy_args ids (MLrel 1) e in 
	 MLletin (id, kill_dummy c,kill_dummy e) 
       with Impossible -> MLletin(id,kill_dummy c,kill_dummy e))
  | a -> ast_map kill_dummy a

and kill_dummy_fix i fi c = 
  let n = Array.length fi in 
  let ids,ci = kill_dummy_lams c.(i) in 
  let c = Array.copy c in c.(i) <- ci; 
  for j = 0 to (n-1) do 
    c.(j) <- kill_dummy (kill_dummy_args ids (MLrel (n-i)) c.(j)) 
  done;
  ids,c

(*s Putting things together. *)

let normalize a = 
  if (optim()) then kill_dummy (simpl true a) else simpl false a

(*S Special treatment of fixpoint for pretty-printing purpose. *)

let general_optimize_fix f ids n args m c = 
  let v = Array.make n 0 in 
  for i=0 to (n-1) do v.(i)<-i done;
  let aux i = function 
    | MLrel j when v.(j-1)>=0 -> v.(j-1)<-(-i-1)
    | _ -> raise Impossible
  in list_iter_i aux args; 
  let args_f = List.rev_map (fun i -> MLrel (i+m+1)) (Array.to_list v) in
  let new_f = anonym_lams (MLapp (MLrel (n+m+1),args_f)) m in  
  let new_c = named_lams ids (normalize (MLapp ((ml_subst new_f c),args))) in
  MLfix(0,[|f|],[|new_c|])

let optimize_fix a = 
  if not (optim()) then a 
  else
    let ids,a' = collect_lams a in 
    let n = List.length ids in 
    if n = 0 then a 
    else match a' with 
      | MLfix(_,[|f|],[|c|]) ->
	  let new_f = MLapp (MLrel (n+1),eta_args n) in 
	  let new_c = named_lams ids (normalize (ml_subst new_f c))
	  in MLfix(0,[|f|],[|new_c|])
      | MLapp(a',args) ->
	  let m = List.length args in 
	  (match a' with 
	     | MLfix(_,_,_) when 
		 (test_eta_args_lift 0 n args) && not (occurs_itvl 1 m a') 
		 -> a'
	     | MLfix(_,[|f|],[|c|]) -> 
		 (try general_optimize_fix f ids n args m c
		  with Impossible -> 
		    named_lams ids (MLapp (MLfix (0,[|f|],[|c|]),args))) 
	     | _ -> a)
      | _ -> a

(*S Inlining. *)

(* Utility functions used in the decision of inlining. *)

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
	(* In [(x y)] we say that only x is strict. Cf [sig_rec]. We may *)
	(* gain something if x is replaced by a function like a projection *)
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
      (* The only interesting case: for a variable to be non-strict, *)
      (* it is sufficient that it appears non-strict in at least one branch, *)
      (* so he make an union (in fact a merge). *)
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
  try let _ = non_stricts true [] t in false
  with Toplevel -> true

(*s Inlining decision *)

(* [inline_test] answers the following question: 
   If we could inline [t] (the user said nothing special), 
   should we inline ? 
   
   We don't expand fixpoints, but always inductive constructors
   and small terms.
   Last case of inlining is a term with at least one non-strict 
   variable (i.e. a variable that may not be evaluated). *)

let inline_test t = 
  not (is_fix t) 
  && (is_constr t || ml_size t < 3 || (ml_size t < 12 && is_not_strict t))

let manual_inline_list = 
  List.map (fun s -> path_of_string ("Coq.Init."^s))
    [ "Specif.sigS_rect" ; "Specif.sigS_rec" ; 
      "Logic.and_rect"; "Logic.and_rec";
      "Datatypes.prod_rect" ; "Datatypes.prod_rec"; 
      "Wf.Acc_rec" ; "Wf.Acc_rect" ; 
      "Wf.well_founded_induction" ; "Wf.well_founded_induction_type" ]

let manual_inline = function 
  | ConstRef sp -> List.mem sp manual_inline_list
  | _ -> false 

(* If the user doesn't say he wants to keep [t], we inline in two cases:
   \begin{itemize}
   \item the user explicitly requests it 
   \item [expansion_test] answers that the inlining is a good idea, and 
   we are free to act (AutoInline is set)
   \end{itemize} *)

let inline r t = 
  not (to_keep r) (* The user DOES want to keep it *)
  && (to_inline r (* The user DOES want to inline it *) 
     || (auto_inline () && lang () <> Haskell 
	 && (manual_inline r || inline_test t)))

(*S Optimization. *)

let subst_glob_ast r m = 
  let rec substrec = function
    | MLglob r' as t -> if r = r' then m else t
    | t -> ast_map substrec t
  in substrec

let subst_glob_decl r m = function
  | Dglob(r',t') -> Dglob(r', subst_glob_ast r m t')
  | d -> d

let inline_glob r t l = 
  if not (inline r t) then true, l 
  else false, List.map (subst_glob_decl r t) l

let print_ml_decl prm (r,_) = 
  not (to_inline r) || List.mem r prm.to_appear

let add_ml_decls prm decls = 
  let l = sorted_ml_extractions () in 
  let l = List.filter (print_ml_decl prm) l in 
  let l = List.map (fun (r,s)-> Dcustom (r,s)) l in 
  (List.rev l @ decls)

let rec expunge_fix_decls prm v c b = function 
  | [] -> b, [] 
  | Dglob (r, t) :: l when array_exists ((=) r) v -> 
      let t = normalize t in 
      let t' = optimize_fix t in 
      (match t' with 
	 | MLfix(_,_,c') when c=c' -> 
	     let b',l = inline_glob r t l in 
	     expunge_fix_decls prm v c (b || b' || List.mem r prm.to_appear) l 
	 | _ -> raise Impossible)
  | d::l -> let b,l = expunge_fix_decls prm v c b l in b, d::l  

let rec optimize prm = function
  | [] -> 
      []
  | (Dabbrev (r,_,Tdummy) | Dglob(r,MLdummy)) as d :: l ->
      if List.mem r prm.to_appear then d :: (optimize prm l) 
      else optimize prm l
  | Dglob (r,t) :: l ->
      let t = normalize t in
      let b,l = inline_glob r t l in 
      let t' = optimize_fix t in
      (try optimize_Dfix prm r t' b l 
      with Impossible -> 
	if (b || prm.modular || List.mem r prm.to_appear) then 
	  Dglob (r,t') :: (optimize prm l)
	else optimize prm l)
  | d :: l -> d :: (optimize prm l)

and optimize_Dfix prm r t b l = 
  match t with 
    | MLfix (_, f, c) -> 
	if Array.length f = 1 then 
	  if b then 
	    Dfix ([|r|], c) :: (optimize prm l)
	  else optimize prm l
	else 
	  let v = try 
	    let d = dirpath (sp_of_r r) in 
	    Array.map (fun id -> locate (make_qualid d id)) f 
	  with Not_found -> raise Impossible 
	  in 
	  let b,l = expunge_fix_decls prm v c (prm.modular || b) l in 
	  if b then Dfix (v, c) :: (optimize prm l)
	  else optimize prm l 
    | _ -> raise Impossible





