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
open Util
open Names
open Libnames
open Nametab
open Table
open Miniml
(*i*)

(*s Exceptions. *)

exception Found
exception Impossible

(*S Names operations. *)

let anonymous = id_of_string "x"
let dummy_name = id_of_string "_"

let id_of_name = function
  | Anonymous -> anonymous
  | Name id when id = dummy_name -> anonymous
  | Name id -> id 

(*S Operations upon ML types (with meta). *)

let meta_count = ref 0 
		     
let reset_meta_count () = meta_count := 0
			      
let new_meta _ = 
  incr meta_count; 
  Tmeta {id = !meta_count; contents = None}

(*s Sustitution of [Tvar i] by [t] in a ML type. *)

let type_subst i t0 t = 
  let rec subst t = match t with
    | Tvar j when i = j -> t0
    | Tmeta {contents=None} -> t 
    | Tmeta {contents=Some u} -> subst u
    | Tarr (a,b) -> Tarr (subst a, subst b)
    | Tglob (r, l) -> Tglob (r, List.map subst l)
    | a -> a 
  in subst t
       
(* Simultaneous substitution of [[Tvar 1; ... ; Tvar n]] by [l] in a ML type. *)

let type_subst_list l t = 
  let rec subst t = match t with 
    | Tvar j -> List.nth l (j-1)
    | Tmeta {contents=None} -> t
    | Tmeta {contents=Some u} -> subst u
    | Tarr (a,b) -> Tarr (subst a, subst b)
    | Tglob (r, l) -> Tglob (r, List.map subst l)
    | a -> a
  in subst t

(* Simultaneous substitution of [[|Tvar 1; ... ; Tvar n|]] by [v] in a ML type. *)

let type_subst_vect v t = 
  let rec subst t = match t with 
    | Tvar j -> v.(j-1)
    | Tmeta {contents=None} -> t
    | Tmeta {contents=Some u} -> subst u
    | Tarr (a,b) -> Tarr (subst a, subst b)
    | Tglob (r, l) -> Tglob (r, List.map subst l)
    | a -> a
  in subst t

(*s From a type schema to a type. All [Tvar] become fresh [Tmeta]. *)

let instantiation (nb,t) = type_subst_vect (Array.init nb new_meta) t

(*s Occur-check of a free meta in a type *)

let rec type_occurs alpha t =
  match t with
  | Tmeta {id=beta; contents=None} -> alpha = beta
  | Tmeta {contents=Some u} -> type_occurs alpha u
  | Tarr (t1, t2) -> type_occurs alpha t1 || type_occurs alpha t2
  | Tglob (r,l) -> List.exists (type_occurs alpha) l  
  | _ -> false

(*s Most General Unificator *)

let rec mgu = function
  | Tmeta m, Tmeta m' when m.id = m'.id -> ()
  | Tmeta m, t when m.contents=None -> 
      if type_occurs m.id t then raise Impossible
      else m.contents <- Some t
  | t, Tmeta m when m.contents=None -> 
      if type_occurs m.id t then raise Impossible
      else m.contents <- Some t
  | Tmeta {contents=Some u}, t -> mgu (u, t)
  | t, Tmeta {contents=Some u} -> mgu (t, u)
  | Tarr(a, b), Tarr(a', b') ->
      mgu (a, a'); mgu (b, b')
  | Tglob (r,l), Tglob (r',l') when r = r' ->
       List.iter mgu (List.combine l l')
  | Tvar i, Tvar j when i = j -> ()
  | Tvar' i, Tvar' j when i = j -> ()
  | Tdummy, Tdummy -> ()
  | Tunknown, Tunknown -> ()
  | _ -> raise Impossible

let needs_magic p = try mgu p; false with Impossible -> true

let put_magic_if b a = if b then MLmagic a else a

let put_magic p a = if needs_magic p then MLmagic a else a


(*S ML type env. *)

module Mlenv = struct 
  
  let meta_cmp m m' = compare m.id m'.id 
  module Metaset = Set.Make(struct type t = ml_meta let compare = meta_cmp end)

  (* Main MLenv type. [env] is the real environment, whereas [free] 
     (tries to) record the free meta variables occurring in [env]. *)

  type t = { env : ml_schema list; mutable free : Metaset.t}

  (* Empty environment. *)

  let empty = { env = []; free = Metaset.empty }

  (* [get] returns a instantiated copy of the n-th most recently added 
     type in the environment. *)

  let get mle n = 
    assert (List.length mle.env >= n); 
    instantiation (List.nth mle.env (n-1))

  (* [find_free] finds the free meta in a type. *) 

  let rec find_free set = function 
    | Tmeta m when m.contents = None -> Metaset.add m set
    | Tmeta {contents = Some t} -> find_free set t
    | Tarr (a,b) -> find_free (find_free set a) b
    | Tglob (_,l) -> List.fold_left find_free set l
    | _ -> set

  (* The [free] set of an environment can be outdate after 
     some unifications. [clean_free] takes care of that. *) 
			
  let clean_free mle = 
    let rem = ref Metaset.empty 
    and add = ref Metaset.empty in 
    let clean m = match m.contents with 
      | None -> () 
      | Some u -> rem := Metaset.add m !rem; add := find_free !add u
    in 
    Metaset.iter clean mle.free; 
    mle.free <- Metaset.union (Metaset.diff mle.free !rem) !add

  (* From a type to a type schema. If a [Tmeta] is still uninstantiated
     and does appears in the [mle], then it becomes a [Tvar]. *)

  let generalization mle t = 
    let c = ref 0 in 
    let map = ref (Intmap.empty : int Intmap.t) in 
    let add_new i = incr c; map := Intmap.add i !c !map; !c in 
    let rec meta2var t = match t with 
      | Tmeta {contents=Some u} -> meta2var u 
      | Tmeta ({id=i} as m) -> 
	  (try Tvar (Intmap.find i !map) 
	   with Not_found ->  
	     if Metaset.mem m mle.free then t 
	     else Tvar (add_new i))
      | Tarr (t1,t2) -> Tarr (meta2var t1, meta2var t2)
      | Tglob (r,l) -> Tglob (r, List.map meta2var l) 
      | t -> t 
    in !c, meta2var t
	
  (* Adding a type in an environment, after generalizing. *)

  let push_gen mle t = 
    clean_free mle; 
    { env = generalization mle t :: mle.env; free = mle.free }

  (* Adding a type with no [Tvar], hence no generalization needed. *)

  let push_type {env=e;free=f} t = 
    { env = (0,t) :: e; free = find_free f t} 
    
  (* Adding a type with no [Tvar] nor [Tmeta]. *)

  let push_std_type {env=e;free=f} t = 
    { env = (0,t) :: e; free = f}

end

(*S Operations upon ML types (without meta). *)

(*s Does a section path occur in a ML type ? *)

let kn_of_r r = match r with 
    | ConstRef kn -> kn
    | IndRef (kn,_) -> kn
    | ConstructRef ((kn,_),_) -> kn
    | VarRef _ -> assert false

let rec type_mem_kn kn = function 
  | Tmeta _ -> assert false
  | Tglob (r,l) -> (kn_of_r r) = kn || List.exists (type_mem_kn kn) l
  | Tarr (a,b) -> (type_mem_kn kn a) || (type_mem_kn kn b)
  | _ -> false

(*s Greatest variable occurring in [t]. *)

let type_maxvar t = 
  let rec parse n = function 
    | Tmeta _ -> assert false
    | Tvar i -> max i n 
    | Tarr (a,b) -> parse (parse n a) b
    | Tglob (_,l) -> List.fold_left parse n l 
    | _ -> n 
  in parse 0 t

(*s From [a -> b -> c] to [[a;b],c]. *) 

let rec type_decomp = function 
  | Tmeta _ -> assert false
  | Tarr (a,b) -> let l,h = type_decomp b in a::l, h 
  | a -> [],a

(*s The converse: From [[a;b],c] to [a -> b -> c]. *)

let rec type_recomp (l,t) = match l with 
  | [] -> t 
  | a::l -> Tarr (a, type_recomp (l,t))

(*s Translating [Tvar] to [Tvar'] to avoid clash. *)

let rec var2var' = function 
  | Tmeta _ -> assert false
  | Tvar i -> Tvar' i
  | Tarr (a,b) -> Tarr (var2var' a, var2var' b)
  | Tglob (r,l) -> Tglob (r, List.map var2var' l)
  | a -> a

type abbrev_map = global_reference -> ml_type option

(*s Delta-reduction of type constants everywhere in a ML type [t].
   [env] is a function of type [ml_type_env]. *)

let type_expand env t = 
  let rec expand = function
    | Tmeta _ -> assert false
    | Tglob (r,l) as t ->    
	(match env r with 
	   | Some mlt -> expand (type_subst_list l mlt) 
	   | None -> Tglob (r, List.map expand l))
    | Tarr (a,b) -> Tarr (expand a, expand b)
    | a -> a
  in expand t

(*s Idem, but only at the top level of implications. *)

let is_arrow = function Tarr _ -> true | _ -> false

let type_weak_expand env t = 
  let rec expand = function
    | Tmeta _ -> assert false
    | Tglob (r,l) as t ->    
	(match env r with 
	   | Some mlt -> 
	       let u = expand (type_subst_list l mlt) in 
	       if is_arrow u then u else t
	   | None -> t)
    | Tarr (a,b) -> Tarr (a, expand b)
    | a -> a
  in expand t

(*s Equality over ML types modulo delta-reduction *)

let type_eq env t t' = (type_expand env t = type_expand env t')

let type_neq env t t' = (type_expand env t <> type_expand env t')

(*s Generating a signature from a ML type. *)

let type_to_sign env t = 
  let rec f = function 
    | Tmeta _ -> assert false
    | Tarr (a,b) -> (Tdummy <> a) :: (f b)
    | _ -> [] 
  in f (type_expand env t)

(*s Removing [Tdummy] from the top level of a ML type. *)

let type_expunge env t = 
  let s = type_to_sign env t in 
  if s = [] then t 
  else if List.mem true s then 
    let rec f t s = 
      if List.mem false s then 
	match t with 
	  | Tmeta _ -> assert false
	  | Tarr (a,b) -> 
	      let t = f b (List.tl s) in 
	      if List.hd s then Tarr (a, t) else t  
	  | Tglob (r,l) ->
	      (match env r with 
		 | Some mlt -> f (type_subst_list l mlt) s
		 | None -> assert false)
	  | _ -> assert false
      else t 
    in f t s 
  else Tarr (Tdummy, snd (type_decomp (type_weak_expand env t))) 

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

(*s [ast_occurs k t] returns [true] if [(Rel k)] occurs in [t]. *)

let ast_occurs k t = 
  try 
    ast_iter_rel (fun i -> if i = k then raise Found) t; false 
  with Found -> true

(*s [occurs_itvl k k' t] returns [true] if there is a [(Rel i)] 
   in [t] with [k<=i<=k'] *)

let ast_occurs_itvl k k' t = 
  try 
    ast_iter_rel (fun i -> if (k <= i) && (i <= k') then raise Found) t; false 
  with Found -> true

(*s Number of occurences of [Rel k] and [Rel 1] in [t]. *)

let nb_occur_k k t =
  let cpt = ref 0 in 
  ast_iter_rel (fun i -> if i = k then incr cpt) t;
  !cpt

let nb_occur t = nb_occur_k 1 t

(* Number of occurences of [Rel 1] in [t], with special treatment of match:
   occurences in different branches aren't added, but we rather use max. *)

let nb_occur_match = 
  let rec nb k = function 
    | MLrel i -> if i = k then 1 else 0
    | MLcase(a,v) -> 
        Array.fold_left 
          (fun r (_,ids,a) -> max r (nb (k+(List.length ids)) a)) (nb k a) v
    | MLletin (_,a,b) -> (nb k a) + (nb (k+1) a) 
    | MLfix (_,ids,v) -> let k = k+(Array.length ids) in 
      Array.fold_left (fun r a -> r+(nb k a)) 0 v
    | MLlam (_,a) -> nb (k+1) a
    | MLapp (a,l) -> List.fold_left (fun r a -> r+(nb k a)) (nb k a) l
    | MLcons (_,l) -> List.fold_left (fun r a -> r+(nb k a)) 0 l 
    | MLcast (a,_) -> nb k a
    | MLmagic a -> nb k a
    | MLglob _ | MLexn _ | MLdummy -> 0
  in nb 1

(*s Lifting on terms.
    [ast_lift k t] lifts the binding depth of [t] across [k] bindings. *)

let ast_lift k t = 
  let rec liftrec n = function
    | MLrel i as a -> if i-n < 1 then a else MLrel (i+k)
    | a -> ast_map_lift liftrec n a
  in if k = 0 then t else liftrec 0 t

let ast_pop t = ast_lift (-1) t

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

let ast_subst e =
  let rec subst n = function
    | MLrel i as a ->
	let i' = i-n in 
	if i'=1 then ast_lift n e
	else if i'<1 then a 
	else MLrel (i-1)
    | a -> ast_map_lift subst n a
  in subst 0

(*s Generalized substitution. 
   [gen_subst v d t] applies to [t] the substitution coded in the 
   [v] array: [(Rel i)] becomes [v.(i-1)]. [d] is the correction applies 
   to [Rel] greater than [Array.length v]. *)

let gen_subst v d t = 
  let rec subst n = function
    | MLrel i as a -> 
	let i'= i-n in 
	if i' < 1 then a 
	else if i' <= Array.length v then 
	  ast_lift n v.(i'-1) 
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
  | n -> dummy_lams (MLlam (dummy_name,a)) (pred n)

(*s mixed according to a signature. *)

let rec anonym_or_dummy_lams a = function 
  | [] -> a 
  | true :: s -> MLlam(anonymous, anonym_or_dummy_lams a s)
  | false :: s -> MLlam(dummy_name, anonym_or_dummy_lams a s)

(*S Operations concerning eta. *)

(*s The following function creates [MLrel n;...;MLrel 1] *)

let rec eta_args n = 
  if n = 0 then [] else (MLrel n)::(eta_args (pred n))

(*s Same, but filtered by a signature. *)

let rec eta_args_sign n = function 
  | [] -> [] 
  | true :: s -> (MLrel n) :: (eta_args_sign (n-1) s) 
  | false :: s -> eta_args_sign (n-1) s

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
	  if test_eta_args_lift 0 n a2 && not (ast_occurs_itvl 1 n f)
	  then ast_lift (-n) f
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
  if ast_occurs_itvl 1 n t then raise Impossible; 
  let cst = ast_lift (-n) t in 
  for i = 1 to Array.length br - 1 do 
    let (r,l,t) = br.(i) in
    let n = List.length l in
    if (ast_occurs_itvl 1 n t) || (cst <> (ast_lift (-n) t)) 
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
	let c = ast_lift k c in 
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
      (id = dummy_name) || (is_atomic c) || (nb_occur_match e <= 1) -> 
	simpl o (ast_subst c e)
  | MLfix(i,ids,c) as t when o -> 
      let n = Array.length ids in 
      if ast_occurs_itvl 1 n c.(i) then 
	MLfix (i, ids, Array.map (simpl o) c)
      else simpl o (ast_lift (-n) c.(i)) (* Dummy fixpoint *)
  | a -> ast_map (simpl o) a 

and simpl_app o a = function  
  | MLapp (f',a') -> simpl_app o (a'@a) f'
  | MLlam (id,t) when id = dummy_name -> 
      simpl o (MLapp (ast_pop t, List.tl a))
  | MLlam (id,t) -> (* Beta redex *)
      (match nb_occur_match t with
	 | 0 -> simpl o (MLapp (ast_pop t, List.tl a))
	 | 1 when o -> 
	     simpl o (MLapp (ast_subst (List.hd a) t, List.tl a))
	 | _ -> 
	     let a' = List.map (ast_lift 1) (List.tl a) in
	     simpl o (MLletin (id, List.hd a, MLapp (t, a'))))
  | MLletin (id,e1,e2) -> 
      (* Application of a letin: we push arguments inside *)
      MLletin (id, e1, simpl o (MLapp (e2, List.map (ast_lift 1) a)))
  | MLcase (e,br) -> (* Application of a case: we push arguments inside *)
      let br' = 
	Array.map 
      	  (fun (n,l,t) -> 
	     let k = List.length l in
	     let a' = List.map (ast_lift k) a in
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
	  else named_lams ids (MLcase (ast_lift n e, br))

let rec post_simpl = function 
  | MLletin(_,c,e) when (is_atomic (eta_red c)) -> 
      post_simpl (ast_subst (eta_red c) e)
  | a -> ast_map post_simpl a 

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
  else if n' = 0 then [],ast_lift (-n) c 
  else begin
    let v = Array.make n MLdummy in 
    let rec parse_ids i j = function 
      | [] -> ()
      | true :: l -> v.(i) <- MLrel j; parse_ids (i+1) (j+1) l
      | false :: l -> parse_ids (i+1) j l
    in parse_ids 0 1 bl ; 
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

(*s [eta_expansion_sign] takes a function [fun idn ... id1 -> c] 
   and a signature [s] and builds a eta-long version. *)

(* For example, if [s = [true;true;false;true]] then the output is :
   [fun idn ... id1 x x _ x -> (c' 4 3 __ 1)]  with [c' = lift 4 c] *)

let eta_expansion_sign s (ids,c) =
  let rec abs ids rels i = function
    | [] -> 
	let a = List.rev_map (function MLrel x -> MLrel (i-x) | a -> a) rels
	in ids, MLapp (ast_lift (i-1) c, a) 
    | true :: l -> abs (anonymous :: ids) (MLrel i :: rels) (i+1) l 
    | false :: l -> abs (dummy_name :: ids) (MLdummy :: rels) (i+1) l
  in abs ids [] 1 s

(*s If [s = [b1; ... ; bn]] then [case_expunge] decomposes [e] 
  in [n] lambdas (with eta-expansion if needed) and removes all dummy lambdas 
  corresponding to [false] in [s]. *)

let case_expunge s e = 
  let m = List.length s in 
  let n = nb_lams e in 
  let p = if m <= n then collect_n_lams m e 
  else eta_expansion_sign (snd (list_chop n s)) (collect_lams e) in 
  kill_some_lams (List.rev s) p

(*s [term_expunge] takes a function [fun idn ... id1 -> c] 
  and a signature [s] and remove dummy lams. The difference 
  with [case_expunge] is that we here leave one dummy lambda 
  if all lambdas are dummy. *)

let term_expunge s (ids,c) =
  if s = [] then c 
  else 
    let ids,c = kill_some_lams (List.rev s) (ids,c) in 
    if ids = [] then MLlam (dummy_name, ast_lift 1 c)
    else named_lams ids c

(*s [kill_dummy_args ids t0 t] looks for occurences of [t0] in [t] and 
  purge the args of [t0] corresponding to a [dummy_name]. 
  It makes eta-expansion if needed. *) 

let kill_dummy_args ids t0 t =
  let m = List.length ids in 
  let bl = List.rev_map ((<>) dummy_name) ids in
  let rec killrec n = function 
    | MLapp(e, a) when e = ast_lift n t0 -> 
	let k = max 0 (m - (List.length a)) in 
	let a = List.map (killrec n) a in  
	let a = List.map (ast_lift k) a in 
	let a = select_via_bl bl (a @ (eta_args k)) in 
	named_lams (list_firstn k ids) (MLapp (ast_lift k e, a)) 
    | e when e = ast_lift n t0 -> 
	let a = select_via_bl bl (eta_args m) in 
	named_lams ids (MLapp (ast_lift m e, a))
    | e -> ast_map_lift killrec n e 
  in killrec 0 t 

(*s The main function for local [dummy] elimination. *)

let rec kill_dummy = function 
  | MLfix(i,fi,c) -> 
      (try 
	 let ids,c = kill_dummy_fix i fi c in 
	 ast_subst (MLfix (i,fi,c)) (kill_dummy_args ids (MLrel 1) (MLrel 1))
       with Impossible -> MLfix (i,fi,Array.map kill_dummy c))
  | MLapp (MLfix (i,fi,c),a) -> 
      (try 
	 let ids,c = kill_dummy_fix i fi c in 
	 let a = List.map (fun t -> ast_lift 1 (kill_dummy t)) a in 
	 let e = kill_dummy_args ids (MLrel 1) (MLapp (MLrel 1,a)) in
	 ast_subst (MLfix (i,fi,c)) e  
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
  if optim () then post_simpl (kill_dummy (simpl true a)) else simpl false a

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
  let new_c = named_lams ids (normalize (MLapp ((ast_subst new_f c),args))) in
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
	  let new_c = named_lams ids (normalize (ast_subst new_f c))
	  in MLfix(0,[|f|],[|new_c|])
      | MLapp(a',args) ->
	  let m = List.length args in 
	  (match a' with 
	     | MLfix(_,_,_) when 
		 (test_eta_args_lift 0 n args) && not (ast_occurs_itvl 1 m a') 
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
      (* so we make an union (in fact a merge). *)
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
   
   We expand small terms with at least one non-strict 
   variable (i.e. a variable that may not be evaluated).
   
   Futhermore we don't expand fixpoints. *)

let inline_test t = 
  not (is_fix t) && (ml_size t < 12 && is_not_strict t)

let manual_inline_list = 
  let mp = MPfile (dirpath_of_string "Coq.Init.Wf") in 
  List.map (fun s -> (make_kn mp empty_dirpath (mk_label s)))
    [ "well_founded_induction_type"; "well_founded_induction"; 
      "Acc_rect"; "Acc_rec" ]

let manual_inline = function 
  | ConstRef c -> List.mem c manual_inline_list
  | _ -> false 

(* If the user doesn't say he wants to keep [t], we inline in two cases:
   \begin{itemize}
   \item the user explicitly requests it 
   \item [expansion_test] answers that the inlining is a good idea, and 
   we are free to act (AutoInline is set)
   \end{itemize} *)

let inline r t = 
  not (to_keep r) (* The user DOES want to keep it *)
  && not (is_inline_custom r) 
  && (to_inline r (* The user DOES want to inline it *) 
     || (auto_inline () && lang () <> Haskell && not (is_projection r)
         && (is_recursor r || manual_inline r || inline_test t)))

(*S Optimization. *)

let rec subst_glob_ast s t = match t with 
  | MLglob (ConstRef kn) -> (try KNmap.find (long_kn kn) !s with Not_found -> t)
  | _ -> ast_map (subst_glob_ast s) t

let rec optim prm s = function
  | [] -> []
  | (Dtype (r,_,Tdummy) | Dterm(r,MLdummy,_)) as d :: l ->
      if List.mem r prm.to_appear then d :: (optim prm s l) else optim prm s l
  | Dterm (r,t,typ) :: l ->
      let t = normalize (subst_glob_ast s t) in 
      let i = inline r t in 
      if i then s := KNmap.add (long_kn (kn_of_r r)) t !s; 
      if not i || prm.modular || List.mem r prm.to_appear 
      then 
	let d = match optimize_fix t with 
	  | MLfix (0, _, [|c|]) -> 
	      Dfix ([|r|], [|ast_subst (MLglob r) c|], [|typ|])
	  | t -> Dterm (r, t, typ)
	in d :: (optim prm s l)
      else optim prm s l
  | d :: l -> d :: (optim prm s l)

let rec optim_se top prm s = function 
  | [] -> [] 
  | (l,SEdecl (Dterm (r,a,t))) :: lse -> 
      let r = long_r r in 
      let kn = kn_of_r r in 
      let a = normalize (subst_glob_ast s a) in 
      let i = inline r a in 
      if i then s := KNmap.add kn a !s; 
      if top && i && not prm.modular && not (List.mem r prm.to_appear)
      then optim_se top prm s lse
      else 
	let d = match optimize_fix a with 
	  | MLfix (0, _, [|c|]) -> 
	      Dfix ([|r|], [|ast_subst (MLglob r) c|], [|t|])
	  | a -> Dterm (r, a, t)
	in (l,SEdecl d) :: (optim_se top prm s lse)
  | (l,SEdecl (Dfix (rv,av,tv))) :: lse -> 
      let av = Array.map (fun a -> normalize (subst_glob_ast s a)) av in 
      (l,SEdecl (Dfix (rv, av, tv))) :: (optim_se top prm s lse)
  | (l,SEmodule m) :: lse -> 
      let m = { m with ml_mod_expr = option_app (optim_me prm s) m.ml_mod_expr}
      in (l,SEmodule m) :: (optim_se top prm s lse)
  | se :: lse -> se :: (optim_se top prm s lse) 

and optim_me prm s = function 
  | MEstruct (msid, lse) -> MEstruct (msid, optim_se false prm s lse)
  | MEident mp as me -> me
  | MEapply (me, me') -> MEapply (optim_me prm s me, optim_me prm s me')
  | MEfunctor (mbid,mt,me) -> MEfunctor (mbid,mt, optim_me prm s me)

let optimize_struct prm before struc = 
  let subst = ref (KNmap.empty : ml_ast KNmap.t) in 
  option_iter (fun l -> ignore (optim prm subst l)) before; 
  List.map (fun (mp,lse) -> (mp, optim_se true prm subst lse)) struc

(*s Apply some functions upon all [ml_decl] and [ml_spec] found in a 
   [ml_structure]. *) 

let struct_iter do_decl do_spec s = 
  let rec se_iter = function 
    | (_,SEdecl d) -> do_decl d
    | (_,SEmodule m) -> 
	option_iter me_iter m.ml_mod_expr; mt_iter m.ml_mod_type
    | (_,SEmodtype m) -> mt_iter m
  and me_iter = function 
    | MEident _ -> () 
    | MEfunctor (_,mt,me) -> me_iter me; mt_iter mt
    | MEapply (me,me') -> me_iter me; me_iter me'
    | MEstruct (msid, sel) -> List.iter se_iter sel
  and mt_iter = function 
    | MTident _ -> () 
    | MTfunsig (_,mt,mt') -> mt_iter mt; mt_iter mt'
    | MTsig (_, sign) -> List.iter spec_iter sign
  and spec_iter = function 
    | (_,Spec s) -> do_spec s
    | (_,Smodule mt) -> mt_iter mt
    | (_,Smodtype mt) -> mt_iter mt
  in 
  List.iter (function (_,sel) -> List.iter se_iter sel) s

(*s Apply some fonctions upon all references in [ml_type], [ml_ast], 
  [ml_decl], [ml_spec] and [ml_structure]. *)

type do_ref = global_reference -> unit

let type_iter_references do_type t = 
  let rec iter = function 
    | Tglob (r,l) -> do_type r; List.iter iter l 
    | Tarr (a,b) -> iter a; iter b 
    | _ -> () 
  in iter t

let ast_iter_references do_term do_cons do_type a = 
  let rec iter a = 
    ast_iter iter a;
    match a with 
      | MLglob r -> do_term r
      | MLcons (r,_) -> do_cons r
      | MLcase (_,v) as a -> Array.iter (fun (r,_,_) -> do_cons r) v
      | MLcast (_,t) -> type_iter_references do_type t 
      | _ -> ()
  in iter a

let ind_iter_references do_term do_cons do_type kn ind = 
  let type_iter = type_iter_references do_type in
  let cons_iter cp l = do_cons (ConstructRef cp); List.iter type_iter l in 
  let packet_iter ip p = 
    do_type (IndRef ip); Array.iteri (fun j -> cons_iter (ip,j+1)) p.ip_types 
  in
  if ind.ind_info = Record then List.iter do_term (find_projections kn); 
  Array.iteri (fun i -> packet_iter (kn,i)) ind.ind_packets
  
let decl_iter_references do_term do_cons do_type = 
  let type_iter = type_iter_references do_type 
  and ast_iter = ast_iter_references do_term do_cons do_type in
  function 
    | Dind (kn,ind) -> ind_iter_references do_term do_cons do_type kn ind 
    | Dtype (r,_,t) -> do_type r; type_iter t 
    | Dterm (r,a,t) -> do_term r; ast_iter a; type_iter t
    | Dfix(rv,c,t) -> 	
	Array.iter do_term rv; Array.iter ast_iter c; Array.iter type_iter t

let spec_iter_references do_term do_cons do_type = function 
  | Sind (kn,ind) -> ind_iter_references do_term do_cons do_type kn ind
  | Stype (r,_,ot) -> do_type r; option_iter (type_iter_references do_type) ot
  | Sval (r,t) -> do_term r; type_iter_references do_type t

let struct_iter_references do_term do_cons do_type = 
  struct_iter 
    (decl_iter_references do_term do_cons do_type) 
    (spec_iter_references do_term do_cons do_type) 

(*S Searching occurrences of a particular term (no lifting done). *)

let rec ast_search t a = 
  if t = a then raise Found else ast_iter (ast_search t) a

let decl_ast_search t = function 
  | Dterm (_,a,_) -> ast_search t a
  | Dfix (_,c,_) -> Array.iter (ast_search t) c
  | _ -> () 

let struct_ast_search t s = 
  try struct_iter (decl_ast_search t) (fun _ -> ()) s; false
  with Found -> true

let rec type_search t = function  
  | Tarr (a,b) -> type_search t a; type_search t b 
  | Tglob (r,l) -> List.iter (type_search t) l
  | u -> if t = u then raise Found

let decl_type_search t = function 
  | Dind (_,{ind_packets=p})  -> 
      Array.iter 
	(fun {ip_types=v} -> Array.iter (List.iter (type_search t)) v) p
  | Dterm (_,_,u) -> type_search t u
  | Dfix (_,_,v) -> Array.iter (type_search t) v
  | Dtype (_,_,u) -> type_search t u

let spec_type_search t = function 
  | Sind (_,{ind_packets=p}) -> 
      Array.iter 
	(fun {ip_types=v} -> Array.iter (List.iter (type_search t)) v) p
  | Stype (_,_,ot) -> option_iter (type_search t) ot
  | Sval (_,u) -> type_search t u

let struct_type_search t s = 
  try struct_iter (decl_type_search t) (spec_type_search t) s; false
  with Found -> true


(*s Generating the signature. *)

let rec msig_of_ms = function 
  | [] -> [] 
  | (l,SEdecl (Dind (kn,i))) :: ms -> (l,Spec (Sind (kn,i))) :: (msig_of_ms ms)
  | (l,SEdecl (Dterm (r,_,t))) :: ms -> (l,Spec (Sval (r,t))) :: (msig_of_ms ms)
  | (l,SEdecl (Dtype (r,v,t))) :: ms -> 
      (l,Spec (Stype (r,v,Some t))) :: (msig_of_ms ms) 
  | (l,SEdecl (Dfix (rv,_,tv))) :: ms -> 
      let msig = ref (msig_of_ms ms) in 
      for i = Array.length rv - 1 downto 0 do 
	msig := (l,Spec (Sval (rv.(i),tv.(i))))::!msig
      done; 
      !msig
  | (l,SEmodule m) :: ms -> (l,Smodule m.ml_mod_type) :: (msig_of_ms ms)
  | (l,SEmodtype m) :: ms -> (l,Smodtype m) :: (msig_of_ms ms)

let signature_of_structure s = 
  List.map (fun (mp,ms) -> mp,msig_of_ms ms) s 


