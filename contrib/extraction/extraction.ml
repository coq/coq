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
open Nameops
open Term
open Termops
open Declarations
open Environ
open Reductionops
open Inductive
open Inductiveops
open Instantiate
open Miniml
open Table
open Mlutil
open Closure
open Summary
open Libnames
open Nametab
(*i*)

(*S Extraction results. *)

(* The type [flag] gives us information about any Coq term: 
   \begin{itemize}
   \item [TypeScheme] denotes a type scheme, that is 
     something that will become a type after enough applications. 
     More formally, a type scheme has type $(x_1:X_1)\ldots(x_n:X_n)s$ with 
     [s = Set], [Prop] or [Type] 
   \item [Default] denotes the other cases. It may be inexact after 
     instanciation. For example [(X:Type)X] is [Default] and may give [Set]
     after instanciation, which is rather [TypeScheme]
   \item [Logic] denotes a term of sort [Prop], or a type scheme on sort [Prop]
   \item [Info] is the opposite. The same example [(X:Type)X] shows 
     that an [Info] term might in fact be [Logic] later on. 
   \end{itemize} *)

type info = Logic | Info

type scheme = TypeScheme | Default

type flag = info * scheme

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)
   
(* Convention: outmost lambda/product gives the head of the list, 
   and [true] means that the argument is to be kept. *)

type signature = bool list

(* The [ind_extraction_result] is used to save the extraction of 
   an inductive type. In the informative case, it stores a signature 
   and a type variable list. *)

type ind_extraction_result = signature * identifier list 

(* For an informative constructor, the [cons_extraction_result] 
   contains the list of the types of its arguments and the number of 
   parameters to discard. *)

type cons_extraction_result = ml_type list * int  

(*S Tables to keep the extraction results. *)

let visited_inductive = ref (Gset.empty : kernel_name Gset.t)
let visit_inductive k = visited_inductive := Gset.add k !visited_inductive
let already_visited_inductive k = Gset.mem k !visited_inductive

let inductive_table = 
  ref (Gmap.empty : (inductive, ind_extraction_result) Gmap.t)
let add_inductive i e = inductive_table := Gmap.add i e !inductive_table
let lookup_inductive i = Gmap.find i !inductive_table

let constructor_table = 
  ref (Gmap.empty : (constructor, cons_extraction_result) Gmap.t)
let add_constructor c e = constructor_table := Gmap.add c e !constructor_table
let lookup_constructor c = Gmap.find c !constructor_table

let cst_term_table = ref (Gmap.empty : (kernel_name, ml_decl) Gmap.t)
let add_cst_term kn d = cst_term_table := Gmap.add kn d !cst_term_table
let lookup_cst_term kn = Gmap.find kn !cst_term_table

let cst_type_table = ref (Gmap.empty : (kernel_name, ml_schema) Gmap.t)
let add_cst_type kn s = cst_type_table := Gmap.add kn s !cst_type_table
let lookup_cst_type kn = Gmap.find kn !cst_type_table 

(* Tables synchronization. *)

let freeze () =
  !visited_inductive, !inductive_table, 
  !constructor_table, !cst_term_table, !cst_type_table

let unfreeze (vi,it,ct,te,ty) =
  visited_inductive := vi; inductive_table := it; constructor_table := ct;
  cst_term_table := te; cst_type_table := ty

let _ = declare_summary "Extraction tables"
	  { freeze_function = freeze;
	    unfreeze_function = unfreeze;
	    init_function = (fun () -> ());
	    survive_section = true }

(*S Generation of flags and signatures. *)

let none = Evd.empty

let type_of env c = Retyping.get_type_of env none (strip_outer_cast c)

let sort_of env c = Retyping.get_sort_family_of env none (strip_outer_cast c)

let is_axiom kn = (Global.lookup_constant kn).const_body = None

(*s [flag_of_type] transforms a type [t] into a [flag]. 
  Really important function. *)

let rec flag_of_type env t = 
  let t = whd_betadeltaiota env none t in 
  match kind_of_term t with
    | Prod (x,t,c) -> flag_of_type (push_rel (x,None,t) env) c
    | Sort (Prop Null) -> (Logic,TypeScheme)
    | Sort _ -> (Info,TypeScheme)
    | _ -> if (sort_of env t) = InProp then (Logic,Default) else (Info,Default)

(*s Two particular cases of [flag_of_type]. *)

let is_default env t = (flag_of_type env t = (Info, Default))

let is_info_scheme env t = (flag_of_type env t = (Info, TypeScheme))

(*s [type_sign] gernerates a signature aimed at treating a type application. *)

let rec type_sign env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	(is_info_scheme env t)::(type_sign (push_rel_assum (n,t) env) d)
    | _ -> []

(*s [type_sign_vl] does the same, plus a type var list. *)

let rec type_sign_vl env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	let s,vl = type_sign_vl (push_rel_assum (n,t) env) d in 
	if not (is_info_scheme env t) then false::s, vl
	else true::s, (next_ident_away (id_of_name n) vl) :: vl
    | _ -> [],[]

(*S Management of type variable contexts. *)

(* A De Bruijn variable context (db) is a context for translating Coq [Rel]  
   into ML type [Tvar]. *)

(*s From a type signature toward a type variable context (db). *)

let db_from_sign s = 
  let rec make i acc = function 
    | [] -> acc  
    | true :: l -> make (i+1) (i::acc) l
    | false :: l -> make i (0::acc) l
  in make 1 [] s

(*s Create a type variable context from indications taken from 
  an inductive type (see just below). *) 

let rec db_from_ind dbmap i = 
  if i = 0 then []
  else (try Intmap.find i dbmap with Not_found -> 0)::(db_from_ind dbmap (i-1))

(*s [parse_ind_args] builds a map: [i->j] iff the i-th Coq argument 
  of a constructor corresponds to the j-th type var of the ML inductive. *)

(* \begin{itemize}
   \item [si] : signature of the inductive
   \item [i] :  counter of Coq args for [(I args)] 
   \item [j] : counter of ML type vars 
   \item [relmax] : total args number of the constructor 
   \end{itemize} *)

let parse_ind_args si args relmax = 
  let rec parse i j = function 
    | [] -> Intmap.empty
    | false :: s -> parse (i+1) j s
    | true :: s -> 
      (match kind_of_term args.(i-1) with 
	 | Rel k -> Intmap.add (relmax+1-k) j (parse (i+1) (j+1) s)
	 | _ -> parse (i+1) (j+1) s)
  in parse 1 1 si 

(*S Extraction of a type. *)

(* [extract_type env db c args] is used to produce an ML type from the 
   coq term [(c args)], which is supposed to be a Coq type. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

(* [j] stands for the next ML type var. [j=0] means we do not 
   generate ML type var anymore (in subterms for example). *) 

let rec extract_type env db j c args = 
  match kind_of_term (whd_betaiotazeta c) with
    | Var _ -> error_section ()
    | App (d, args') ->
	(* We just accumulate the arguments. *)
	extract_type env db j d (Array.to_list args' @ args)
    | Lambda (_,_,d) -> 
	(match args with 
	   | [] -> assert false (* otherwise the lambda would be reductible. *)
	   | a :: args -> extract_type env db j (subst1 a d) args)
    | Prod (n,t,d) ->
	assert (args = []); 
	let env' = push_rel_assum (n,t) env in 
	(match flag_of_type env t with 
	   | (Info, Default) -> 
	       (* Standard case: two [extract_type] ... *)
	       let mld = extract_type env' (0::db) j d [] in 
	       if mld = Tdummy then Tdummy 
	       else Tarr (extract_type env db 0 t [], mld) 
	   | (Info, TypeScheme) when j > 0 -> 
	       (* A new type var. *)
	       let mld = extract_type env' (j::db) (j+1) d [] in 
	       if mld = Tdummy then Tdummy else Tarr (Tdummy, mld)
	   | _ -> 
	       let mld = extract_type env' (0::db) j d [] in 
	       if mld = Tdummy then Tdummy else Tarr (Tdummy, mld))
    | Sort _ -> Tdummy (* The two logical cases. *)
    | _ when sort_of env (applist (c, args)) = InProp -> Tdummy 
    | Rel n -> 
	(match lookup_rel n env with
           | (_,Some t,_) -> extract_type env db j (lift n t) args
	   | _ -> 
	       (* Asks [db] a translation for [n]. *)
	       if n > List.length db then Tunknown 
	       else let n' = List.nth db (n-1) in 
	       if n' = 0 then Tunknown else Tvar n')
    | Const kn when is_ml_extraction (ConstRef kn) -> 
	assert (args = []); 
	Tglob (ConstRef kn,[])
    | Const kn when is_axiom kn -> 
	(* There are two kinds of informative axioms here, *)
	(* - the types that should be realized via [Extract Constant] *)
	(* - the type schemes that are not realizable (yet). *) 
	if args = [] then error_axiom kn
	else error_axiom_scheme kn 
    | Const kn ->
	let body = constant_value env kn in 
	let mlt1 = extract_type env db j (applist (body, args)) [] in 
	(match mlt_env (ConstRef kn) with 
	   | Some mlt ->
	       if mlt = Tdummy then Tdummy
               else 
		 let s = type_sign env (constant_type env kn) in 
		 let mlt2 = extract_type_app env db (ConstRef kn,s) args in 
		 (* ML type abbreviation behave badly with respect to Coq *)
		 (* reduction. Try to find the shortest correct answer. *) 
		 if type_eq mlt_env mlt1 mlt2 then mlt2 else mlt1
	   | None -> mlt1)
    | Ind kni ->
	let si = fst (extract_inductive kni) in 
	extract_type_app env db (IndRef kni,si) args
    | Case _ | Fix _ | CoFix _ -> Tunknown
    | _ -> assert false

(* [extract_maybe_type] calls [extract_type] when used on a Coq type, 
   and otherwise returns [Tdummy] or [Tunknown] *)

and extract_maybe_type env db c = 
  let t = whd_betadeltaiota env none (type_of env c) in 
  if isSort t then extract_type env db 0 c [] 
  else if sort_of env t = InProp then Tdummy else Tunknown

(*s Auxiliary function dealing with type application. 
  Precondition: [r] is a type scheme represented by the signature [s], 
  and is completely applied: [List.length args = List.length s]. *)
		  
and extract_type_app env db (r,s) args =
  let ml_args = 
    List.fold_right 
      (fun (b,c) a -> if b then 
	 let p = List.length (fst (splay_prod env none (type_of env c))) in
         let db = iterate (fun l -> 0 :: l) p db in
         (extract_type_scheme env db c p) :: a
       else a)
      (List.combine s args) []
  in Tglob (r,  ml_args)

(*S Extraction of a type scheme. *)

(* [extract_type_scheme env db c p] works on a Coq term [c] which is
  an informative type scheme. It means that [c] is not a Coq type, but will 
  be when applied to sufficiently many arguments ([p] in fact).  
  This function decomposes p lambdas, with eta-expansion if needed. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

and extract_type_scheme env db c p = 
  if p=0 then extract_type env db 0 c [] 
  else 
    let c = whd_betaiotazeta c in 
    match kind_of_term c with 
      | Lambda (n,t,d) -> 
          extract_type_scheme (push_rel_assum (n,t) env) db d (p-1)
      | _ ->  
          let rels = fst (splay_prod env none (type_of env c)) in
          let env = push_rels_assum rels env in  
          let eta_args = List.rev_map mkRel (interval 1 p) in 
          extract_type env db 0 (lift p c) eta_args


(*S Extraction of an inductive type. *)

(* [extract_inductive] answers a [ind_extraction_result] in
   case of an informative inductive, and raises [Not_found] otherwise *)

and extract_inductive ((kn,_) as i) =
  if not (already_visited_inductive kn) then extract_mib kn; 
  lookup_inductive i
			     
(* [extract_constructor] answers a [cons_extraction_result] in
   case of an informative constructor, and raises [Not_found] otherwise *)

and extract_constructor (((kn,_),_) as c) =
  if not (already_visited_inductive kn) then extract_mib kn; 
  lookup_constructor c

(* The real job: *)

and extract_mib kn =
  visit_inductive kn; 
  let env = Global.env () in 
  let (mib,mip) = Global.lookup_inductive (kn,0) in
  (* Everything concerning parameters. *)
  (* We do that first, since they are common to all the [mib]. *)
  let params_nb = mip.mind_nparams in
  let params_env = push_rel_context mip.mind_params_ctxt env in
  (* First pass: we store inductive signatures together with *)
  (* their type var list. *)
  for i = 0 to mib.mind_ntypes - 1 do
    let mip = snd (Global.lookup_inductive (kn,i)) in 
    if mip.mind_sort <> (Prop Null) then 
      add_inductive (kn,i) (type_sign_vl env mip.mind_nf_arity)
  done;
  (* Second pass: we extract constructors *)
  for i = 0 to mib.mind_ntypes - 1 do
    let ip = (kn,i) in 
    let mip = snd (Global.lookup_inductive ip) in
    if mip.mind_sort <> (Prop Null) then
      let s = fst (lookup_inductive ip) in 
      let types = arities_of_constructors env ip in
      for j = 0 to Array.length types - 1 do 
	let t = snd (decompose_prod_n params_nb types.(j)) in
	let args = match kind_of_term (snd (decompose_prod t)) with
	  | App (f,args) -> args (* [kind_of_term f = Ind ip] *)
	  | _ -> [||]
	in 
	let dbmap = parse_ind_args s args (nb_prod t + params_nb) in 
	let db = db_from_ind dbmap params_nb in 
	let l = extract_type_cons params_env db dbmap t (params_nb+1) in 
	add_constructor (ip,j+1) (l,params_nb)
      done
  done

(*s [extract_type_cons] extracts the type of an inductive 
  constructor toward the corresponding list of ML types. *)

(* \begin{itemize}
   \item [db] is a context for translating Coq [Rel] into ML type [Tvar] 
   \item [dbmap] is a translation map (produced by a call to [parse_in_args])
   \item [i] is the rank of the current product (initially [params_nb+1]) 
   \end{itemize} *)

and extract_type_cons env db dbmap c i =
  match kind_of_term (whd_betadeltaiota env none c) with 
    | Prod (n,t,d) -> 
	let env' = push_rel_assum (n,t) env in
	let db' = (try Intmap.find i dbmap with Not_found -> 0) :: db in
	let l = extract_type_cons env' db' dbmap d (i+1) in 
	(extract_type env db 0 t []) :: l 
    | _ -> [] 

(*s Recording the ML type abbreviation of a Coq type scheme constant. *)

and mlt_env r = match r with 
  | ConstRef kn -> 
      (try match lookup_cst_term kn with 
	 | Dtype (_,vl,mlt) -> Some mlt
	 | _ -> None
       with Not_found -> 
	 let env = Global.env() in    
	 let cb = Global.lookup_constant kn in
	 let typ = cb.const_type in
	 match cb.const_body with
	   | None -> None
	   | Some l_body -> 
	       (match flag_of_type env typ with 
		  | Info,TypeScheme -> 
		      let body = Declarations.force l_body in
		      let s,vl = type_sign_vl env typ in 
		      let db = db_from_sign s in 
		      let t = extract_type_scheme env db body (List.length s) 
		      in add_cst_term kn (Dtype (r, vl, t)); Some t
		  | _ -> None))
  | _ -> None

let type_expand = type_expand mlt_env
let type_neq = type_neq mlt_env
let type_to_sign = type_to_sign mlt_env
let type_expunge = type_expunge mlt_env

(*s Extraction of the type of a constant. *)

let record_constant_type kn = 
  try lookup_cst_type kn
  with Not_found -> 
    let env = Global.env () in 
    let mlt = extract_type env [] 1 (constant_type env kn) [] in 
    let schema = (type_maxvar mlt, mlt)
    in add_cst_type kn schema; schema

(*s Looking for informative singleton case, i.e. an inductive with one 
   constructor which has one informative argument. This dummy case will 
   be simplified. *)

let is_singleton_inductive ip = 
  let (mib,mip) = Global.lookup_inductive ip in 
  mib.mind_finite &&
  (mib.mind_ntypes = 1) &&
  (Array.length mip.mind_consnames = 1) && 
  try 
    let l = List.filter (type_neq Tdummy) (fst (extract_constructor (ip,1))) in
    List.length l = 1 && not (type_mem_kn (fst ip) (List.hd l))
  with Not_found -> false
          
let is_singleton_constructor ((kn,i),_) = 
  is_singleton_inductive (kn,i) 

(*S Extraction of a term. *)

(* Precondition: [(c args)] is not a type scheme, and is informative. *)

(* [mle] is a ML environment [Mlenv.t]. *)
(* [mlt] is the ML type we want our extraction of [(c args)] to have. *)

let rec extract_term env mle mlt c args = 
  match kind_of_term c with
    | App (f,a) ->
	extract_term env mle mlt f (Array.to_list a @ args)
    | Lambda (n, t, d) ->
	let id = id_of_name n in 
	(match args with 
	   | a :: l -> 
	       (* We make as many [LetIn] as possible. *)
 	       let d' = mkLetIn (Name id,a,t,applistc d (List.map (lift 1) l))
	       in extract_term env mle mlt d' []
	   | [] -> 
	       let env' = push_rel_assum (Name id, t) env in 
	       let id, a = 
		 if is_default env t 
		 then id, new_meta () 
		 else dummy_name, Tdummy in 
	       let b = new_meta () in 
	       (* If [mlt] cannot be unified with an arrow type, then magic! *)
	       let magic = needs_magic (mlt, Tarr (a, b)) in 
	       let d' = extract_term env' (Mlenv.push_type mle a) b d [] in 
	       put_magic_if magic (MLlam (id, d')))
    | LetIn (n, c1, t1, c2) ->
	let id = id_of_name n in 
	let env' = push_rel (Name id, Some c1, t1) env in 
	let args' = List.map (lift 1) args in 
	if is_default env t1 then 
	  let a = new_meta () in 
	  let c1' = extract_term env mle a c1 [] in
	  (* The type of [c1'] is generalized and stored in [mle]. *)
	  let mle' = Mlenv.push_gen mle a in 
	  MLletin (id, c1', extract_term env' mle' mlt c2 args') 
	else 
	  let mle' = Mlenv.push_std_type mle Tdummy in 
	  ast_pop (extract_term env' mle' mlt c2 args')
    | Const kn ->
	extract_cst_app env mle mlt kn args
    | Construct cp ->
	extract_cons_app env mle mlt cp args
    | Rel n ->
	(* As soon as the expected [mlt] for the head is known, *)
	(* we unify it with an fresh copy of the stored type of [Rel n]. *)
	let extract_rel mlt = put_magic (mlt, Mlenv.get mle n) (MLrel n)
	in extract_app env mle mlt extract_rel args 
    | Case ({ci_ind=ip},_,c0,br) ->
 	extract_app env mle mlt (extract_case env mle (ip,c0,br)) args
    | Fix ((_,i),recd) ->
 	extract_app env mle mlt (extract_fix env mle i recd) args 
    | CoFix (i,recd) ->
 	extract_app env mle mlt (extract_fix env mle i recd) args
    | Cast (c, _) -> extract_term env mle mlt c args
    | Ind _ | Prod _ | Sort _ | Meta _ | Evar _ -> assert false 
    | Var _ -> error_section ()

(*s [extract_maybe_term] is [extract_term] for usual terms, else [MLdummy] *) 

and extract_maybe_term env mle mlt c =
  if is_default env (type_of env c) then extract_term env mle mlt c [] 
  else put_magic (mlt, Tdummy) MLdummy

(*s Generic way to deal with an application. *)

(* We first type all arguments starting with unknown meta types. 
   This gives us the expected type of the head. Then we use the 
   [mk_head] to produce the ML head from this type. *)

and extract_app env mle mlt mk_head args = 
  let metas = List.map new_meta args in 
  let type_head = type_recomp (metas, mlt) in 
  let mlargs = List.map2 (extract_maybe_term env mle) metas args in 
  if mlargs = [] then mk_head type_head else MLapp (mk_head type_head, mlargs)

(*s Auxiliary function used to extract arguments of constant or constructor. *)

and make_mlargs env e s args typs = 
  let l = ref s in 
  let keep () = match !l with [] -> true | b :: s -> l:=s; b in
  let rec f = function  
    | [], [] -> [] 
    | a::la, t::lt when keep() -> extract_maybe_term env e t a :: (f (la,lt))
    | _::la, _::lt -> f (la,lt)
    | _ -> assert false 
  in f (args,typs)

(*s Extraction of a constant applied to arguments. *)

and extract_cst_app env mle mlt kn args = 
  (* First, the [ml_schema] of the constant, in expanded version. *) 
  let nb,t = record_constant_type kn in 
  let schema = nb, type_expand t in 
  (* Then the expected type of this constant. *)
  let metas = List.map new_meta args in 
  let type_head = type_recomp (metas,mlt) in 
  (* The head gets a magic if stored and expected types differ. *)
  let head = 
    let h = MLglob (ConstRef kn) in 
    put_magic (type_recomp (metas,mlt), instantiation schema) h in
  (* Now, the extraction of the arguments. *)
  let s = type_to_sign (snd schema) in 
  let ls = List.length s in 
  let la = List.length args in
  let mla = make_mlargs env mle s args metas in 
  (* Different situations depending of the number of arguments: *)
  if ls = 0 then head
  else if List.mem true s then 
    if la >= ls then MLapp (head, mla)
    else 
      (* Not enough arguments. We complete via eta-expansion. *)
      let ls' = ls-la in
      let s' = list_lastn ls' s in
      let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
      anonym_or_dummy_lams (MLapp (head, mla)) s'
  else 
    (* In the special case of always false signature, one dummy lam is left. *)
    (* So a [MLdummy] is left accordingly. *) 
    if la >= ls then MLapp (head, MLdummy :: mla)
    else dummy_lams head (ls-la-1)

(*s Extraction of an inductive constructor applied to arguments. *)

(* \begin{itemize}
   \item In ML, contructor arguments are uncurryfied. 
   \item We managed to suppress logical parts inside inductive definitions,
   but they must appears outside (for partial applications for instance)
   \item We also suppressed all Coq parameters to the inductives, since
   they are fixed, and thus are not used for the computation.
   \end{itemize} *)

and extract_cons_app env mle mlt ((ip,_) as cp) args =
  (* First, we build the type of the constructor, stored in small pieces. *)
  let types, params_nb = extract_constructor cp in
  let types = List.map type_expand types in
  let nb_tvar = List.length (snd (extract_inductive ip)) in 
  let list_tvar = List.map (fun i -> Tvar i) (interval 1 nb_tvar) in 
  let type_cons = type_recomp (types, Tglob (IndRef ip, list_tvar)) in
  let type_cons = instantiation (nb_tvar, type_cons) in 
  (* Then, the usual variables [s], [ls], [la], ... *)
  let s = List.map ((<>) Tdummy) types in
  let ls = List.length s in 
  let la = List.length args in 
  assert (la <= ls + params_nb);
  let la' = max 0 (la - params_nb) in 
  let args' = list_lastn la' args in 
  (* Now, we build the expected type of the constructor *)
  let metas = List.map new_meta args' in 
  let type_head = type_recomp (metas, mlt) in
  (* If stored and expected types differ, then magic! *)
  let magic = needs_magic (type_cons, type_head) in 
  let head mla = 
    if is_singleton_constructor cp then 
      put_magic_if magic (List.hd mla) (* assert (List.length mla = 1) *)
    else put_magic_if magic (MLcons (ConstructRef cp, mla))
  in 
  (* Different situations depending of the number of arguments: *)
  if la < params_nb then 
    let head' = head (eta_args_sign ls s) in 
    dummy_lams (anonym_or_dummy_lams head' s) (params_nb - la)
  else 
    let mla = make_mlargs env mle s args' metas in 
    if la = ls + params_nb then head mla
    else (* [ params_nb <= la <= ls + params_nb ] *) 
      let ls' = params_nb + ls - la in 
      let s' = list_lastn ls' s in 
      let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
      anonym_or_dummy_lams (head mla) s'

(*S Extraction of a case. *)

and extract_case env mle (ip,c,br) mlt = 
  (* [br]: bodies of each branch (in functional form) *)
  (* [ni]: number of arguments without parameters in each branch *)
  let ni = mis_constr_nargs ip in
  let br_size = Array.length br in 
  assert (Array.length ni = br_size); 
  if br_size = 0 then MLexn "absurd case"
  else 
    (* [c] has an inductive type, and is not a type scheme type. *)
    let t = type_of env c in 
    (* The only non-informative case: [c] is of sort [Prop] *)
    if (sort_of env t) = InProp then 
      begin 
	(* Logical singleton case: *)
	(* [match c with C i j k -> t] becomes [t'] *)
	assert (br_size = 1);
	let s = iterate (fun l -> false :: l) ni.(0) [] in
	let mlt = iterate (fun t -> Tarr (Tdummy, t)) ni.(0) mlt in 
	let e = extract_maybe_term env mle mlt br.(0) in 
	snd (case_expunge s e)
      end 
    else 
      let nb_tvar = List.length (snd (extract_inductive ip)) in 
      let metas = Array.init nb_tvar new_meta in 
      (* The extraction of the head. *)
      let type_head = Tglob (IndRef ip, Array.to_list metas) in
      let a = extract_term env mle type_head c [] in 
      (* The extraction of each branch. *)
      let extract_branch i = 
	(* The types of the arguments of the corresponding constructor. *)
	let f t = type_subst_vect metas (type_expand t) in 
	let l = List.map f (fst (extract_constructor (ip,i+1))) in
	(* Extraction of the branch (in functional form). *)
	let e = extract_maybe_term env mle (type_recomp (l,mlt)) br.(i) in 
	(* We suppress dummy arguments according to signature. *)
	let ids,e = case_expunge (List.map ((<>) Tdummy) l) e in
	(ConstructRef (ip,i+1), List.rev ids, e)
      in
      if is_singleton_inductive ip then 
	begin 
	  (* Informative singleton case: *)
	  (* [match c with C i -> t] becomes [let i = c' in t'] *)
	  assert (br_size = 1);
	  let (_,ids,e') = extract_branch 0 in
	  assert (List.length ids = 1);
	  MLletin (List.hd ids,a,e')
	end 
      else 
	(* Standard case: we apply [extract_branch]. *)
	MLcase (a, Array.init br_size extract_branch)
  
(*s Extraction of a (co)-fixpoint. *)

and extract_fix env mle i (fi,ti,ci as recd) mlt = 
  let n = Array.length fi in
  let env = push_rec_types recd env in 
  let metas = Array.map (fun _ -> new_meta ()) fi in 
  let magic = needs_magic (mlt, metas.(i)) in 
  let mle = Array.fold_left Mlenv.push_type mle metas in 
  let ei = array_map2 (extract_maybe_term env mle) metas ci in 
  put_magic_if magic (MLfix (i, Array.map id_of_name fi, ei))

(*S ML declarations. *)

(* [decomp_lams_eta env c t] finds the number [n] of products in the type [t], 
   and decompose the term [c] in [n] lambdas, with eta-expansion if needed. *)

let rec decomp_lams_eta env c t = 
  let rels = fst (splay_prod env none t) in 
  let n = List.length rels in 
  let m = nb_lam c in 
  if m >= n then decompose_lam_n n c 
  else
    let rels',c = decompose_lam c in 
    let d = n - m in 
    (* we'd better keep rels' as long as possible. *)
    let rels = (list_firstn d rels) @ rels' in
    let eta_args = List.rev_map mkRel (interval 1 d) in 
    rels, applist (lift d c,eta_args)

(*s From a constant to a ML declaration. *)

let extract_constant kn r = 
  let env = Global.env() in    
  let cb = Global.lookup_constant kn in
  let typ = cb.const_type in
  match cb.const_body with
    | None -> (* A logical axiom is risky, an informative one is fatal. *) 
        (match flag_of_type env typ with
	   | (Info,TypeScheme) -> 
	       if isSort typ then error_axiom kn 
	       else error_axiom_scheme kn
           | (Info,Default) -> error_axiom kn 
           | (Logic,TypeScheme) -> warning_axiom kn; Dtype (r, [], Tdummy)
	   | (Logic,Default) -> warning_axiom kn; Dterm (r, MLdummy, Tdummy))
    | Some l_body ->
	(match flag_of_type env typ with
	   | (Logic, Default) -> Dterm (r, MLdummy, Tdummy)
	   | (Logic, TypeScheme) -> Dtype (r, [], Tdummy)
	   | (Info, Default) -> 
	       let body = Declarations.force l_body in
	       (* Decomposing the top level lambdas of [body]. *)
	       let rels,c = decomp_lams_eta env body typ in
	       (* The lambdas names. *)
	       let ids = List.map (fun (n,_) -> id_of_name n) rels in 
	       (* The according Coq environment. *)
	       let env = push_rels_assum rels env in
	       (* The ML part: *)
	       reset_meta_count (); 
	       (* The short type [t] (i.e. possibly with abbreviations). *)
	       let t = snd (record_constant_type kn) in 
	       (* The real type [t']: without head lambdas, expanded, *)
	       (* and with [Tvar] translated to [Tvar'] (not instantiable). *)
	       let l,t' = type_decomp (type_expand (var2var' t)) in 
	       (* The initial ML environment. *)
	       let mle = List.fold_left Mlenv.push_std_type Mlenv.empty l in 
	       (* The real extraction: *)
	       let e = extract_term env mle t' c [] in
	       if e = MLdummy then Dterm (r, MLdummy, Tdummy)
	       else 
		 (* Expunging term and type from dummy lambdas. *) 
		 let s = List.map ((<>) Tdummy) l in 
		 Dterm (r, term_expunge s (ids,e), type_expunge t)
	   | (Info, TypeScheme) -> 
	       let body = Declarations.force l_body in
	       let s,vl = type_sign_vl env typ in 
               let db = db_from_sign s in 
               let t = extract_type_scheme env db body (List.length s) in 
               Dtype (r, vl, t))

let extract_constant_cache kn r = 
  try lookup_cst_term kn 
  with Not_found ->
    let d = extract_constant kn r
    in add_cst_term kn d; d

(*s From an inductive to a ML declaration. *)

let extract_inductive_declaration kn =
  if not (already_visited_inductive kn) then extract_mib kn; 
  let ip = (kn,0) in 
  if is_singleton_inductive ip then
    let t = 
      List.hd (List.filter (type_neq Tdummy) (fst (lookup_constructor (ip,1))))
    and vl = snd (lookup_inductive ip) in 
    Dtype (IndRef ip,vl,t)
  else
    let mib = Global.lookup_mind kn in
    let one_ind ip n = 
      iterate_for (-n) (-1)
	(fun j l -> 
	   let cp = (ip,-j) in 
	   let mlt = fst (lookup_constructor cp) in 
	   (ConstructRef cp, List.filter (type_neq Tdummy) mlt)::l) []
    in
    let l = 
      iterate_for (1 - mib.mind_ntypes) 0
	(fun i acc -> 
	   let ip = (kn,-i) in
	   let nc = Array.length mib.mind_packets.(-i).mind_consnames in 
	   try 
	     let vl = snd (lookup_inductive ip) in 
	     (vl, IndRef ip, one_ind ip nc) :: acc
	   with Not_found -> acc)
	[] 
    in
    Dind (l, not mib.mind_finite)

(*s From a global reference to a ML declaration. *)

let extract_declaration r = match r with
  | ConstRef kn -> extract_constant_cache kn r
  | IndRef (kn,_) -> extract_inductive_declaration kn
  | ConstructRef ((kn,_),_) -> extract_inductive_declaration kn
  | VarRef kn -> error_section ()

(*s Check if a global reference corresponds to a logical inductive. *)

let decl_is_logical_ind = function 
  | IndRef ip -> (try ignore (extract_inductive ip); false with _ -> true)
  | ConstructRef cp -> 
      (try ignore (extract_constructor cp); false with _ -> true)
  | _ -> false

(*s Check if a global reference corresponds to the constructor of 
  a singleton inductive. *)

let decl_is_singleton = function 
  | ConstructRef cp -> is_singleton_constructor cp 
  | _ -> false 


