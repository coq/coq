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
open Term
open Declarations
open Environ
open Reductionops
open Inductive
open Termops
open Inductiveops
open Recordops
open Nameops
open Summary
open Libnames
open Nametab
open Miniml
open Table
open Mlutil
(*i*)

exception I of inductive_info

let none = Evd.empty

let type_of env c = Retyping.get_type_of env none (strip_outer_cast c)

let sort_of env c = Retyping.get_sort_family_of env none (strip_outer_cast c)

let is_axiom kn = (Global.lookup_constant kn).const_body = None

(*S Generation of flags and signatures. *)

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
	if args = [] then error_axiom (ConstRef kn)
	else error_axiom_scheme (ConstRef kn) 
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
    | Ind ((kn,i) as ip) ->
	let s = (extract_inductive kn).ind_packets.(i).ip_sign in  
	extract_type_app env db (IndRef ip,s) args
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

and extract_inductive kn =
  try lookup_ind kn with Not_found -> 
    add_recursors kn; 
    let env = Global.env () in 
    let (mib,mip) = Global.lookup_inductive (kn,0) in
    (* Everything concerning parameters. *)
    (* We do that first, since they are common to all the [mib]. *)
    let npar = mip.mind_nparams in
    let epar = push_rel_context mip.mind_params_ctxt env in
    (* First pass: we store inductive signatures together with *)
    (* their type var list. *)
    let packets = 
      Array.map 
	(fun mip -> 
	   let b = mip.mind_sort <> (Prop Null) in 
	   let s,v = if b then type_sign_vl env mip.mind_nf_arity else [],[] in
	   let t = Array.make (Array.length mip.mind_nf_lc) [] in 
	   { ip_logical = (not b); ip_sign = s; ip_vars = v; ip_types = t }) 
	mib.mind_packets 
    in 
    add_ind kn {ind_info = Standard; ind_nparams = npar; ind_packets = packets};
    (* Second pass: we extract constructors *)
    for i = 0 to mib.mind_ntypes - 1 do
      let p = packets.(i) in 
      if not p.ip_logical then
	let types = arities_of_constructors env (kn,i) in 
	for j = 0 to Array.length types - 1 do 
	  let t = snd (decompose_prod_n npar types.(j)) in
	  let args = match kind_of_term (snd (decompose_prod t)) with
	    | App (f,args) -> args (* [kind_of_term f = Ind ip] *)
	    | _ -> [||]
	  in 
	  let dbmap = parse_ind_args p.ip_sign args (nb_prod t + npar) in 
	  let db = db_from_ind dbmap npar in 
	  p.ip_types.(j) <- extract_type_cons epar db dbmap t (npar+1)
	done
    done;
    (* Third pass: we determine special cases. *)
    let ind_info = 
      try 
	if not mib.mind_finite then raise (I Coinductive); 
	if mib.mind_ntypes <> 1 then raise (I Standard); 
	let p = packets.(0) in 
	if p.ip_logical then raise (I Standard);
	if Array.length p.ip_types <> 1 then raise (I Standard);
	let typ = p.ip_types.(0) in 
	let l = List.filter (type_neq mlt_env Tdummy) typ in 
	if List.length l = 1 && not (type_mem_kn kn (List.hd l)) 
	then raise (I Singleton); 
	if l = [] then raise (I Standard); 
	let projs = 
	  try (find_structure (kn,0)).s_PROJ 
	  with Not_found -> raise (I Standard);
	in 
	let s = List.map (type_neq mlt_env Tdummy) typ in
	let check (_,o) = match o with 
	  | None -> raise (I Standard)
	  | Some kn -> ConstRef kn 
	in  
	add_record kn (List.map check (List.filter fst (List.combine s projs))); 
	raise (I Record)
      with (I info) -> info
    in
    let i = {ind_info = ind_info; ind_nparams = npar; ind_packets = packets} in 
    add_ind kn i; i

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
      (try match lookup_term kn with 
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
		      in add_term kn (Dtype (r, vl, t)); Some t
		  | _ -> None))
  | _ -> None

let type_expand = type_expand mlt_env
let type_neq = type_neq mlt_env
let type_to_sign = type_to_sign mlt_env
let type_expunge = type_expunge mlt_env

(*s Extraction of the type of a constant. *)

let record_constant_type kn = 
  try lookup_type kn
  with Not_found -> 
    let env = Global.env () in 
    let mlt = extract_type env [] 1 (constant_type env kn) [] in 
    let schema = (type_maxvar mlt, mlt)
    in add_type kn schema; schema

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

and extract_cons_app env mle mlt (((kn,i) as ip,j) as cp) args =
  (* First, we build the type of the constructor, stored in small pieces. *)
  let mi = extract_inductive kn in 
  let params_nb = mi.ind_nparams in 
  let oi = mi.ind_packets.(i) in 
  let nb_tvars = List.length oi.ip_vars
  and types = List.map type_expand oi.ip_types.(j-1) in
  let list_tvar = List.map (fun i -> Tvar i) (interval 1 nb_tvars) in 
  let type_cons = type_recomp (types, Tglob (IndRef ip, list_tvar)) in
  let type_cons = instantiation (nb_tvars, type_cons) in 
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
    if mi.ind_info = Singleton then 
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

and extract_case env mle ((kn,i) as ip,c,br) mlt = 
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
      let mi = extract_inductive kn in 
      let params_nb = mi.ind_nparams in 
      let oi = mi.ind_packets.(i) in 
      let metas = Array.init (List.length oi.ip_vars) new_meta in 
      (* The extraction of the head. *)
      let type_head = Tglob (IndRef ip, Array.to_list metas) in
      let a = extract_term env mle type_head c [] in 
      (* The extraction of each branch. *)
      let extract_branch i = 
	(* The types of the arguments of the corresponding constructor. *)
	let f t = type_subst_vect metas (type_expand t) in 
	let l = List.map f oi.ip_types.(i) in
	(* Extraction of the branch (in functional form). *)
	let e = extract_maybe_term env mle (type_recomp (l,mlt)) br.(i) in 
	(* We suppress dummy arguments according to signature. *)
	let ids,e = case_expunge (List.map ((<>) Tdummy) l) e in
	(ConstructRef (ip,i+1), List.rev ids, e)
      in
      if mi.ind_info = Singleton then 
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
	       if isSort typ then error_axiom r
	       else error_axiom_scheme r
           | (Info,Default) -> error_axiom r 
           | (Logic,TypeScheme) -> warning_axiom r; Dtype (r, [], Tdummy)
	   | (Logic,Default) -> warning_axiom r; Dterm (r, MLdummy, Tdummy))
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
	       let s = List.map ((<>) Tdummy) l in 
	       (* The initial ML environment. *)
	       let mle = List.fold_left Mlenv.push_std_type Mlenv.empty l in 
	       (* The real extraction: *)
	       let e = extract_term env mle t' c [] in
	       (* Expunging term and type from dummy lambdas. *) 
	       Dterm (r, term_expunge s (ids,e), type_expunge t)
	   | (Info, TypeScheme) -> 
	       let body = Declarations.force l_body in
	       let s,vl = type_sign_vl env typ in 
               let db = db_from_sign s in 
               let t = extract_type_scheme env db body (List.length s) in 
               Dtype (r, vl, t))

let extract_constant_cache kn r = 
  try lookup_term kn 
  with Not_found ->
    let d = extract_constant kn r
    in add_term kn d; d

let extract_inductive_declaration kn = 
  let ind = extract_inductive kn in 
  let f l = List.filter (type_neq Tdummy) l in 
  let packets = 
    Array.map (fun p -> { p with ip_types = Array.map f p.ip_types }) 
      ind.ind_packets
  in Dind (kn,{ ind with ind_packets = packets })

(*s From a global reference to a ML declaration. *)

let extract_declaration r = match r with
  | ConstRef kn -> extract_constant_cache kn r
  | IndRef (kn,_) -> extract_inductive_declaration kn
  | ConstructRef ((kn,_),_) -> extract_inductive_declaration kn
  | VarRef kn -> error_section ()


