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

let constant_table = 
  ref (Gmap.empty : (kernel_name, ml_decl) Gmap.t)
let add_constant kn d = constant_table := Gmap.add kn d !constant_table
let lookup_constant kn = Gmap.find kn !constant_table

let mltype_table = 
  ref (Gmap.empty : (kernel_name, ml_schema) Gmap.t)
let add_mltype kn s = mltype_table := Gmap.add kn s !mltype_table
let lookup_mltype kn = Gmap.find kn !mltype_table 

(* Tables synchronization. *)

let freeze () =
  !visited_inductive, !inductive_table, 
  !constructor_table, !constant_table, !mltype_table

let unfreeze (vi,it,cst,ct,st) =
  visited_inductive := vi; 
  inductive_table := it; constructor_table := cst;
  constant_table := ct; mltype_table := st

let _ = declare_summary "Extraction tables"
	  { freeze_function = freeze;
	    unfreeze_function = unfreeze;
	    init_function = (fun () -> ());
	    survive_section = true }

(*S Warning and Error messages. *)

let axiom_error_message kn =
  errorlabstrm "axiom_message"
    (str "You must specify an extraction for axiom" ++ spc () ++ 
       pr_kn kn ++ spc () ++ str "first.")

let axiom_warning_message kn = 
  Options.if_verbose warn 
    (str "This extraction depends on logical axiom" ++ spc () ++ 
     pr_kn kn ++ str "." ++ spc() ++ 
     str "Having false logical axiom in the environment when extracting" ++ 
     spc () ++ str "may lead to incorrect or non-terminating ML terms.")
    
let section_message () = 
  errorlabstrm "section_message"
    (str "You can't extract within a section. Close it and try again.")

(*S Generation of flags and signatures. *)

let none = Evd.empty

let type_of env c = Retyping.get_type_of env none (strip_outer_cast c)

let sort_of env c = Retyping.get_sort_family_of env none (strip_outer_cast c)

let is_axiom kn = (Global.lookup_constant kn).const_body = None

let break_prod env t =  
  match kind_of_term (whd_betadeltaiota env none t) with 
    | Prod (n,t1,t2) -> (t1,t2)
    | _ -> anomaly ("Non-fonctional construction ")

(*s [flag_of_type] transforms a type [t] into a [flag]. 
  Really important function. *)

let rec flag_of_type env t = 
  let t = whd_betadeltaiota env none t in 
  match kind_of_term t with
    | Prod (x,t,c) -> flag_of_type (push_rel (x,None,t) env) c
    | Sort (Prop Null) -> (Logic,TypeScheme)
    | Sort _ -> (Info,TypeScheme)
    | _ -> if (sort_of env t) = InProp then (Logic,Default) else (Info,Default)

(*s [is_default] is a particular case of [flag_of_type]. *)

let is_default env t = (flag_of_type env t = (Info, Default))

let is_info_sort env t = 
  match kind_of_term (whd_betadeltaiota env none t) with
    | Sort (Prop Null) -> false
    | Sort _ -> true 
    | _ -> false

let is_info_type_scheme env t = (flag_of_type env t = (Info, TypeScheme))

let is_type env t = isSort (whd_betadeltaiota env none (type_of env t))

(*s [type_sign_vl] gernerates a signature aimed at treating a term 
  application at the ML type level, and a type var list. *)

let rec type_sign_vl env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	let s,vl = type_sign_vl (push_rel_assum (n,t) env) d in 
	if not (is_info_type_scheme env t) then false::s, vl
	else true::s, (next_ident_away (id_of_name n) vl) :: vl
    | _ -> [],[]

let rec type_sign env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	(is_info_type_scheme env t)::(type_sign (push_rel_assum (n,t) env) d)
    | _ -> []

(*S Management of type variable contexts. *)

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
    | Var _ -> section_message ()
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
	if j > 0 && is_info_type_scheme env t then 
	  let mld = extract_type env' (j::db) (j+1) d [] in 
	  if mld = Tdummy then Tdummy 
	  else Tarr (Tdummy, mld)
	else
	  let mld = extract_type env' (0::db) j d [] in 
	  if mld = Tdummy then Tdummy 
	  else if not (is_default env t) then Tarr (Tdummy, mld)
	  else Tarr (extract_type env db 0 t [], mld)
    | Sort _ -> Tdummy
    | _ when sort_of env (applist (c, args)) = InProp -> Tdummy 
    | Rel n -> 
	(match lookup_rel n env with
           | (_,Some t,_) -> extract_type env db j (lift n t) args
	   | _ -> 
	       if n > List.length db then Tunknown 
	       else let n' = List.nth db (n-1) in 
	       if n' = 0 then Tunknown else Tvar n')
    | Const sp when is_ml_extraction (ConstRef sp) -> Tglob (ConstRef sp,[])
    | Const sp when is_axiom sp -> Tunknown
    | Const sp ->
	let body = constant_value env sp in 
	let mlt1 = extract_type env db j (applist (body, args)) [] in 
	(match mlt_env (ConstRef sp) with 
	   | Some mlt ->
	       if mlt = Tdummy then Tdummy
               else 
		 let s = type_sign env (constant_type env sp) in 
		 let mlt2 = extract_type_app env db (ConstRef sp,s) args in 
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
  let t = type_of env c in 
  if isSort (whd_betadeltaiota env none t) 
  then extract_type env db 0 c [] 
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
      (try match lookup_constant kn with 
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
		      in add_constant kn (Dtype (r, vl, t)); Some t
		  | _ -> None))
  | _ -> None

let type_expand = type_expand mlt_env
let type_neq = type_neq mlt_env
let type_to_sign = type_to_sign mlt_env
let type_expunge = type_expunge mlt_env

(*s Extraction of the type of a constant. *)

let record_constant_type kn = 
  try lookup_mltype kn
  with Not_found -> 
    let env = Global.env () in 
    let mlt = extract_type env [] 1 (constant_type env kn) [] in 
    let schema = (type_maxvar mlt, mlt)
    in add_mltype kn schema; schema

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

(*S Modification of the signature of terms. *)

(* We sometimes want to suppress [Logic] and [TypeScheme] parts 
   in the signature of a term. It is so: 
   \begin{itemize}
   \item after a case, in [extract_case]
   \item for the toplevel definition of a function, in [suppress_prop_eta] 
   below. By the way we do some eta-expansion if needed using 
   [expansion_prop_eta].
   \end{itemize}
   To ensure correction of execution, we then need to reintroduce 
   dummy lambdas around constructors and functions occurrences. 
   This is done by [abstract_constructor] and [abstract_constant]. *)

let expansion_prop_eta s (ids,c) =
  let rec abs ids rels i = function
    | [] -> 
	let a = List.rev_map (function MLrel x -> MLrel (i-x) | a -> a) rels
	in ids, MLapp (ast_lift (i-1) c, a) 
    | true :: l -> abs (anonymous :: ids) (MLrel i :: rels) (i+1) l 
    | false :: l -> abs (dummy_name :: ids) (MLdummy :: rels) (i+1) l
  in abs ids [] 1 s

let kill_all_prop_lams_eta e s = 
  let m = List.length s in 
  let n = nb_lams e in 
  let p = if m <= n then collect_n_lams m e 
  else expansion_prop_eta (snd (list_chop n s)) (collect_lams e) in 
  kill_some_lams (List.rev s) p

let kill_prop_lams_eta s (ids,c) =
  if s = [] then c 
  else 
    let ids,c = kill_some_lams (List.rev s) (ids,c) in 
    if ids = [] then MLlam (dummy_name, ast_lift 1 c)
    else named_lams ids c

(*S Extraction of a term. *)

(* Precondition: [c] is not a type scheme, and is informative. *)

let rec extract_term env mle mlt c args = 
  match kind_of_term c with
    | App (f,a) ->
	extract_term env mle mlt f (Array.to_list a @ args)
    | Lambda (n, t, d) ->
	let id = id_of_name n in 
	(match args with 
	   | a :: l -> 
 	       let d' = mkLetIn (Name id,a,t,applistc d (List.map (lift 1) l))
	       in extract_term env mle mlt d' []
	   | [] -> 
	       let env' = push_rel_assum (Name id, t) env in 
	       let id, a = 
		 if is_default env t 
		 then id, new_meta () 
		 else dummy_name, Tdummy in 
	       let b = new_meta () in 
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
    | Var _ -> section_message ()

(*s [extract_maybe_term] is [extract_term] for usual terms, else [MLdummy] *) 

and extract_maybe_term env mle mlt c =
  if is_default env (type_of env c) then extract_term env mle mlt c [] 
  else put_magic (mlt, Tdummy) MLdummy

(*s Generic way to deal with an application. *)

and extract_app env mle mlt mk_head args = 
  let metas = List.map new_meta args in 
  let type_head = type_recomp (metas, mlt) in 
  let mlargs = List.map2 (extract_maybe_term env mle) metas args in 
  if mlargs = [] then mk_head type_head else MLapp (mk_head type_head, mlargs)

(*s Extraction of a constant applied to arguments. *)

and make_mlargs env mle s args mlts = 
  let rec f = function 
    | _, [], [] -> [] 
    | [], a::args, mlt::mlts -> 
	(extract_maybe_term env mle mlt a) :: (f ([],args,mlts))
    | true::s, a::args, mlt::mlts -> 
	(extract_maybe_term env mle mlt a) :: (f (s,args,mlts))
    | false::s, _::args, _::mlts -> f (s,args,mlts)
    | _ -> assert false 
  in f (s,args,mlts)

and extract_cst_app env mle mlt kn args = 
  let nb,t = record_constant_type kn in 
  let schema = nb, type_expand t in 
  let metas = List.map new_meta args in 
  let type_head = type_recomp (metas,mlt) in 
  let head = 
    let h = MLglob (ConstRef kn) in 
    put_magic (type_head, instantiation schema) h in
  let s = type_to_sign (snd schema) in 
  let ls = List.length s in 
  let la = List.length args in
  let mla = make_mlargs env mle s args metas in 
  if ls = 0 then head
  else if List.mem true s then 
    if la >= ls then MLapp (head, mla)
    else 
      let ls' = ls-la in
      let s' = list_lastn ls' s in
      let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
      anonym_or_dummy_lams (MLapp (head, mla)) s'
  else 
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
  let types, params_nb = extract_constructor cp in
  let types = List.map type_expand types in
  let nb_tvar = List.length (snd (extract_inductive ip)) in 
  let list_tvar = List.map (fun i -> Tvar i) (interval 1 nb_tvar) in 
  let type_cons = type_recomp (types, Tglob (IndRef ip, list_tvar)) in
  let type_cons = instantiation (nb_tvar, type_cons) in 
  let s = List.map ((<>) Tdummy) types in
  let ls = List.length s in 
  let la = List.length args in 
  assert (la <= ls + params_nb);
  let la' = max 0 (la - params_nb) in 
  let args' = list_lastn la' args in 
  let metas = List.map new_meta args' in 
  let type_head = type_recomp (metas, mlt) in
  let magic = needs_magic (type_cons, type_head) in 
  let head mla = 
    if is_singleton_constructor cp then 
      put_magic_if magic (List.hd mla) (* assert (List.length mla = 1) *)
    else put_magic_if magic (MLcons (ConstructRef cp, mla))
  in 
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

and extract_case env mle (ip,c,br_vect) mlt = 
  (* [ni_vect]: number of arguments without parameters in each branch *)
  (* [br_vect]: bodies of each branch (in functional form) *)
  let ni_vect = mis_constr_nargs ip in
  let br_size = Array.length br_vect in 
  assert (Array.length ni_vect = br_size); 
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
	let s = iterate (fun l -> false :: l) ni_vect.(0) [] in
	let mlt = iterate (fun t -> Tarr (Tdummy, t)) ni_vect.(0) mlt in 
	let e = extract_maybe_term env mle mlt br_vect.(0) in 
	snd (kill_all_prop_lams_eta e s)
      end 
    else 
      let types_vect = Array.make br_size [] 
      and sign_vect = Array.make br_size [] in 
      for i = 0 to br_size-1 do 
	let l = List.map type_expand (fst (extract_constructor (ip,i+1))) in 
	types_vect.(i) <- l; 
	sign_vect.(i) <- List.map ((<>) Tdummy) l; 
	assert (List.length sign_vect.(i) = ni_vect.(i))
      done;  
      let big_schema = 
	let nb_tvar = List.length (snd (extract_inductive ip)) in 
	let list_tvar = List.map (fun i -> Tvar i) (interval 1 nb_tvar) in 
	let l = array_map_to_list (fun l -> type_recomp (l,mlt)) types_vect in 
	nb_tvar, type_recomp (l, Tglob (IndRef ip, list_tvar))
      in 
      let type_list, type_head = type_decomp (instantiation big_schema) in
      let type_vect = Array.of_list type_list in 
      let a = extract_term env mle type_head c [] in 
      let extract_branch i = 	  
	let e = extract_maybe_term env mle type_vect.(i) br_vect.(i) in 
	let ids,e = kill_all_prop_lams_eta e sign_vect.(i) in
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

(*s From a constant to a ML declaration. *)

let rec decomp_n_lams_eta env typ c = 
  let rels = fst (splay_prod env none typ) in 
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

let extract_constant kn r = 
  let env = Global.env() in    
  let cb = Global.lookup_constant kn in
  let typ = cb.const_type in
  match cb.const_body with
    | None -> (* A logical axiom is risky, an informative one is fatal. *) 
        (match flag_of_type env typ with
           | (Info,_) -> axiom_error_message kn 
           | (Logic,TypeScheme) ->
	       axiom_warning_message kn; 
	       Dtype (r, [], Tdummy)
	   | (Logic,Default) -> 
	       axiom_warning_message kn; 
	       Dterm (r, MLdummy, Tdummy))
    | Some l_body ->
	(match flag_of_type env typ with
	   | (Logic, Default) -> Dterm (r, MLdummy, Tdummy)
	   | (Logic, TypeScheme) -> Dtype (r, [], Tdummy)
	   | (Info, Default) -> 
	       let body = Declarations.force l_body in
	       let rels,c = decomp_n_lams_eta env typ body in
	       let env' = push_rels_assum rels env in 
	       let ids = List.map (fun (n,_) -> id_of_name n) rels in 
	       reset_meta_count (); 
	       let t = snd (record_constant_type kn) in 
	       let l,t' = type_decomp (type_expand (var2var' t)) in 
	       let s = List.map ((<>) Tdummy) l in 
	       let mle = List.fold_left Mlenv.push_std_type Mlenv.empty l in 
	       let e = extract_term env' mle t' c [] in
	       if e = MLdummy then Dterm (r, MLdummy, Tdummy)
	       else Dterm (r, kill_prop_lams_eta s (ids,e), type_expunge t)
	   | (Info, TypeScheme) -> 
	       let body = Declarations.force l_body in
	       let s,vl = type_sign_vl env typ in 
               let db = db_from_sign s in 
               let t = extract_type_scheme env db body (List.length s) in 
               Dtype (r, vl, t))

let extract_constant_cache kn r = 
  try lookup_constant kn 
  with Not_found ->
    let d = extract_constant kn r
    in add_constant kn d; d

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
  | VarRef _ -> assert false

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


