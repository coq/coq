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

(* The type [flag] gives us information about an identifier
   coming from a Lambda or a Product:
   \begin{itemize}
   \item [Arity] denotes identifiers of type an arity of some sort [Set],
     [Prop] or [Type], that is $(x_1:X_1)\ldots(x_n:X_n)s$ with [s = Set],
     [Prop] or [Type] 
   \item [NotArity] denotes the other cases. It may be inexact after 
   instanciation. For example [(X:Type)X] is [NotArity] and may give [Set]
   after instanciation, which is rather [Arity]
   \item [Logic] denotes identifiers of type an arity of sort [Prop], 
     or of type of type [Prop]
   \item [Info] is the opposite. The same example [(X:Type)X] shows 
     that an [Info] term might in fact be [Logic] later on. 
   \end{itemize} *)

type info = Logic | Info

type arity = Arity | Flexible | Default

type flag = info * arity

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)
   
(* Convention: outmost lambda/product gives the head of the list, 
   and [true] means that the argument is to be kept. *)

type signature = bool list

(* The [indutive_extraction_result] is used to save the extraction of 
   an inductive type. It tells whether this inductive is informative 
   or not, and in the informative case, stores a signature and a type 
   variable list. *)

type inductive_extraction_result = 
  | Iml of signature * identifier list
  | Iprop

(* For an informative constructor, the [constructor_extraction_result] 
   contains the list of the types of its arguments, a signature, and 
   the number of parameters to discard. *)

type constructor_extraction_result = 
  | Cml of ml_type list * signature * int
  | Cprop

(*S Tables to keep the extraction results. *)

let inductive_table = 
  ref (Gmap.empty : (inductive, inductive_extraction_result) Gmap.t)
let add_inductive i e = inductive_table := Gmap.add i e !inductive_table
let lookup_inductive i = Gmap.find i !inductive_table

let constructor_table = 
  ref (Gmap.empty : (constructor, constructor_extraction_result) Gmap.t)
let add_constructor c e = constructor_table := Gmap.add c e !constructor_table
let lookup_constructor c = Gmap.find c !constructor_table

let constant_table = 
  ref (Gmap.empty : (kernel_name, ml_decl) Gmap.t)
let add_constant kn d = constant_table := Gmap.add kn d !constant_table
let lookup_constant kn = Gmap.find kn !constant_table

let signature_table = ref (Gmap.empty : (kernel_name, signature) Gmap.t)
let add_signature kn s = signature_table := Gmap.add kn s !signature_table
let lookup_signature kn = Gmap.find kn !signature_table 

(* Tables synchronization. *)

let freeze () =
  !inductive_table, !constructor_table, !constant_table, !signature_table

let unfreeze (it,cst,ct,st) =
  inductive_table := it; constructor_table := cst;
  constant_table := ct; signature_table := st

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

(*s [flag_of_type] transforms a type [t] into a [flag]. 
  Really important function. *)

let rec flag_of_type env t = 
  let t = whd_betadeltaiota env none t in 
  match kind_of_term t with
    | Prod (x,t,c) -> flag_of_type (push_rel (x,None,t) env) c
    | Sort (Prop Null) -> (Logic,Arity)
    | Sort _ -> (Info,Arity)
    | (Case _ | Fix _ | CoFix _) -> 
	if (sort_of env t) = InProp then (Logic,Flexible) else (Info,Default)
    | _ -> if (sort_of env t) = InProp then (Logic,Default) else (Info,Default)

(*s [is_default] and [is_info_arity] are particular cases of [flag_of_type]. *)

let is_default env t = (flag_of_type env t = (Info, Default))

let is_info_arity env t = (flag_of_type env t = (Info, Arity))

(*s [term_sign] gernerates a signature aimed at treating a term 
  application at the ML term level. *)

let rec term_sign env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	(is_default env t) :: (term_sign (push_rel_assum (n,t) env) d)
    | _ -> []

(*s [type_sign] gernerates a signature aimed at treating a term 
  application at the ML type level. *)
	  
let rec type_sign env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	(is_info_arity env t)::(type_sign (push_rel_assum (n,t) env) d)
    | _ -> []

(* There is also a variant producing at the same time a type var list. *)

let rec type_sign_vl env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	let s,vl = type_sign_vl (push_rel_assum (n,t) env) d in 
	if not (is_info_arity env t) then false::s, vl
	else true::s, (next_ident_away (id_of_name n) vl) :: vl
    | _ -> [],[]

(*s Function recording signatures of section paths. *)

let signature_of_kn kn = 
  try lookup_signature kn
  with Not_found -> 
    let env = Global.env () in 
    let s = term_sign env (constant_type env kn)
    in add_signature kn s; s

(*S Management of type variable contexts. *)

(*s From a signature toward a type variable context (db). *)

let db_from_sign s = 
  let rec f i = function 
    | [] -> [] 
    | true :: l -> i :: (f (i+1) l)
    | false :: l -> 0 :: (f i l)
  in f 1 (List.rev s)

(*s Create a type variable context from indications taken from 
  an inductive type (see just below). *) 

let db_from_ind dbmap params_nb length_sign = 
  let rec f i = 
    if i > params_nb then [] 
    else try 
      Intmap.find (i+length_sign) dbmap :: (f (i+1))
    with Not_found -> 0 :: (f (i+1))
  in f 1

(*s [parse_ind_args] is the function used for generating ad-hoc
  translation of de Bruijn indices for extraction of inductive type. *)

let parse_ind_args si args = 
  let rec parse i k = function 
    | [] -> Intmap.empty
    | false :: s -> parse (i-1) k s
    | true :: s -> 
      (match kind_of_term args.(i) with 
	 | Rel j -> Intmap.add j k (parse (i-1) (k+1) s)
	 | _ -> parse (i-1) (k+1) s)
  in parse ((Array.length args)-1) 1 (List.rev si) 

(*S Extraction of a type. *)

(*s [extract_type env db c args] is used to produce an ML type from the 
   coq term [(c args)], which is supposed to be a Coq type. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

let rec extract_type env db c args = 
  match kind_of_term (whd_betaiotazeta c) with
    | Lambda (_,_,d) -> 
	(match args with 
	   | [] -> assert false (* otherwise the lambda would be reductible. *)
	   | a :: args -> extract_type env db (subst1 a d) args)
    | Prod (n,t,d) ->
	let mld = extract_type (push_rel_assum (n,t) env) (0::db) d [] in 
	if mld = Tdummy then Tdummy 
	else if not (is_default env t) then Tarr (Tdummy, mld)
	else Tarr (extract_type env db t [], mld)
    | App (d, args') ->
	(* We just accumulate the arguments. *)
	extract_type env db d (Array.to_list args' @ args)
    | Rel n -> 
	(match lookup_rel n env with
	   | (_,Some t,_) -> 
	       extract_type env db (lift n t) args
	   | _ -> 
	       let n' = List.nth db (n-1) in 
	       if n' = 0 then Tunknown else Tvar n')
    | Const kn ->
	let t = constant_type env kn in 
	(match flag_of_type env t with 
	   | (Info,Arity) -> 
	       extract_type_app env db (ConstRef kn, type_sign env t) args
	   | (Info,_) -> Tunknown
	   | (Logic,_) -> Tdummy)
    | Ind kni ->
	(match extract_inductive kni with 
	   | Iml (si,_) -> extract_type_app env db (IndRef kni,si) args
	   | Iprop -> Tdummy)
    | Sort _ -> Tdummy 
    | Case _ | Fix _ | CoFix _ -> Tunknown
    | Var _ -> section_message ()
    | _ -> assert false

(*s Auxiliary function dealing with type application. 
  Precondition: [r] is of type an arity represented by the signature [s], 
  and is completely applied: [List.length args = List.length s]. *)
		  
and extract_type_app env db (r,s) args =
  let ml_args = 
    List.fold_right 
      (fun (b,c) a -> if b then 
	 let p = List.length (fst (splay_prod env none (type_of env c))) in
	 let db = iterate (fun l -> 0 :: l) p db in
	 (extract_type_arity env db c p) :: a
       else a)
      (List.combine s args) []
  in Tglob (r,  ml_args)

(*s [extract_type_arity env db c p] works on a Coq term [c] whose 
  type is an arity. It means that [c] is not a Coq type, but will 
  be when applied to sufficiently many arguments ([p] in fact).  
  This function decomposes p lambdas, with eta-expansion if needed. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

and extract_type_arity env db c p = 
  if p=0 then extract_type env db c [] 
  else 
    let c = whd_betaiotazeta c in 
    match kind_of_term c with 
      | Lambda (n,t,d) -> 
	  extract_type_arity (push_rel_assum (n,t) env) db d (p-1)
      | _ ->  
	  let rels = fst (splay_prod env none (type_of env c)) in
	  let env = push_rels_assum rels env in  
	  let eta_args = List.rev_map mkRel (interval 1 p) in 
	  extract_type env db (lift p c) eta_args

(*s [extract_type_ind] extracts the type of an inductive 
  constructor toward the corresponding list of ML types. *)

(* [p] is the number of product in [c] and [db] is a context for 
  translating Coq [Rel] into ML type [Tvar] and [dbmap] is a translation 
  map (produced by a call to [parse_in_args]). *)

and extract_type_ind env db dbmap c p = 
  match kind_of_term (whd_betadeltaiota env none c) with 
    | Prod (n,t,d) -> 
	let env' = push_rel_assum (n,t) env in
	let db' = (try Intmap.find p dbmap with Not_found -> 0) :: db in
	let l = extract_type_ind env' db' dbmap d (p-1) in 
	if is_default env t then
	  let mlt = extract_type env db t [] in 
	  if mlt = Tdummy then l else mlt :: l 
	else l 
    | _ -> [] 

(*S Extraction of an inductive. *)
    
and extract_inductive ((sp,_) as i) =
  extract_mib sp;
  lookup_inductive i
			     
and extract_constructor (((sp,_),_) as c) =
  extract_mib sp;
  lookup_constructor c

and extract_mib kn =
  let ind = (kn,0) in
  if not (Gmap.mem ind !inductive_table) then begin
    let (mib,mip) = Global.lookup_inductive ind in
    let env = Global.env () in 
    (* Everything concerning parameters. *)
    (* We do that first, since they are common to all the [mib]. *)
    let params_nb = mip.mind_nparams in
    let params_env = push_rel_context mip.mind_params_ctxt env in
    (* First pass: we store inductive signatures together with *)
    (* their type var list. *)
    for i = 0 to mib.mind_ntypes - 1 do
      let ip = (kn,i) in 
      let (mib,mip) = Global.lookup_inductive ip in 
      if mip.mind_sort = (Prop Null) then 
	add_inductive ip Iprop
      else
	let arity = mip.mind_nf_arity in
	let s,vl = type_sign_vl env arity in 
	add_inductive ip (Iml (s,vl))
    done;
    (* Second pass: we extract constructors *)
    for i = 0 to mib.mind_ntypes - 1 do
      let ip = (kn,i) in
      let (mib,mip) = Global.lookup_inductive ip in
      match lookup_inductive ip with 
	| Iprop -> 
	    for j = 1 to Array.length mip.mind_consnames do
	      add_constructor (ip,j) Cprop
	    done
	| Iml (si,_) ->  
	    for j = 1 to Array.length mip.mind_consnames do 
	      let cp = (ip,j) in 
	      let t = type_of_constructor env cp in
	      let t = snd (decompose_prod_n params_nb t) in
	      let s = term_sign params_env t in
	      let n = List.length s in 
	      let args = match find_conclusion params_env none t with
		| App (f,args) -> args (* [kind_of_term f = Ind ip] *)
		| _ -> [||]
	      in 
	      let dbmap = parse_ind_args si args in 
	      let db = db_from_ind dbmap params_nb n in 
	      let l = extract_type_ind params_env db dbmap t n in	      
	      add_constructor cp (Cml (l,s,params_nb))
	    done
    done
  end	      

(*s Looking for informative singleton case, i.e. an inductive with one 
   constructor which has one informative argument. This dummy case will 
   be simplified. *)
 
let is_singleton_inductive ind = 
  let (mib,mip) = Global.lookup_inductive ind in 
  mib.mind_finite &&
  (mib.mind_ntypes = 1) &&
  (Array.length mip.mind_consnames = 1) && 
  match extract_constructor (ind,1) with 
    | Cml ([mlt],_,_)-> not (type_mem_kn (fst ind) mlt)
    | _ -> false
          
let is_singleton_constructor ((kn,i),_) = 
  is_singleton_inductive (kn,i) 

(*S Modification of the signature of terms. *)

(* We sometimes want to suppress [prop] and [arity] in the signature 
   of a term. It is so: 
   \begin{itemize}
   \item after a case, in [extract_case]
   \item for the toplevel definition of a function, in [suppress_prop_eta] 
   below. By the way we do some eta-expansion if needed using 
   [expansion_prop_eta].
   \end{itemize}
   To ensure correction of execution, we then need to reintroduce 
   [prop] and [arity] lambdas around constructors and functions occurrences. 
   This is done by [abstract_constructor] and [abstract_constant]. *)

let expansion_prop_eta s (ids,c) =
  let rec abs ids rels i = function
    | [] -> 
	let a = List.rev_map (function MLrel x -> MLrel (i-x) | a -> a) rels
	in ids, MLapp (ml_lift (i-1) c, a) 
    | true :: l -> abs (anonymous :: ids) (MLrel i :: rels) (i+1) l 
    | false :: l -> abs (dummy_name :: ids) (MLdummy' :: rels) (i+1) l
  in abs ids [] 1 s

let kill_all_prop_lams_eta e s = 
  let m = List.length s in 
  let n = nb_lams e in 
  let p = if m <= n then collect_n_lams m e 
  else expansion_prop_eta (snd (list_chop n s)) (collect_lams e) in 
  kill_some_lams (List.rev s) p

let kill_prop_lams_eta e s =
  if s = [] then e 
  else 
    let ids,e = kill_all_prop_lams_eta e s in 
    if ids = [] then MLlam (dummy_name, ml_lift 1 e)
    else named_lams ids e

(*s Auxiliary functions for [apply_constant] and [apply_constructor]. *)

let rec anonym_or_dummy_lams c = function 
  | [] -> c 
  | true :: l -> MLlam(anonymous, anonym_or_dummy_lams c l)
  | false :: l -> MLlam(dummy_name, anonym_or_dummy_lams c l)
    
let rec extract_eta_args n = function 
  | [] -> [] 
  | true :: s -> (MLrel n) :: (extract_eta_args (n-1) s) 
  | false :: s -> extract_eta_args (n-1) s

let rec extract_real_args env args s = 
  let a = Array.length args in 
  let rec f i l = function 
    | [] -> l 
    | true :: s -> f (i-1) ((extract_constr_to_term env args.(i)) :: l) s
    | false :: s -> f (i-1) l s
  in f (a-1) [] (List.rev s)

(*s Abstraction of an constant. *)

and apply_constant env kn args = 
  let head = MLglob (ConstRef kn) in 
  let s = signature_of_kn kn in 
  let ls = List.length s in 
  let la = Array.length args in 
  if ls = 0 then begin
    (* if the type of this constant isn't a product, it cannot be applied. *)
    assert (la = 0); 
    head
  end else if List.mem true s then 
    if la = ls then 
      MLapp (head, extract_real_args env args s)
    else if la > ls then 
      let s' = s @ (iterate (fun l -> true :: l) (la-ls) []) in
      MLapp (head, extract_real_args env args s')
    else (* [la < ls] *)
      let n1 = la 
      and n2 = ls-la in 
      let s1,s2 = list_chop n1 s in 
      let mla1 = List.map (ml_lift n2) (extract_real_args env args s1) in
      let mla2 = extract_eta_args n2 s2 in 
      anonym_or_dummy_lams (MLapp (head, mla1 @ mla2)) s2
  else 
    if la >= ls then 
      let s' = iterate (fun l -> true :: l) (la-ls) [] in 
      MLapp(head, MLdummy' :: (extract_real_args env args s'))
    else (* [la < ls] *)
      dummy_lams head (ls-la-1)

(*s Application of an inductive constructor.
   \begin{itemize}
   \item In ML, contructor arguments are uncurryfied. 
   \item We managed to suppress logical parts inside inductive definitions,
   but they must appears outside (for partial applications for instance)
   \item We also suppressed all Coq parameters to the inductives, since
   they are fixed, and thus are not used for the computation.
   \end{itemize} *)

and apply_constructor env cp args =
  let head mla = 
    if is_singleton_constructor cp then 
      List.hd mla (* assert (List.length mla = 1) *)
    else MLcons (ConstructRef cp, mla)
  in 
  match extract_constructor cp with 
    | Cprop -> assert false 
    | Cml (_,s,params_nb) -> 
	let ls = List.length s in 
	let la = Array.length args in 
	assert (la <= ls + params_nb);
	if la = ls + params_nb then 
	  head (extract_real_args env args s)
	else if la >= params_nb then 
	  let n1 = la - params_nb in 
	  let n2 = ls - n1 in 
	  let s1,s2 = list_chop n1 s in 
	  let mla1 = List.map (ml_lift n2) (extract_real_args env args s1) in
	  let mla2 = extract_eta_args n2 s2 in 
	  anonym_or_dummy_lams (head (mla1 @ mla2)) s2
	else (* [la < params_nb] *)
	  let head' = head (extract_eta_args ls s) in 
	  dummy_lams (anonym_or_dummy_lams head' s) (params_nb - la)
	    
(*S Extraction of a term. *)

(* Precondition: [c] has a type which is not an arity, and is informative. 
   This is normaly checked in [extract_constr]. *)

and extract_term env c = 
  match kind_of_term c with
    | Lambda (n, t, d) ->
	let id = id_of_name n in 
	(* If [d] was of type an arity, [c] too would be so *)
	let d' = extract_term (push_rel_assum (Name id,t) env) d in
	if is_default env t then MLlam (id, d')
	else MLlam (dummy_name, d')
    | LetIn (n, c1, t1, c2) ->
	let id = id_of_name n in 
	(* If [c2] was of type an arity, [c] too would be so *)
	let c2' = extract_term (push_rel (Name id,Some c1,t1) env) c2 in
	if is_default env t1 then MLletin (id, extract_term env c1, c2')
	else ml_pop c2'
    | Rel n ->
	MLrel n
    | App (f,a) ->
	(match kind_of_term (strip_outer_cast f) with 
	   | App _ -> assert false 
      	   | Const kn -> apply_constant env kn a 
	   | Construct cp -> apply_constructor env cp a
	   | _ -> 
	       let mlargs = 
		 Array.fold_right 
		   (fun a l -> (extract_constr_to_term env a) :: l) a []
	       in MLapp (extract_term env f, mlargs))
    | Const kn ->
	apply_constant env kn [||]
    | Construct cp ->
	apply_constructor env cp [||]
    | Case ({ci_ind=ip},_,c,br) ->
	extract_case env ip c br
    | Fix ((_,i),recd) -> 
	extract_fix env i recd
    | CoFix (i,recd) -> 
	extract_fix env i recd  
    | Cast (c, _) ->
	extract_term env c
    | Ind _ | Prod _ | Sort _ | Meta _ | Evar _ -> assert false 
    | Var _ -> section_message ()


(*s Extraction of a case. *)

and extract_case env ip c br = 
  let ni = mis_constr_nargs ip in
  (* [ni]: number of arguments without parameters in each branch *)
  (* [br]: bodies of each branch (in functional form) *)
  let extract_branch j b = 	  
    (* Some pathological cases need an [extract_constr] here rather *)
    (* than an [extract_term]. See exemples in [test_extraction.v] *)
    let e = extract_constr_to_term env b in 
    let cp = (ip,succ j) in
    let s = match extract_constructor cp with 
      | Cml (_,s,_) -> s 
      | _ -> assert false
    in assert (List.length s = ni.(j));
    let ids,e = kill_all_prop_lams_eta e s in
    (ConstructRef cp, List.rev ids, e)
  in
  if br = [||] then MLexn "absurd case"
  else 
    (* [c] has an inductive type, not an arity type. *)
    let t = type_of env c in 
    (* The only non-informative case: [c] is of sort [Prop] *)
    if (sort_of env t) = InProp then 
      begin 
	(* Logical singleton case: *)
	(* [match c with C i j k -> t] becomes [t'] *)
	assert (Array.length br = 1);
	let e = extract_constr_to_term env br.(0) in 
	let s = iterate (fun l -> false :: l) ni.(0) [] in
	snd (kill_all_prop_lams_eta e s)
      end 
    else 
      let a = extract_term env c in 
      if is_singleton_inductive ip then 
	begin 
	  (* Informative singleton case: *)
	  (* [match c with C i -> t] becomes [let i = c' in t'] *)
	  assert (Array.length br = 1);
	  let (_,ids,e') = extract_branch 0 br.(0) in
	  assert (List.length ids = 1);
	  MLletin (List.hd ids,a,e')
	end 
      else 
	(* Standard case: we apply [extract_branch]. *)
	MLcase (a, Array.mapi extract_branch br)
  
(*s Extraction of a (co)-fixpoint. *)

and extract_fix env i (fi,ti,ci as recd) = 
  let n = Array.length ti in
  let ti' = Array.mapi lift ti in 
  let lb = Array.to_list (array_map2 (fun a b -> (a,b)) fi ti') in
  let env' = push_rels_assum (List.rev lb) env in
  let extract_fix_body c t = 
    extract_constr_to_term_wt env' c (lift n t) in
  let ei = array_map2 extract_fix_body ci ti in
  MLfix (i, Array.map id_of_name fi, ei)

(*s Extraction of a constr seen as a term. *)

and extract_constr_to_term env c =
  extract_constr_to_term_wt env c (type_of env c)

(* Same, but With Type (wt). *)

and extract_constr_to_term_wt env c t = 
  match flag_of_type env t with 
    | (Info, Default) -> extract_term env c
    | (Logic, Flexible) -> MLdummy'
    | _ -> MLdummy'
(*i dummy_lams MLdummy (List.length (fst (splay_prod env none t))) i*) 

(*S ML declarations. *)

(*s From a constant to a ML declaration. *)

let extract_constant kn r = 
  let env = Global.env() in    
  let cb = Global.lookup_constant kn in
  let typ = cb.const_type in
  match cb.const_body with
    | None -> (* A logical axiom is risky, an informative one is fatal. *) 
        (match flag_of_type env typ with
           | (Info,_) -> axiom_error_message kn 
           | (Logic,Arity) -> axiom_warning_message kn; 
	       DdummyType r
	   | (Logic,_) -> axiom_warning_message kn;
	       Dterm (r, MLdummy'))
    | Some l_body ->
	(match flag_of_type env typ with
	   | (Logic, Arity) -> DdummyType r
	   | (Info, Arity) -> 
	       let s,vl = type_sign_vl env typ in 
	       let db = db_from_sign s in 
	       let body = Declarations.force l_body in
	       let t = extract_type_arity env db body (List.length s)
	       in Dtype (r, vl, t)
	   | (Logic, _) -> Dterm (r, MLdummy')
	   | (Info, _) -> 
	       let body = Declarations.force l_body in
	       let a = extract_term env body in
	       if a <> MLdummy' then 
		 Dterm (r, kill_prop_lams_eta a (signature_of_kn kn))
	       else Dterm (r, a))
		   
let extract_constant_cache kn r = 
  try lookup_constant kn 
  with Not_found ->
    let d = extract_constant kn r
    in add_constant kn d; d

(*s From an inductive to a ML declaration. *)
      
let extract_inductive_declaration kn =
  extract_mib kn;
  let ip = (kn,0) in 
  if is_singleton_inductive ip then
    let t = match lookup_constructor (ip,1) with 
      | Cml ([t],_,_)-> t
      | _ -> assert false
    in
    let vl = match lookup_inductive ip with 
       | Iml (_,vl) -> vl
       | _ -> assert false
     in 
    Dtype (IndRef ip,vl,t)
  else
    let mib = Global.lookup_mind kn in
    let one_ind ip n = 
      iterate_for (-n) (-1)
	(fun j l -> 
	   let cp = (ip,-j) in 
	   match lookup_constructor cp with 
	     | Cml (t,_,_) -> (ConstructRef cp, t)::l
	     | _ -> assert false) []
    in
    let l = 
      iterate_for (1 - mib.mind_ntypes) 0
	(fun i acc -> 
	   let ip = (kn,-i) in
	   let nc = Array.length mib.mind_packets.(-i).mind_consnames in 
	   match lookup_inductive ip with
	     | Iprop -> acc
	     | Iml (_,vl) -> (vl, IndRef ip, one_ind ip nc) :: acc)
	[] 
    in
    Dind (l, not mib.mind_finite)

(*s From a global reference to a ML declaration. *)

let extract_declaration r = match r with
  | ConstRef kn -> extract_constant kn r
  | IndRef (kn,_) -> extract_inductive_declaration kn
  | ConstructRef ((kn,_),_) -> extract_inductive_declaration kn
  | VarRef _ -> assert false

(*s Check if a global reference corresponds to a logical inductive. *)

let decl_is_logical_ind = function 
  | IndRef ip -> extract_inductive ip = Iprop 
  | ConstructRef cp -> extract_constructor cp  = Cprop
  | _ -> false

(*s Check if a global reference corresponds to the constructor of 
  a singleton inductive. *)

let decl_is_singleton = function 
  | ConstructRef cp -> is_singleton_constructor cp 
  | _ -> false 

