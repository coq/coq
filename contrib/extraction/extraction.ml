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

type arity = Arity | NotArity

type flag = info * arity

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)
   
(* Convention: outmost lambda/product gives the head of the list, 
   and [true] means that the argument is to be kept. *)

type signature = bool list

(* The [extraction_result] is the result of the [extract_constr]
   function that extracts any CIC object. It is either a ML type or 
   a ML object. An ML type contains also a signature (saying how to 
   translate its coq arity into a ML arity) and a type variable list. *)

type extraction_result =
  | Emltype of ml_type * signature * identifier list
  | Emlterm of ml_ast

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
  ref (Gmap.empty : (section_path, extraction_result) Gmap.t)
let add_constant sp e = constant_table := Gmap.add sp e !constant_table
let lookup_constant sp = Gmap.find sp !constant_table

let signature_table = ref (Gmap.empty : (section_path, signature) Gmap.t)
let add_signature sp s = signature_table := Gmap.add sp s !signature_table
let lookup_signature sp = Gmap.find sp !signature_table 

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

(*S Error messages. *)

let axiom_message sp =
  errorlabstrm "axiom_message"
    (str "You must specify an extraction for axiom" ++ spc () ++ 
       pr_sp sp ++ spc () ++ str "first.")

let section_message () = 
  errorlabstrm "section_message"
    (str "You can't extract within a section. Close it and try again.")

(*S Generation of flags and signatures. *)

let none = Evd.empty

let type_of env c = Retyping.get_type_of env none (strip_outer_cast c)

let sort_of env c = Retyping.get_sort_family_of env none (strip_outer_cast c)

let is_axiom sp = (Global.lookup_constant sp).const_body = None

(*s [flag_of_type] transforms a type [t] into a [flag]. 
  Really important function. *)

let flag_of_type env t = match find_conclusion env t with
  | Sort (Prop Null) -> (Logic,Arity)
  | Sort _ -> (Info,Arity)
  | _ -> if (sort_of env t) = InProp then (Logic,NotArity)
    else (Info,NotArity)

(*s [is_default] is a particular case of the last function. *)

let is_default env t = 
  not (is_arity env none t) && (sort_of env t) <> InProp

(*s [term_sign] gernerates a signature aimed at treating a term 
  application at the ML term level. *)

let rec term_sign env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	(is_default env t) :: (term_sign (push_rel_assum (n,t) env) d)
    | _ -> []

(*s [type_sign] gernerates a signature aimed at treating a term 
  application at the ML type level. It also produce a type var list. *)

let rec type_sign env c = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) -> 
	let s,vl = type_sign (push_rel_assum (n,t) env) d in 
	let b = flag_of_type env t = (Info,Arity) in
	let vl = if not b then vl
	else (next_ident_away (id_of_name n) vl) :: vl 
	in b::s, vl
    | Sort _ -> [],[]
    | _ -> assert false

(*s [app_sign] is used to generate a long enough signature.
   Precondition: the head [f] is [Info].
   Postcondition: the output signature is at least as long as the arguments. *)
    
let rec app_sign env f t a =
  let s = term_sign env t in
  let na = Array.length a in	
  let ns = List.length s in 
  if ns >= na then s
  else 
    (* This case can really occur. Cf [test_extraction.v]. *)
    let f' = mkApp (f, Array.sub a 0 ns) in 
    let a' = Array.sub a ns (na-ns) in 
    s @ app_sign env f' (type_of env f') a'
  
(*s Function recording signatures of section paths. *)

let signature_of_sp sp typ = 
  try lookup_signature sp
  with Not_found -> 
    let s = term_sign (Global.env()) typ in 
    add_signature sp s; s

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
    | false :: l -> abs (dummy_name :: ids) (MLdummy :: rels) (i+1) l
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

(*s Auxiliary function for [abstract_constant] and [abstract_constructor]. *)

let prop_abstract f  = 
  let rec abs rels i = function 
    | [] -> f (List.rev_map (fun x -> MLrel (i-x)) rels)
    | true :: l -> MLlam (anonymous, abs (i :: rels) (succ i) l)
    | false :: l -> MLlam (dummy_name, abs rels (succ i) l)
  in abs [] 1  

(*s Abstraction of an constant. *)

let abstract_constant sp s = 
  if List.mem false s then  
    let f a = 
      if List.mem true s then MLapp (MLglob (ConstRef sp), a)
      else MLapp (MLglob (ConstRef sp), [MLdummy])
    in prop_abstract f s
  else MLglob (ConstRef sp) 

(*S Management of type variable contexts. *)

(*s From a signature toward a type variable context (ctx). *)

let ctx_from_sign s = 
  let rec make i = function 
    | [] -> [] 
    | true :: l -> i :: (make (i+1) l)
    | false :: l -> 0 :: (make i l)
  in make 1 (List.rev s)

(*s Create a type variable context from indications taken from 
  an inductive type (see just below). *) 

let ctx_from_ind rels n d = 
  let rec make i = 
    if i > n then [] 
    else try 
      (Intmap.find (i+d) rels) :: (make (i+1))
    with Not_found -> 0 :: (make (i+1))
  in make 1

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

(*s [extract_type env c args ctx] is used to produce an ML type from the 
   coq term [(c args)], which is supposed to be a Coq type on an informative 
   sort. *)

(* [ctx] is a context for translating Coq [Rel] into ML type [Tvar]. *)

let rec extract_type env c args ctx = 
  match kind_of_term (whd_betaiotazeta c) with
    | Lambda (_,_,d) -> 
	(match args with 
	   | [] -> assert false (* This lambda must be reductible. *)
	   | a :: args -> extract_type env (subst1 a d) args ctx)
    | Sort _ ->
	Tdummy 
    | Prod (n,t,d) ->
	let mld = extract_type (push_rel_assum (n,t) env) d [] (0::ctx) in 
	if mld = Tdummy then Tdummy 
	else if not (is_default env t) then Tarr (Tdummy, mld)
	else Tarr (extract_type env t [] ctx, mld)
    | App (d, args') ->
	(* We just accumulate the arguments. *)
	extract_type env d (Array.to_list args' @ args) ctx
    | Rel n -> 
	(match lookup_rel n env with
	   | (_,Some t,_) -> 
	       extract_type env (lift n t) args ctx
	   | _ -> 
	       let n' = List.nth ctx (n-1) in 
	       if n' = 0 then Tunknown else Tvar n')
    | Const sp when is_ml_extraction (ConstRef sp) ->
	Tglob (ConstRef sp)
    | Const sp when is_axiom sp -> 
	Tunknown
    | Const sp ->
	let t = constant_type env sp in 
	if is_arity env none t then
	  match extract_constant sp with 
	    | Emltype (mlt, sc, _) -> 
		if mlt = Tdummy then Tdummy
		else extract_type_app env (ConstRef sp,sc) args ctx
	    | Emlterm _ -> assert false
	else 
	  (* We can't keep as ML type abbreviation a Coq constant *)
	  (* which type is not an arity: we reduce this constant. *)
	  let cvalue = constant_value env sp in
	  extract_type env (applist (cvalue, args)) [] ctx
    | Ind spi ->
	(match extract_inductive spi with 
	   | Iml (si,vli) -> extract_type_app env (IndRef spi,si) args ctx
	   | Iprop -> assert false (* Cf. initial tests *))
    | Case _ | Fix _ | CoFix _ -> Tunknown
    | Var _ -> section_message ()
    | _ -> assert false

(*s Auxiliary function dealing with type application. 
  Precondition: [r] is of type an arity represented by the signature [s], 
  and is completely applied: [List.length args = List.length s]. *)
		  
and extract_type_app env (r,s) args ctx =
  let ml_args = 
    List.fold_right 
      (fun (b,c) a -> if not b then a 
       else 
	 let p = List.length (fst (splay_prod env none (type_of env c))) in
	 let ctx = iterate (fun l -> 0 :: l) p ctx in
	 (extract_type_arity env c ctx p) :: a)
      (List.combine s args) []
  in Tapp ((Tglob r) :: ml_args)

(*s [extract_type_arity env c ctx p] works on a Coq term [c] whose type 
  is an informative arity. It means that [c] is not a Coq type, but will 
  be when applied to sufficiently many arguments ([p] in fact).  
  This function decomposes p lambdas, with eta-expansion if needed. *)

(* [ctx] is a context for translating Coq [Rel] into ML type [Tvar]. *)

and extract_type_arity env c ctx p = 
  if p=0 then extract_type env c [] ctx 
  else 
    let c = whd_betaiotazeta c in 
    match kind_of_term c with 
      | Lambda (n,t,d) -> 
	  extract_type_arity (push_rel_assum (n,t) env) d ctx (p-1)
      | _ ->  
	  let rels = fst (splay_prod env none (type_of env c)) in
	  let env = push_rels_assum rels env in  
	  let eta_args = List.rev_map mkRel (interval 1 p) in 
	  extract_type env (lift p c) eta_args ctx

(*s [extract_type_ind] extracts the type of an informative inductive 
  constructor toward the corresponding list of ML types. *)

(* [p] is the number of product in [c] and [ctx] is a context for 
  translating Coq [Rel] into ML type [Tvar] and [db] is a translation 
  map (produced by a call to [parse_in_args]). *)

and extract_type_ind env c ctx db p = 
  match kind_of_term (whd_betadeltaiota env none c) with 
    | Prod (n,t,d) -> 
	let env' = push_rel_assum (n,t) env in
	let ctx' = (try Intmap.find p db with Not_found -> 0) :: ctx in
	let l = extract_type_ind env' d ctx' db (p-1) in 
	if is_default env t then
	  let mlt = extract_type env t [] ctx in 
	  if mlt = Tdummy then l else mlt :: l 
	else l 
    | _ -> [] 

(*S Extraction of a term. *)

(* Precondition: [c] has a type which is not an arity, and is informative. 
   This is normaly checked in [extract_constr]. *)

and extract_term env c = 
  extract_term_wt env c (type_of env c)

(* Same, but With Type (wt). *)

and extract_term_wt env c t = 
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
	 if is_default env t1 then 
	   let c1' = extract_term_wt env c1 t1 in 
	   MLletin (id,c1',c2')
	 else MLletin (dummy_name, MLdummy, c2')
     | Rel n ->
	 MLrel n
     | Const sp ->
	 abstract_constant sp (signature_of_sp sp t)
     | App (f,a) ->
      	 extract_app env f a 
     | Construct cp ->
	 abstract_constructor cp (signature_of_constructor cp)
     | Case ({ci_ind=ip},_,c,br) ->
	 extract_case env ip c br
     | Fix ((_,i),recd) -> 
	 extract_fix env i recd
     | CoFix (i,recd) -> 
	 extract_fix env i recd  
     | Cast (c, _) ->
	 extract_term_wt env c t
     | Ind _ | Prod _ | Sort _ | Meta _ | Evar _ -> assert false 
     | Var _ -> section_message ()

(*s Abstraction of an inductive constructor.
   \begin{itemize}
   \item In ML, contructor arguments are uncurryfied. 
   \item We managed to suppress logical parts inside inductive definitions,
   but they must appears outside (for partial applications for instance)
   \item We also suppressed all Coq parameters to the inductives, since
   they are fixed, and thus are not used for the computation.
   \end{itemize}

   The following code deals with those 3 questions: from constructor [C], it 
   produces: 
   [fun ]$p_1 \ldots p_n ~ x_1 \ldots x_n $[-> C(]$x_{i_1},\ldots, x_{i_k}$[)].
   This ML term will be reduced later on when applied, see [mlutil.ml].\\

   In the special case of a informative singleton inductive, [C] is identity. *)

and abstract_constructor cp (s,params_nb) =
  let f a = if is_singleton_constructor cp then List.hd a
  else MLcons (ConstructRef cp, a)
  in dummy_lams (ml_lift params_nb (prop_abstract f s)) params_nb

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
    let s = fst (signature_of_constructor cp) in
    assert (List.length s = ni.(j));
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
      let a = extract_term_wt env c t in 
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

(*s Extraction of an term application.
  Precondition: the head [f] is [Info]. *)

and extract_app env f args =
  let tyf = type_of env f in
  let nargs = Array.length args in
  let sf = app_sign env f tyf args in  
  assert (List.length sf >= nargs); 
  (* Cf. postcondition of [signature_of_application]. *)
  let mlargs = 
    List.map 
      (* We can't trust tag [default], so we use [extract_constr]. *)
      (fun (b,a) -> if b then extract_constr_to_term env a else MLdummy)
      (List.combine (list_firstn nargs sf) (Array.to_list args))
  in
  (* [f : arity] implies [(f args):arity], that can't be *)
  MLapp (extract_term_wt env f tyf, mlargs)

(*s Extraction of a constr seen as a term. *)

and extract_constr_to_term env c =
  extract_constr_to_term_wt env c (type_of env c)

(* Same, but With Type (wt). *)

and extract_constr_to_term_wt env c t = 
  if is_default env t then extract_term_wt env c t 
  else dummy_lams MLdummy (List.length (fst (splay_prod env none t)))

(*S Extraction of a constr. *)

and extract_constr env c = 
  extract_constr_wt env c (type_of env c)

(* Same, but With Type (wt). *)

and extract_constr_wt env c t =
  match flag_of_type env t with
    | (Logic, Arity) -> Emltype (Tdummy, [], [])
    | (Info, Arity) -> 
	let s,vl = type_sign env t in 
	let ctx = ctx_from_sign s in 
	let mlt = extract_type_arity env c ctx (List.length s) in 
	Emltype (mlt, s, vl)
    | (Logic, NotArity) -> Emlterm MLdummy
    | (Info, NotArity) -> Emlterm (extract_term_wt env c t)
	  
(*S Extraction of a constant. *)
		
and extract_constant sp =
  try lookup_constant sp 
  with Not_found ->
    let env = Global.env() in    
    let cb = Global.lookup_constant sp in
    let typ = cb.const_type in
    match cb.const_body with
      | None ->
          (match flag_of_type env typ with
             | (Info,_) -> axiom_message sp (* We really need some code here *)
             | (Logic,NotArity) -> Emlterm MLdummy (* Axiom? I don't mind! *)
             | (Logic,Arity) -> Emltype (Tdummy,[],[]))  (* Idem *)
      | Some body ->
	  let e = match extract_constr_wt env body typ with 
	    | Emlterm MLdummy as e -> e
	    | Emlterm a -> 
		Emlterm (kill_prop_lams_eta a (signature_of_sp sp typ))
	    | e -> e 
	  in add_constant sp e; e

(*S Extraction of an inductive. *)
    
and extract_inductive ((sp,_) as i) =
  extract_mib sp;
  lookup_inductive i
			     
and extract_constructor (((sp,_),_) as c) =
  extract_mib sp;
  lookup_constructor c

and signature_of_constructor cp = match extract_constructor cp with
  | Cprop -> assert false
  | Cml (_,s,n) -> (s,n)

(*s Looking for informative singleton case, i.e. an inductive with one 
   constructor which has one informative argument. This dummy case will 
   be simplified. *)
 
and is_singleton_inductive ind = 
  let (mib,mip) = Global.lookup_inductive ind in 
  mib.mind_finite &&
  (mib.mind_ntypes = 1) &&
  (Array.length mip.mind_consnames = 1) && 
  match extract_constructor (ind,1) with 
    | Cml ([mlt],_,_)-> not (type_mem_sp (fst ind) mlt)
    | _ -> false
          
and is_singleton_constructor ((sp,i),_) = 
  is_singleton_inductive (sp,i) 

and extract_mib sp =
  let ind = (sp,0) in
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
      let ip = (sp,i) in 
      let (mib,mip) = Global.lookup_inductive ip in 
      if mip.mind_sort = (Prop Null) then 
	add_inductive ip Iprop
      else
	let arity = mip.mind_nf_arity in
	let s,vl = type_sign env arity in 
	add_inductive ip (Iml (s,vl))
    done;
    (* Second pass: we extract constructors *)
    for i = 0 to mib.mind_ntypes - 1 do
      let ip = (sp,i) in
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
	      let db,ctx = 
		if si=[] then Intmap.empty,[]
		else match find_conclusion params_env t with 
		  | App (f, args) -> 
		      (*i assert (kind_of_term f = Ind ip); i*)
		      let db = parse_ind_args si args in 
		      db, ctx_from_ind db params_nb n 
		  | _ -> assert false 
	      in 
	      let l = extract_type_ind params_env t ctx db n in	      
	      add_constructor cp (Cml (l,s,params_nb))
	    done
    done
  end	      

and extract_inductive_declaration sp =
  extract_mib sp;
  let ip = (sp,0) in 
  if is_singleton_inductive ip then
    let t = match lookup_constructor (ip,1) with 
      | Cml ([t],_,_)-> t
      | _ -> assert false
    in
    let vl = match lookup_inductive ip with 
       | Iml (_,vl) -> vl
       | _ -> assert false
     in 
    Dabbrev (IndRef ip,vl,t)
  else
    let mib = Global.lookup_mind sp in
    let one_ind ip n = 
      iterate_for (-n) (-1)
	(fun j l -> 
	   let cp = (ip,-j) in 
	   match lookup_constructor cp with 
	     | Cprop -> assert false
	     | Cml (t,_,_) -> (ConstructRef cp, t)::l) []
    in
    let l = 
      iterate_for (1 - mib.mind_ntypes) 0
	(fun i acc -> 
	   let ip = (sp,-i) in
	   let nc = Array.length mib.mind_packets.(-i).mind_consnames in 
	   match lookup_inductive ip with
	     | Iprop -> acc
	     | Iml (_,vl) -> (vl, IndRef ip, one_ind ip nc) :: acc)
	[] 
    in
    Dtype (l, not mib.mind_finite)
      
(*S Extraction of a global reference. *)

(* It is either a constant or an inductive. *)

let extract_declaration r = match r with
  | ConstRef sp -> 
      (match extract_constant sp with
	 | Emltype (mlt, s, vl) -> Dabbrev (r, vl, mlt)
	 | Emlterm t -> Dglob (r, t))
  | IndRef (sp,_) -> extract_inductive_declaration sp
  | ConstructRef ((sp,_),_) -> extract_inductive_declaration sp
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
