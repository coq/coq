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

(* The flag [type_var] gives us information about an identifier
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

type type_var = info * arity

let logic_arity = (Logic, Arity)
let info_arity = (Info, Arity)
let logic = (Logic, NotArity)
let default = (Info, NotArity)

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)
   
(* Convention: outmost lambda/product gives the head of the list *)

type signature = type_var list

(* The [type_extraction_result] is the result of the [extract_type] function
   that extracts a CIC object into an ML type. It is either: 
   \begin{itemize}
   \item a real ML type, followed by its list of type variables (['a],\ldots)
   \item a dummy type, denoting either: 
   \begin{itemize} 
   \item a CIC arity, without counterpart in ML
   \item a non-informative type, which will receive special treatment
   \end{itemize}
   \end{itemize} *)

type type_extraction_result =
  | Tmltype of ml_type * identifier list
  | Tdum

(* The [indutive_extraction_result] is the dual of [type_extraction_result], 
   but for inductive types. *)

type inductive_extraction_result = 
  | Iml of signature * identifier list
  | Iprop

(* For an informative constructor, the [constructor_extraction_result] contains
   the list of the types of its arguments, a signature, and the number of 
   parameters to discard. *)

type constructor_extraction_result = 
  | Cml of ml_type list * signature * int
  | Cprop

(* The [extraction_result] is the result of the [extract_constr]
   function that extracts any CIC object. It is either a ML type or 
   a ML object. *)

type extraction_result =
  | Emltype of ml_type * signature * identifier list
  | Emlterm of ml_ast

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

(*S Utility functions. *)

let none = Evd.empty

let type_of env c = Retyping.get_type_of env none (strip_outer_cast c)

let sort_of env c = Retyping.get_sort_family_of env none (strip_outer_cast c)

let is_axiom sp = (Global.lookup_constant sp).const_body = None

type lamprod = Lam | Product

let dummy_arrow = function 
  | Tmltype (mld,vl) -> Tmltype (Tarr (Tdummy, mld), vl)
  | Tdum -> Tdum

(*s [list_of_ml_arrows] applied to the ML type [a->b->]\dots[z->t]
   returns the list [[a;b;...;z]]. It is used when making the ML types
   of inductive definitions. We also suppress [prop] and [arity] parts. *)

let rec list_of_ml_arrows = function
  | Tarr (Tdummy, b) -> list_of_ml_arrows b
  | Tarr (a, b) -> a :: list_of_ml_arrows b
  | t -> []

(*s [get_arity c] returns [Some s] if [c] is an arity of sort [s], 
  and [None] otherwise. *)

let rec get_arity env c =
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (x,t,c0) -> get_arity (push_rel (x,None,t) env) c0
    | Sort s -> Some (family_of_sort s)
    | _ -> None

(*s [v_of_t] transforms a type [t] into a [type_var] flag. 
  Really important function. *)

let v_of_t env t = match get_arity env t with
  | Some InProp -> logic_arity
  | Some _ -> info_arity
  | None when (sort_of env t) = InProp -> logic
  | None -> default

(*S Operations on binders. *)

type binders = (name * constr) list

(* Convention: right binders give [Rel 1] at the head, like those answered by 
   [decompose_prod]. Left binders are the converse, like [signature]. *)

let rec lbinders_fold f acc env = function 
  | [] -> acc
  | (n,t) as b :: l -> 
      f n t (v_of_t env t)
        (lbinders_fold f acc (push_rel_assum b env) l)

(*s [sign_of_arity] transforms an arity into a signature. It is used 
   for example with the types of inductive definitions, which are known
   to be already in arity form. *)

let sign_of_lbinders = lbinders_fold (fun _ _ v a -> v::a) [] 

let sign_of_arity env c = 
  sign_of_lbinders env (List.rev (fst (decompose_prod c)))

(*s [vl_of_arity] returns the list of the lambda variables tagged [info_arity]
   in an arity. Renaming is done. *)

let vl_of_lbinders = 
  let f n _ v a = if v <> info_arity then a 
  else (next_ident_away (id_of_name n) a) :: a
  in lbinders_fold f [] 
  
let vl_of_arity env c = vl_of_lbinders env (List.rev (fst (decompose_prod c)))
	 
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
    | (Info,NotArity) :: l -> abs (anonymous :: ids) (MLrel i :: rels) (i+1) l 
    | _ :: l -> abs (dummy_name :: ids) (MLdummy :: rels) (i+1) l
  in abs ids [] 1 s

let kill_all_prop_lams_eta e s = 
  let m = List.length s in 
  let n = nb_lams e in 
  let p = if m <= n then collect_n_lams m e 
  else expansion_prop_eta (snd (list_chop n s)) (collect_lams e) in 
  kill_some_lams (List.rev_map ((=) default) s) p

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
    | ((_,Arity)|(Logic,_)) :: l -> MLlam (dummy_name, abs rels (succ i) l)
    | (Info,_) :: l -> MLlam (anonymous, abs (i :: rels) (succ i) l)
  in abs [] 1  

(*s Abstraction of an constant. *)

let abstract_constant sp s = 
  if List.for_all ((=) default) s then MLglob (ConstRef sp) 
  else 
    let f a = 
      if List.mem default s then MLapp (MLglob (ConstRef sp), a)
      else MLapp (MLglob (ConstRef sp), [MLdummy])
    in prop_abstract f s

(*S Error messages. *)

let axiom_message sp =
  errorlabstrm "axiom_message"
    (str "You must specify an extraction for axiom" ++ spc () ++ 
       pr_sp sp ++ spc () ++ str "first.")

let section_message () = 
  errorlabstrm "section_message"
    (str "You can't extract within a section. Close it and try again.")

(*S Extraction of a type. *)

(* When calling [extract_type] we suppose that the type of [c] is an
   arity. This is for example checked in [extract_constr]. *)

(* Relation with [v_of_t]: it is less precise, since we do not 
   delta-reduce in [extract_type] in general.
   \begin{itemize}
   \item If [v_of_t env t = _,NotArity], 
   then [extract_type env t] is a [Tmltype].
   \item If [extract_type env t = Tdum], then [v_of_t env t = _,Arity]
   or [Logic,NotArity].
   \end{itemize} *)

(* Generation of type variable list (['a] in caml).
   In Coq [(a:Set)(a:Set)a] is legal, but in ML we have only a flat list 
   of type variable, so we must take care of renaming now, in order to get 
   something like [type ('a,'a0) foo = 'a0].  The list [vl] is used to 
   accumulate those type variables and to do renaming on the fly. 
   Convention: the last elements of this list correspond to external products.
   This is used when dealing with applications *)

let rec extract_type env c =
  extract_type_rec env c [] [] 

and extract_type_rec env c vl args = 
  (* We accumulate the context, arguments and generated variables list *)
  let t = type_of env (applist (c, args)) in
  (* Since [t] is an arity, there is two non-informative case: *)
  (* [t] is an arity of sort [Prop], or *)
  (* [c] has a non-informative head symbol *)
  match get_arity env t with 
    | None -> assert false (* Cf. precondition. *)
    | Some InProp -> Tdum 
    | Some _ -> extract_type_rec_info env c vl args
	  
and extract_type_rec_info env c vl args = 
  match (kind_of_term (whd_betaiotazeta c)) with
    | Sort _ ->
	assert (args = []); (* A sort can't be applied. *)
	Tdum 
    | Prod (n,t,d) ->
	assert (args = []); (* A product can't be applied. *)
	extract_prod_lam env (n,t,d) vl Product
    | Lambda (n,t,d) ->
	assert (args = []); (* [c] is now in head normal form. *)
	extract_prod_lam env (n,t,d) vl Lam
    | App (d, args') ->
	(* We just accumulate the arguments. *)
	extract_type_rec_info env d vl (Array.to_list args' @ args)
    | Rel n -> 
	(match lookup_rel n env with
	   | (_,Some t,_) -> extract_type_rec_info env (lift n t) vl args  
	   | (id,_,_) -> Tmltype (Tvar (id_of_name id), vl))
    | Const sp when args = [] && is_ml_extraction (ConstRef sp) ->
	Tmltype (Tglob (ConstRef sp), vl)
    | Const sp when is_axiom sp -> 
	let id = next_ident_away (basename sp) (dummy_name::vl) in 
	Tmltype (Tvar id,  id :: vl)
    | Const sp ->
	let t = constant_type env sp in 
	if is_arity env none t then
	  (match extract_constant sp with 
	     | Emltype (Tdummy,_,_) -> Tdum
	     | Emltype (_, sc, vlc) ->  
		 extract_type_app env (ConstRef sp,sc,vlc) vl args 
	     | Emlterm _ -> assert false) 
	else 
	  (* We can't keep as ML type abbreviation a CIC constant *)
	  (* which type is not an arity: we reduce this constant. *)
	  let cvalue = constant_value env sp in
	  extract_type_rec_info env (applist (cvalue, args)) vl []
    | Ind spi ->
	(match extract_inductive spi with 
	   |Iml (si,vli) -> extract_type_app env (IndRef spi,si,vli) vl args 
	   |Iprop -> assert false (* Cf. initial tests *))
    | Case _ | Fix _ | CoFix _ ->
	let id = next_ident_away flex_name (dummy_name::vl) in
	Tmltype (Tvar id,  id :: vl)
	  (* Type without counterpart in ML: we generate a 
	     new flexible type variable. *) 
    | Var _ -> section_message ()
    | _ -> assert false

(*s Auxiliary function used to factor code in lambda and product cases *)

and extract_prod_lam env (n,t,d) vl flag = 
  let tag = v_of_t env t in
  let env' = push_rel_assum (n,t) env in
  match tag,flag with
    | (Info, Arity), Lam -> 
	(* We rename before the [push_rel], to be sure that the corresponding*)
	(* [lookup_rel] will be correct. *)
	let id' = next_ident_away (id_of_name n) vl in 
	let env' = push_rel_assum (Name id', t) env in
	extract_type_rec_info env' d (id'::vl) []
    | _, Lam ->
	extract_type_rec_info  env' d vl []
    | (Info, Arity), Product -> 
	(* We rename before the [push_rel], to be sure that the corresponding*)
	(* [lookup_rel] will be correct. *)
	let id' = next_ident_away (id_of_name n) vl in 
	let env' = push_rel_assum (Name id', t) env in
	dummy_arrow (extract_type_rec_info env' d (id'::vl) [])
    | (Logic,_), Product -> 
	dummy_arrow (extract_type_rec_info env' d vl [])
    | (Info, NotArity), Product ->
	(* It is important to treat [d] first and [t] in second. *)
	(* This ensures that the end of [vl] correspond to external binders. *)
	(match extract_type_rec_info env' d vl [] with 
	   | Tmltype (mld, vl') -> 
	       (match extract_type_rec_info env t vl' [] with
		  | Tdum -> assert false 
			(* Cf. relation between [extract_type] and [v_of_t] *)
		  | Tmltype (mlt,vl'') -> Tmltype (Tarr(mlt,mld), vl''))
	   | et -> et)
	
(*s Auxiliary function dealing with type application. 
  Precondition: [r] is of type an arity. *)
		  
and extract_type_app env (r,sc,vlc) vl args =
  let diff = (List.length args - List.length sc ) in
  let args = if diff > 0 then begin
    (* This can (normally) only happen when r is a flexible type. *)
    (* We discard the remaining arguments *)
    (*i    wARN (hov 0 (str ("Discarding " ^
		 (string_of_int diff) ^ " type(s) argument(s)."))); i*)
    list_firstn (List.length sc) args
  end else args in
  let nargs = List.length args in
  (* [r] is of type an arity, so it can't be applied to more than n args, *)
  (* where n is the number of products in this arity type. *)
  (* But there are flexibles ... *)
  let sign_args = list_firstn nargs sc in
  let (mlargs,vl') = 
    List.fold_right 
      (fun (v,a) ((args,vl) as acc) -> match v with
	 | _, NotArity -> acc
	 | Logic, Arity -> acc
	 | Info, Arity -> match extract_type_rec_info env a vl [] with
	     | Tdum -> (Tdummy :: args, vl) 
  	           (* we pass a dummy type [arity] as argument *)
	     | Tmltype (mla,vl') -> (mla :: args, vl'))
      (List.combine sign_args args) 
      ([],vl)
  in
  (* The type variable list is [vl'] plus those variables of [c] not *)
  (* corresponding to arguments. There is [nvlargs] such variables of [c] *)
  let nvlargs = List.length vlc - List.length mlargs in 
  assert (nvlargs >= 0);
  let vl'' = 
    List.fold_right 
      (fun id l -> (next_ident_away id (dummy_name::l)) :: l) 
      (list_firstn nvlargs vlc) vl'
  in
  (* We complete the list of arguments of [c] by variables *)
  let vlargs = 
    List.rev_map (fun i -> Tvar i) (list_firstn nvlargs vl'') in
  Tmltype (Tapp ((Tglob r) :: mlargs @ vlargs), vl'')


(*S Signature of a type. *)

(* Precondition:  [c] is of type an arity. 
   This function is built on the [extract_type] model. *)

and signature env c =
  signature_rec env c []

and signature_rec env c args = 
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) 
    | Lambda (n,t,d) -> 
	let env' = push_rel_assum (n,t) env in
	(v_of_t env t) :: (signature_rec env' d [])
    | App (d, args') ->
	signature_rec env d (Array.to_list args' @ args)
    | Rel n -> 
	(match lookup_rel n env with
	   | (_,Some t,_) -> signature_rec env (lift n t) args
	   | _ -> [])
    | Ind spi ->
	(match extract_inductive spi with 
	   |Iml (si,_) -> 
	       let d = List.length si - List.length args in 
	       if d <= 0 then [] else list_lastn d si
	   |Iprop -> [])
    | Sort _ | Case _ | Fix _ | CoFix _ -> []
    | Const sp -> assert (is_axiom sp); [] 
    | Var _ -> section_message ()
    | _ -> assert false

(*s signature of a section path *)

and signature_of_sp sp typ = 
  try lookup_signature sp
  with Not_found -> 
    let s = signature (Global.env()) typ in 
    add_signature sp s; s

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
	 if (v_of_t env t) = default then MLlam (id, d')
	 else MLlam (dummy_name, d')
     | LetIn (n, c1, t1, c2) ->
	 let id = id_of_name n in 
	 (* If [c2] was of type an arity, [c] too would be so *)
	 let c2' = extract_term (push_rel (Name id,Some c1,t1) env) c2 in
	 if (v_of_t env t1) = default then 
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
    let (s,_) = signature_of_constructor cp in
    assert (List.length s = ni.(j));
    let ids,e = kill_all_prop_lams_eta e s in
    (ConstructRef cp, List.rev ids, e)
  in
  if br = [||] then 
    MLexn "absurd case"
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
	let s = iterate (fun l -> logic :: l) ni.(0) [] in
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
  let sf = signature_of_application env f tyf args in  
  assert (List.length sf >= nargs); 
  (* Cf. postcondition of [signature_of_application]. *)
  let args = Array.to_list args in 
  let mlargs = 
    List.fold_right 
      (fun (v,a) args -> match v with
	 | (_,Arity) -> MLdummy :: args
	 | (Logic,NotArity) -> MLdummy :: args
	 | (Info,NotArity) -> 
	     (* We can't trust tag [default], so we use [extract_constr]. *)
	     (extract_constr_to_term env a) :: args)
      (List.combine (list_firstn nargs sf) args)
      []
  in
  (* [f : arity] implies [(f args):arity], that can't be *)
  let f' = extract_term_wt env f tyf in 
  MLapp (f', mlargs)

(*s [signature_of_application] is used to generate a long enough signature.
   Precondition: the head [f] is [Info].
   Postcondition: the output signature is at least as long as the arguments. *)
    
and signature_of_application env f t a =
  let s = signature env t in
  let nargs = Array.length a in	
  let ns = List.length s in 
  if ns >= nargs then s
  else 
    (* This case can really occur. Cf [test_extraction.v]. *)
    let f' = mkApp (f, Array.sub a 0 ns) in 
    let a' = Array.sub a ns (nargs-ns) in 
    let t' = type_of env f' in
    s @ signature_of_application env f' t' a'

(*s Extraction of a constr seen as a term. *)

and extract_constr_to_term env c =
  extract_constr_to_term_wt env c (type_of env c)

(* Same, but With Type (wt). *)

and extract_constr_to_term_wt env c t = 
  match v_of_t env t with
    | (_, Arity) -> MLdummy 
    | (Logic, NotArity) -> MLdummy
    | (Info, NotArity) -> extract_term_wt env c t

(*S Extraction of a constr. *)

and extract_constr env c = 
  extract_constr_wt env c (type_of env c)

(* Same, but With Type (wt). *)

and extract_constr_wt env c t =
  match v_of_t env t with
    | (Logic, Arity) -> Emltype (Tdummy, [], [])
    | (Logic, NotArity) -> Emlterm MLdummy
    | (Info, Arity) -> 
	(match extract_type env c with
	   | Tdum -> Emltype (Tdummy, [], [])
	   | Tmltype (t, vl) -> Emltype (t, (signature env c), vl))
    | (Info, NotArity) -> 
	Emlterm (extract_term_wt env c t)
	  
(*S Extraction of a constant. *)
		
and extract_constant sp =
  try lookup_constant sp 
  with Not_found ->
    let env = Global.env() in    
    let cb = Global.lookup_constant sp in
    let typ = cb.const_type in
    match cb.const_body with
      | None ->
          (match v_of_t env typ with
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
    (* an initial type var list. *)
    let vl0 = iterate_for 0 (mib.mind_ntypes - 1)
	(fun i vl -> 
	   let ip = (sp,i) in 
	   let (mib,mip) = Global.lookup_inductive ip in 
	   if mip.mind_sort = (Prop Null) then begin
	     add_inductive ip Iprop; vl
	   end else begin
	     let arity = mip.mind_nf_arity in
	     let vla = List.rev (vl_of_arity env arity) in 
	     add_inductive ip 
	       (Iml (sign_of_arity env arity, vla));
	     vla @ vl 
	   end
	) []
    in
    (* Second pass: we extract constructors arities and we accumulate *)
    (* type variables. Thanks to on-the-fly renaming in [extract_type], *)
    (* the [vl] list should be correct. *)
    let vl = 
      iterate_for 0 (mib.mind_ntypes - 1)
	(fun i vl -> 
	   let ip = (sp,i) in
           let (mib,mip) = Global.lookup_inductive ip in
	   if mip.mind_sort = Prop Null then begin
	     for j = 1 to Array.length mip.mind_consnames do
	       add_constructor (ip,j) Cprop
	     done;
	     vl
	   end else 
	     iterate_for 1 (Array.length mip.mind_consnames)
	       (fun j vl -> 
		  let t = type_of_constructor env (ip,j) in
		  let t = snd (decompose_prod_n params_nb t) in
		  match extract_type_rec_info params_env t vl [] with
		    | Tdum -> assert false
		    | Tmltype (mlt, v) -> 
			let l = list_of_ml_arrows mlt
			and s = signature params_env t in 
			add_constructor (ip,j) (Cml (l,s,params_nb));
			v)
	       vl)
	vl0
    in
    let vl = list_firstn (List.length vl - List.length vl0) vl in
    (* Third pass: we update the type variables list in the inductives table *)
    for i = 0 to mib.mind_ntypes-1 do 
      let ip = (sp,i) in 
      match lookup_inductive ip with 
	| Iprop -> ()
	| Iml (s,l) -> add_inductive ip (Iml (s,vl@l));
    done;
    (* Fourth pass: we also update the constructors table *)
    for i = 0 to mib.mind_ntypes-1 do 
      let ip = (sp,i) in 
      for j = 1 to Array.length mib.mind_packets.(i).mind_consnames do
	let cp = (ip,j) in 
	match lookup_constructor cp  with 
	  | Cprop -> ()
	  | Cml (t,s,n) -> 
	      let vl = List.rev_map (fun i -> Tvar i) vl in
	      let t' = List.map (update_args sp vl) t in 
	      add_constructor cp (Cml (t',s, n))
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
	     | Iml (_,vl) -> 
		 (List.rev vl, IndRef ip, one_ind ip nc) :: acc)
	[] 
    in
    Dtype (l, not mib.mind_finite)
      
(*S Extraction of a global reference. *)

(* It is either a constant or an inductive. *)

let extract_declaration r = match r with
  | ConstRef sp -> 
      (match extract_constant sp with
	 | Emltype (mlt, s, vl) -> Dabbrev (r, List.rev vl, mlt)
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
