(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
open Util
open Pp
open Bigint
open Names
open Term
open Nametab
open Libnames
open Summary
open Rawterm
open Topconstr
open Ppextend
(*i*)

(*s A scope is a set of notations; it includes

  - a set of ML interpreters/parsers for positive (e.g. 0, 1, 15, ...) and
    negative numbers (e.g. -0, -2, -13, ...). These interpreters may
    fail if a number has no interpretation in the scope (e.g. there is
    no interpretation for negative numbers in [nat]); interpreters both for
    terms and patterns can be set; these interpreters are in permanent table
    [numeral_interpreter_tab]
  - a set of ML printers for expressions denoting numbers parsable in 
    this scope
  - a set of interpretations for infix (more generally distfix) notations
  - an optional pair of delimiters which, when occurring in a syntactic
    expression, set this scope to be the current scope
*)

(**********************************************************************)
(* Scope of symbols *)

type level = precedence * tolerability list
type delimiters = string
type notation_location = dir_path * string

type scope = {
  notations: (string, interpretation * notation_location) Gmap.t;
  delimiters: delimiters option
}

(* Uninterpreted notation map: notation -> level * dir_path *)
let notation_level_map = ref Gmap.empty

(* Scopes table: scope_name -> symbol_interpretation *)
let scope_map = ref Gmap.empty

let empty_scope = {
  notations = Gmap.empty;
  delimiters = None
}

let default_scope = "" (* empty name, not available from outside *)
let type_scope = "type_scope" (* special scope used for interpreting types *)

let init_scope_map () =
  scope_map := Gmap.add default_scope empty_scope !scope_map;
  scope_map := Gmap.add type_scope empty_scope !scope_map

(**********************************************************************)
(* Operations on scopes *)

let declare_scope scope =
  try let _ = Gmap.find scope !scope_map in ()
  with Not_found ->
(*    Flags.if_verbose message ("Creating scope "^scope);*)
    scope_map := Gmap.add scope empty_scope !scope_map

let find_scope scope =
  try Gmap.find scope !scope_map
  with Not_found -> error ("Scope "^scope^" is not declared.")

let check_scope sc = let _ = find_scope sc in ()

(**********************************************************************)
(* The global stack of scopes                                         *)

type scope_elem = Scope of scope_name | SingleNotation of string
type scopes = scope_elem list

let scope_stack = ref []

let current_scopes () = !scope_stack

(* TODO: push nat_scope, z_scope, ... in scopes summary *)

(* Exportation of scopes *)
let open_scope i (_,(local,op,sc)) =
  if i=1 then begin
  (match sc with Scope sc -> check_scope sc | _ -> ());
  scope_stack := if op then sc :: !scope_stack else list_except sc !scope_stack
  end

let cache_scope o =
  open_scope 1 o

let subst_scope (_,subst,sc) = sc

open Libobject

let classify_scope (_,(local,_,_ as o)) =
  if local then Dispose else Substitute o

let export_scope (local,_,_ as x) = if local then None else Some x

let (inScope,outScope) = 
  declare_object {(default_object "SCOPE") with
      cache_function = cache_scope;
      open_function = open_scope;
      subst_function = subst_scope;
      classify_function = classify_scope;
      export_function = export_scope }

let open_close_scope (local,opening,sc) =
  Lib.add_anonymous_leaf (inScope (local,opening,Scope sc))

let empty_scope_stack = []

let push_scope sc scopes = Scope sc :: scopes

let push_scopes = List.fold_right push_scope

type local_scopes = tmp_scope_name option * scope_name list

let make_current_scopes (tmp_scope,scopes) =
  Option.fold_right push_scope tmp_scope (push_scopes scopes !scope_stack)

(**********************************************************************)
(* Delimiters *)

let delimiters_map = ref Gmap.empty

let declare_delimiters scope key =
  let sc = find_scope scope in
  if sc.delimiters <> None && Flags.is_verbose () then begin
    let old = Option.get sc.delimiters in
    Flags.if_verbose 
      warning ("Overwritting previous delimiting key "^old^" in scope "^scope)
  end;
  let sc = { sc with delimiters = Some key } in
  scope_map := Gmap.add scope sc !scope_map;
  if Gmap.mem key !delimiters_map then begin
    let oldsc = Gmap.find key !delimiters_map in
    Flags.if_verbose warning ("Hiding binding of key "^key^" to "^oldsc)
  end;
  delimiters_map := Gmap.add key scope !delimiters_map

let find_delimiters_scope loc key = 
  try Gmap.find key !delimiters_map
  with Not_found -> 
    user_err_loc 
    (loc, "find_delimiters", str ("Unknown scope delimiting key "^key^"."))

(* Uninterpretation tables *)

type interp_rule =
  | NotationRule of scope_name option * notation
  | SynDefRule of kernel_name

(* We define keys for rawterm and aconstr to split the syntax entries
   according to the key of the pattern (adapted from Chet Murthy by HH) *)

type key =
  | RefKey of global_reference
  | Oth

(* Scopes table : interpretation -> scope_name *)
let notations_key_table = ref Gmapl.empty
let prim_token_key_table = Hashtbl.create 7

let rawconstr_key = function
  | RApp (_,RRef (_,ref),_) -> RefKey ref
  | RRef (_,ref) -> RefKey ref
  | _ -> Oth

let cases_pattern_key = function
  | PatCstr (_,ref,_,_) -> RefKey (ConstructRef ref)
  | _ -> Oth

let aconstr_key = function (* Rem: AApp(ARef ref,[]) stands for @ref *)
  | AApp (ARef ref,args) -> RefKey ref, Some (List.length args)
  | AList (_,_,AApp (ARef ref,args),_,_) -> RefKey ref, Some (List.length args)
  | ARef ref -> RefKey ref, None
  | _ -> Oth, None

let pattern_key = function
  | PatCstr (_,cstr,_,_) -> RefKey (ConstructRef cstr)
  | _ -> Oth

(**********************************************************************)
(* Interpreting numbers (not in summary because functional objects)   *)

type required_module = section_path * string list 

type 'a prim_token_interpreter =
    loc -> 'a -> rawconstr

type cases_pattern_status = bool (* true = use prim token in patterns *)

type 'a prim_token_uninterpreter =
    rawconstr list * (rawconstr -> 'a option) * cases_pattern_status

type internal_prim_token_interpreter =
    loc -> prim_token -> required_module * (unit -> rawconstr)

let prim_token_interpreter_tab =
  (Hashtbl.create 7 : (scope_name, internal_prim_token_interpreter) Hashtbl.t)

let add_prim_token_interpreter sc interp =
  try 
    let cont = Hashtbl.find prim_token_interpreter_tab sc in
    Hashtbl.replace prim_token_interpreter_tab sc (interp cont)
  with Not_found ->
    let cont = (fun _loc _p -> raise Not_found) in
    Hashtbl.add prim_token_interpreter_tab sc (interp cont)

let declare_prim_token_interpreter sc interp (patl,uninterp,b) =
  declare_scope sc;
  add_prim_token_interpreter sc interp;
  List.iter (fun pat -> 
      Hashtbl.add prim_token_key_table (rawconstr_key pat) (sc,uninterp,b))
    patl

let mkNumeral n = Numeral n
let mkString s = String s

let delay dir int loc x = (dir, (fun () -> int loc x))

let declare_numeral_interpreter sc dir interp (patl,uninterp,inpat) =
  declare_prim_token_interpreter sc
    (fun cont loc -> function Numeral n-> delay dir interp loc n | p -> cont loc p)
    (patl, (fun r -> Option.map mkNumeral (uninterp r)), inpat)

let declare_string_interpreter sc dir interp (patl,uninterp,inpat) =
  declare_prim_token_interpreter sc
    (fun cont loc -> function String s -> delay dir interp loc s | p -> cont loc p)
    (patl, (fun r -> Option.map mkString (uninterp r)), inpat)

let check_required_module loc sc (sp,d) =
  try let _ = Nametab.absolute_reference sp in ()
  with Not_found ->
    user_err_loc (loc,"prim_token_interpreter",
    str ("Cannot interpret in "^sc^" without requiring first module "
    ^(list_last d)^"."))

(* Look if some notation or numeral printer in [scope] can be used in
   the scope stack [scopes], and if yes, using delimiters or not *)

let find_with_delimiters = function
  | None -> None
  | Some scope ->
      match (Gmap.find scope !scope_map).delimiters with
	| Some key -> Some (Some scope, Some key)
	| None -> None

let rec find_without_delimiters find (ntn_scope,ntn) = function
  | Scope scope :: scopes -> 
      (* Is the expected ntn/numpr attached to the most recently open scope? *)
      if Some scope = ntn_scope then
	Some (None,None)
      else
	(* If the most recently open scope has a notation/numeral printer
    	   but not the expected one then we need delimiters *)
	if find scope then
	  find_with_delimiters ntn_scope
	else
	  find_without_delimiters find (ntn_scope,ntn) scopes
  | SingleNotation ntn' :: scopes ->
      if ntn_scope = None & ntn = Some ntn' then 
	Some (None,None)
      else
	find_without_delimiters find (ntn_scope,ntn) scopes
  | [] ->
      (* Can we switch to [scope]? Yes if it has defined delimiters *)
      find_with_delimiters ntn_scope

(* Uninterpreted notation levels *)

let declare_notation_level ntn level =
  if Gmap.mem ntn !notation_level_map then
    anomaly ("Notation "^ntn^" is already assigned a level");
  notation_level_map := Gmap.add ntn level !notation_level_map

let level_of_notation ntn =
  Gmap.find ntn !notation_level_map

(* The mapping between notations and their interpretation *)

let declare_notation_interpretation ntn scopt pat df =
  let scope = match scopt with Some s -> s | None -> default_scope in
  let sc = find_scope scope in
  if Gmap.mem ntn sc.notations then
    Flags.if_warn msg_warning (str ("Notation "^ntn^" was already used"^
    (if scopt = None then "" else " in scope "^scope)));
  let sc = { sc with notations = Gmap.add ntn (pat,df) sc.notations } in
  scope_map := Gmap.add scope sc !scope_map;
  if scopt = None then scope_stack := SingleNotation ntn :: !scope_stack

let declare_uninterpretation rule (metas,c as pat) =
  let (key,n) = aconstr_key c in
  notations_key_table := Gmapl.add key (rule,pat,n) !notations_key_table

let rec find_interpretation find = function
  | [] -> raise Not_found
  | sce :: scopes ->
      let sc,sco = match sce with
	| Scope sc -> sc, Some sc
	| SingleNotation _ -> default_scope, None in
      try
	let (pat,df) = find sc in
	pat,(df,sco)
      with Not_found ->
	find_interpretation find scopes

let find_notation ntn sc =
  Gmap.find ntn (find_scope sc).notations

let notation_of_prim_token = function
  | Numeral n when is_pos_or_zero n -> to_string n
  | Numeral n -> "- "^(to_string (neg n))
  | String _ -> raise Not_found

let find_prim_token g loc p sc =
  (* Try for a user-defined numerical notation *)
  try
    let (_,c),df = find_notation (notation_of_prim_token p) sc in
    g (rawconstr_of_aconstr loc c),df
  with Not_found ->
  (* Try for a primitive numerical notation *)
  let (spdir,interp) = Hashtbl.find prim_token_interpreter_tab sc loc p in
  check_required_module loc sc spdir;
  g (interp ()), (dirpath (fst spdir),"")

let interp_prim_token_gen g loc p local_scopes =
  let scopes = make_current_scopes local_scopes in
  try find_interpretation (find_prim_token g loc p) scopes
  with Not_found ->
    user_err_loc (loc,"interp_prim_token",
    (match p with
      | Numeral n -> str "No interpretation for numeral " ++ pr_bigint n
      | String s -> str "No interpretation for string " ++ qs s) ++ str ".")

let interp_prim_token =
  interp_prim_token_gen (fun x -> x)

let interp_prim_token_cases_pattern loc p name =
  interp_prim_token_gen (cases_pattern_of_rawconstr name) loc p

let rec interp_notation loc ntn local_scopes =
  let scopes = make_current_scopes local_scopes in
  try find_interpretation (find_notation ntn) scopes
  with Not_found ->
    user_err_loc
    (loc,"",str ("Unknown interpretation for notation \""^ntn^"\"."))

let uninterp_notations c =
  Gmapl.find (rawconstr_key c) !notations_key_table

let uninterp_cases_pattern_notations c =
  Gmapl.find (cases_pattern_key c) !notations_key_table

let availability_of_notation (ntn_scope,ntn) scopes =
  let f scope =
    Gmap.mem ntn (Gmap.find scope !scope_map).notations in
  find_without_delimiters f (ntn_scope,Some ntn) (make_current_scopes scopes)

let uninterp_prim_token c =
  try 
    let (sc,numpr,_) = Hashtbl.find prim_token_key_table (rawconstr_key c) in
    match numpr c with
      | None -> raise No_match
      | Some n -> (sc,n)
  with Not_found -> raise No_match

let uninterp_prim_token_cases_pattern c =
  try 
    let k = cases_pattern_key c in
    let (sc,numpr,b) = Hashtbl.find prim_token_key_table k in
    if not b then raise No_match;
    let na,c = rawconstr_of_closed_cases_pattern c in
    match numpr c with
      | None -> raise No_match
      | Some n -> (na,sc,n)
  with Not_found -> raise No_match

let availability_of_prim_token printer_scope local_scopes =
  let f scope = Hashtbl.mem prim_token_interpreter_tab scope in
  let scopes = make_current_scopes local_scopes in
  Option.map snd (find_without_delimiters f (Some printer_scope,None) scopes)

(* Miscellaneous *)

let exists_notation_in_scope scopt ntn r =
  let scope = match scopt with Some s -> s | None -> default_scope in
  try
    let sc = Gmap.find scope !scope_map in
    let (r',_) = Gmap.find ntn sc.notations in
    r' = r
  with Not_found -> false

let isAVar = function AVar _ -> true | _ -> false

(**********************************************************************)
(* Mapping classes to scopes *)

open Classops

let class_scope_map = ref (Gmap.empty : (cl_typ,scope_name) Gmap.t)

let _ = Gmap.add CL_SORT "type_scope" Gmap.empty

let declare_class_scope sc cl =
  class_scope_map := Gmap.add cl sc !class_scope_map

let find_class_scope cl =
  Gmap.find cl !class_scope_map

let find_class t =
  let t, _ = decompose_app (Reductionops.whd_betaiotazeta t) in
  match kind_of_term t with
    | Var id -> CL_SECVAR id
    | Const sp -> CL_CONST sp
    | Ind ind_sp -> CL_IND ind_sp
    | Prod (_,_,_) -> CL_FUN
    | Sort _ -> CL_SORT
    |  _ -> raise Not_found

(**********************************************************************)
(* Special scopes associated to arguments of a global reference *)

let rec compute_arguments_scope t =
  match kind_of_term (Reductionops.whd_betaiotazeta t) with
    | Prod (_,t,u) ->
	let sc =
	  try Some (find_class_scope (find_class t)) with Not_found -> None in
	sc :: compute_arguments_scope u
    | _ -> []

let arguments_scope = ref Refmap.empty

type arguments_scope_discharge_request =
  | ArgsScopeAuto
  | ArgsScopeManual
  | ArgsScopeNoDischarge

let load_arguments_scope _ (_,(_,r,scl)) =
  List.iter (Option.iter check_scope) scl;
  arguments_scope := Refmap.add r scl !arguments_scope

let cache_arguments_scope o =
  load_arguments_scope 1 o

let subst_arguments_scope (_,subst,(req,r,scl)) =
  (ArgsScopeNoDischarge,fst (subst_global subst r),scl)

let discharge_arguments_scope (_,(req,r,l)) =
  if req = ArgsScopeNoDischarge or (isVarRef r & Lib.is_in_section r) then None
  else Some (req,Lib.discharge_global r,l)

let rebuild_arguments_scope (_,(req,r,l)) =
  match req with
    | ArgsScopeNoDischarge -> assert false
    | ArgsScopeAuto ->
	(req,r,compute_arguments_scope (Global.type_of_global r))
    | ArgsScopeManual ->
	(* Add to the manually given scopes the one found automatically
           for the extra parameters of the section *)
	let l' = compute_arguments_scope (Global.type_of_global r) in
	let l1,_ = list_chop (List.length l' - List.length l) l' in
	(req,r,l1@l)

let (inArgumentsScope,outArgumentsScope) = 
  declare_object {(default_object "ARGUMENTS-SCOPE") with
      cache_function = cache_arguments_scope;
      load_function = load_arguments_scope;
      subst_function = subst_arguments_scope;
      classify_function = (fun (_,o) -> Substitute o);
      discharge_function = discharge_arguments_scope;
      rebuild_function = rebuild_arguments_scope;
      export_function = (fun x -> Some x) }

let declare_arguments_scope_gen req r scl =
  Lib.add_anonymous_leaf (inArgumentsScope (req,r,scl))

let declare_arguments_scope local ref scl =
  let req = if local then ArgsScopeNoDischarge else ArgsScopeManual in
  declare_arguments_scope_gen req ref scl

let find_arguments_scope r =
  try Refmap.find r !arguments_scope
  with Not_found -> []

let declare_ref_arguments_scope ref =
  let t = Global.type_of_global ref in
  declare_arguments_scope_gen ArgsScopeAuto ref (compute_arguments_scope t)

(********************************)
(* Encoding notations as string *)

type symbol =
  | Terminal of string
  | NonTerminal of identifier
  | SProdList of identifier * symbol list
  | Break of int

let rec string_of_symbol = function
  | NonTerminal _ -> ["_"]
  | Terminal s -> [s]
  | SProdList (_,l) -> 
     let l = List.flatten (List.map string_of_symbol l) in "_"::l@".."::l@["_"]
  | Break _ -> []

let make_notation_key symbols =
  String.concat " " (List.flatten (List.map string_of_symbol symbols))

let decompose_notation_key s =
  let len = String.length s in
  let rec decomp_ntn dirs n =
    if n>=len then List.rev dirs else
    let pos =
      try
	String.index_from s n ' ' 
      with Not_found -> len
    in
    let tok =
      match String.sub s n (pos-n) with
      | "_" -> NonTerminal (id_of_string "_")
      | s -> Terminal s in
    decomp_ntn (tok::dirs) (pos+1)	  
  in
    decomp_ntn [] 0

(************)
(* Printing *)

let pr_delimiters_info = function
  | None -> str "No delimiting key"
  | Some key -> str "Delimiting key is " ++ str key

let classes_of_scope sc =
  Gmap.fold (fun cl sc' l -> if sc = sc' then cl::l else l) !class_scope_map []

let pr_scope_classes sc =
  let l = classes_of_scope sc in
  if l = [] then mt()
  else 
    hov 0 (str ("Bound to class"^(if List.tl l=[] then "" else "es")) ++
      spc() ++ prlist_with_sep spc pr_class l) ++ fnl()

let pr_notation_info prraw ntn c =
  str "\"" ++ str ntn ++ str "\" := " ++ 
  prraw (rawconstr_of_aconstr dummy_loc c)

let pr_named_scope prraw scope sc =
 (if scope = default_scope then
   match Gmap.fold (fun _ _ x -> x+1) sc.notations 0 with
     | 0 -> str "No lonely notation"
     | n -> str "Lonely notation" ++ (if n=1 then mt() else str"s")
  else 
    str "Scope " ++ str scope ++ fnl () ++ pr_delimiters_info sc.delimiters)
  ++ fnl ()
  ++ pr_scope_classes scope
  ++ Gmap.fold
       (fun ntn ((_,r),(_,df)) strm ->
	 pr_notation_info prraw df r ++ fnl () ++ strm)
       sc.notations (mt ())

let pr_scope prraw scope = pr_named_scope prraw scope (find_scope scope)

let pr_scopes prraw =
 Gmap.fold 
   (fun scope sc strm -> pr_named_scope prraw scope sc ++ fnl () ++ strm)
   !scope_map (mt ())

let rec find_default ntn = function
  | Scope scope::_ when Gmap.mem ntn (find_scope scope).notations ->
      Some scope
  | SingleNotation ntn'::_ when ntn = ntn' -> Some default_scope
  | _::scopes -> find_default ntn scopes
  | [] -> None

let factorize_entries = function
  | [] -> []
  | (ntn,c)::l ->
      let (ntn,l_of_ntn,rest) =
	List.fold_left
          (fun (a',l,rest) (a,c) ->
	    if a = a' then (a',c::l,rest) else (a,[c],(a',l)::rest))
	  (ntn,[c],[]) l in
      (ntn,l_of_ntn)::rest

let is_ident s = (* Poor analysis *)
  String.length s <> 0 & is_letter s.[0]

let browse_notation strict ntn map =
  let find =
    if String.contains ntn ' ' then (=) ntn
    else fun ntn' ->
      let toks = decompose_notation_key ntn' in
      let trms = List.filter (function Terminal _ -> true | _ -> false) toks in
      if strict then [Terminal ntn] = trms else List.mem (Terminal ntn) trms in
  let l =
    Gmap.fold 
      (fun scope_name sc ->
	Gmap.fold (fun ntn ((_,r),df) l ->
	  if find ntn then (ntn,(scope_name,r,df))::l else l) sc.notations)
      map [] in
  List.sort (fun x y -> Pervasives.compare (fst x) (fst y)) l

let global_reference_of_notation test (ntn,(sc,c,_)) =
  match c with
  | ARef ref when test ref -> Some (ntn,sc,ref)
  | AApp (ARef ref, l) when List.for_all isAVar l & test ref -> 
      Some (ntn,sc,ref)
  | _ -> None

let error_ambiguous_notation loc _ntn =
  user_err_loc (loc,"",str "Ambiguous notation.")

let error_notation_not_reference loc ntn =
  user_err_loc (loc,"",
    str "Unable to interpret " ++ quote (str ntn) ++
    str " as a reference.")

let interp_notation_as_global_reference loc test ntn =
  let ntns = browse_notation true ntn !scope_map in
  let refs = List.map (global_reference_of_notation test) ntns in
  match Option.List.flatten refs with
  | [_,_,ref] -> ref
  | [] -> error_notation_not_reference loc ntn
  | refs -> 
      let f (ntn,sc,ref) = find_default ntn !scope_stack = Some sc in
      match List.filter f refs with
      | [_,_,ref] -> ref
      | [] -> error_notation_not_reference loc ntn
      | _ -> error_ambiguous_notation loc ntn

let locate_notation prraw ntn =
  let ntns = factorize_entries (browse_notation false ntn !scope_map) in
  if ntns = [] then
    str "Unknown notation"
  else
    t (str "Notation            " ++
    tab () ++ str "Scope     " ++ tab () ++ fnl () ++ 
    prlist (fun (ntn,l) ->
      let scope = find_default ntn !scope_stack in
      prlist 
	(fun (sc,r,(_,df)) ->
	  hov 0 (
	    pr_notation_info prraw df r ++ tbrk (1,2) ++
	    (if sc = default_scope then mt () else (str ": " ++ str sc)) ++ 
	    tbrk (1,2) ++
	    (if Some sc = scope then str "(default interpretation)" else mt ())
	    ++ fnl ()))
	l) ntns)

let collect_notation_in_scope scope sc known =
  assert (scope <> default_scope);
  Gmap.fold
    (fun ntn ((_,r),(_,df)) (l,known as acc) ->
      if List.mem ntn known then acc else ((df,r)::l,ntn::known))
    sc.notations ([],known)

let collect_notations stack =
  fst (List.fold_left
    (fun (all,knownntn as acc) -> function
      | Scope scope ->
	  if List.mem_assoc scope all then acc
	  else
	    let (l,knownntn) =
	      collect_notation_in_scope scope (find_scope scope) knownntn in
	    ((scope,l)::all,knownntn)
      | SingleNotation ntn ->
	  if List.mem ntn knownntn then (all,knownntn)
	  else
	    let ((_,r),(_,df)) =
	      Gmap.find ntn (find_scope default_scope).notations in
	    let all' = match all with
	      | (s,lonelyntn)::rest when s = default_scope ->
		  (s,(df,r)::lonelyntn)::rest
	      | _ -> 
		  (default_scope,[df,r])::all in
	    (all',ntn::knownntn))
    ([],[]) stack)

let pr_visible_in_scope prraw (scope,ntns) =
  let strm =
    List.fold_right
      (fun (df,r) strm -> pr_notation_info prraw df r ++ fnl () ++ strm)
      ntns (mt ()) in
  (if scope = default_scope then
     str "Lonely notation" ++ (if List.length ntns <> 1 then str "s" else mt())
   else 
     str "Visible in scope " ++ str scope)
  ++ fnl () ++ strm

let pr_scope_stack prraw stack = 
  List.fold_left
    (fun strm scntns -> strm ++ pr_visible_in_scope prraw scntns ++ fnl ())
    (mt ()) (collect_notations stack)

let pr_visibility prraw = function
  | Some scope -> pr_scope_stack prraw (push_scope scope !scope_stack)
  | None -> pr_scope_stack prraw !scope_stack

(**********************************************************************)
(* Mapping notations to concrete syntax *)

type unparsing_rule = unparsing list * precedence

(* Concrete syntax for symbolic-extension table *)
let printing_rules = 
  ref (Gmap.empty : (string,unparsing_rule) Gmap.t)

let declare_notation_printing_rule ntn unpl =
  printing_rules := Gmap.add ntn unpl !printing_rules

let find_notation_printing_rule ntn =
  try Gmap.find ntn !printing_rules
  with Not_found -> anomaly ("No printing rule found for "^ntn)

(**********************************************************************)
(* Synchronisation with reset *)

let freeze () =
 (!scope_map, !notation_level_map, !scope_stack, !arguments_scope,
  !delimiters_map, !notations_key_table, !printing_rules,
  !class_scope_map)

let unfreeze (scm,nlm,scs,asc,dlm,fkm,pprules,clsc) =
  scope_map := scm;
  notation_level_map := nlm;
  scope_stack := scs;
  delimiters_map := dlm;
  arguments_scope := asc;
  notations_key_table := fkm;
  printing_rules := pprules;
  class_scope_map := clsc

let init () =
  init_scope_map ();
(*
  scope_stack := Gmap.empty
  arguments_scope := Refmap.empty
*)
  notation_level_map := Gmap.empty;
  delimiters_map := Gmap.empty;
  notations_key_table := Gmapl.empty;
  printing_rules := Gmap.empty;
  class_scope_map := Gmap.add CL_SORT "type_scope" Gmap.empty

let _ = 
  declare_summary "symbols"
    { freeze_function = freeze;
      unfreeze_function = unfreeze;
      init_function = init;
      survive_module = false;
      survive_section = false }
