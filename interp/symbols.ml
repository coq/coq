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
open Bignat
open Names
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
    this scope (permanently declared in [Esyntax.primitive_printer_tab])
  - a set of interpretations for infix (more generally distfix) notations
  - an optional pair of delimiters which, when occurring in a syntactic
    expression, set this scope to be the current scope
*)

(**********************************************************************)
(* Scope of symbols *)

type level = precedence * tolerability list
type delimiters = string

type scope = {
  notations: (interpretation * (dir_path * string) * bool) Stringmap.t;
  delimiters: delimiters option
}

(* Uninterpreted notation map: notation -> level * dir_path *)
let notation_level_map = ref Stringmap.empty

(* Scopes table: scope_name -> symbol_interpretation *)
let scope_map = ref Stringmap.empty

let empty_scope = {
  notations = Stringmap.empty;
  delimiters = None
}

let default_scope = "" (* empty name, not available from outside *)
let type_scope = "type_scope" (* special scope used for interpreting types *)

let init_scope_map () =
  scope_map := Stringmap.add default_scope empty_scope !scope_map;
  scope_map := Stringmap.add type_scope empty_scope !scope_map

(**********************************************************************)
(* Operations on scopes *)

let declare_scope scope =
  try let _ = Stringmap.find scope !scope_map in ()
  with Not_found ->
(*    Options.if_verbose message ("Creating scope "^scope);*)
    scope_map := Stringmap.add scope empty_scope !scope_map

let find_scope scope =
  try Stringmap.find scope !scope_map
  with Not_found -> error ("Scope "^scope^" is not declared")

let check_scope sc = let _ = find_scope sc in ()

(**********************************************************************)
(* The global stack of scopes                                         *)

type scope_elem = Scope of scope_name | SingleNotation of string
type scopes = scope_elem list

let scope_stack = ref []

let current_scopes () = !scope_stack

(* TODO: push nat_scope, z_scope, ... in scopes summary *)

(* Exportation of scopes *)
let cache_scope (_,(local,op,sc)) =
  (match sc with Scope sc -> check_scope sc | _ -> ());
  scope_stack := if op then sc :: !scope_stack else list_except sc !scope_stack

let subst_scope (_,subst,sc) = sc

open Libobject

let classify_scope (_,(local,_,_ as o)) =
  if local then Dispose else Substitute o

let export_scope (local,_,_ as x) = if local then None else Some x

let (inScope,outScope) = 
  declare_object {(default_object "SCOPE") with
      cache_function = cache_scope;
      open_function = (fun i o -> if i=1 then cache_scope o);
      subst_function = subst_scope;
      classify_function = classify_scope;
      export_function = export_scope }

let open_close_scope (local,opening,sc) =
  Lib.add_anonymous_leaf (inScope (local,opening,Scope sc))

let empty_scope_stack = []

let push_scope sc scopes = Scope sc :: scopes

(**********************************************************************)
(* Delimiters *)

let delimiters_map = ref Stringmap.empty

let declare_delimiters scope key =
  let sc = find_scope scope in
  if sc.delimiters <> None && Options.is_verbose () then begin
    let old = out_some sc.delimiters in
    Options.if_verbose 
      warning ("Overwritting previous delimiting key "^old^" in scope "^scope)
  end;
  let sc = { sc with delimiters = Some key } in
  scope_map := Stringmap.add scope sc !scope_map;
  if Stringmap.mem key !delimiters_map then begin
    let oldsc = Stringmap.find key !delimiters_map in
    Options.if_verbose warning ("Hidding binding of key "^key^" to "^oldsc)
  end;
  delimiters_map := Stringmap.add key scope !delimiters_map

let find_delimiters_scope loc key = 
  try Stringmap.find key !delimiters_map
  with Not_found -> 
    user_err_loc 
    (loc, "find_delimiters", str ("Unknown scope delimiting key "^key))

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
let numeral_key_table = Hashtbl.create 7

let rawconstr_key = function
  | RApp (_,RRef (_,ref),_) -> RefKey ref
  | RRef (_,ref) -> RefKey ref
  | _ -> Oth

let cases_pattern_key = function
  | PatCstr (_,ref,_,_) -> RefKey (ConstructRef ref)
  | _ -> Oth

let aconstr_key = function
  | AApp (ARef ref,args) -> RefKey ref, Some (List.length args)
  | AList (_,_,AApp (ARef ref,args),_,_) -> RefKey ref, Some (List.length args)
  | ARef ref -> RefKey ref, Some 0
  | _ -> Oth, None

let pattern_key = function
  | PatCstr (_,cstr,_,_) -> RefKey (ConstructRef cstr)
  | _ -> Oth

(**********************************************************************)
(* Interpreting numbers (not in summary because functional objects)   *)

type num_interpreter =
    (loc -> bigint -> rawconstr)
    * (loc -> bigint -> name -> cases_pattern) option

type num_uninterpreter =
    rawconstr list * (rawconstr -> bigint option)
    * (cases_pattern -> bigint option) option

type required_module = global_reference * string list 

let numeral_interpreter_tab =
  (Hashtbl.create 7 : (scope_name,required_module*num_interpreter) Hashtbl.t)

let declare_numeral_interpreter sc dir interp (patl,uninterp,uninterpc) =
  declare_scope sc;
  Hashtbl.add numeral_interpreter_tab sc (dir,interp);
  List.iter
    (fun pat -> Hashtbl.add numeral_key_table (rawconstr_key pat)
      (sc,uninterp,uninterpc))
    patl

let check_required_module loc sc (ref,d) =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  try let _ = sp_of_global ref in ()
  with Not_found ->
    user_err_loc (loc,"numeral_interpreter",
    str ("Cannot interpret numbers in "^sc^" without requiring first module "
    ^(list_last d)))

let lookup_numeral_interpreter loc = function
  | Scope sc ->
      let (dir,interpreter) = Hashtbl.find numeral_interpreter_tab sc in
      check_required_module loc sc dir;
      interpreter
  | SingleNotation _ -> raise Not_found

(* Look if some notation or numeral printer in [scope] can be used in
   the scope stack [scopes], and if yes, using delimiters or not *)

let find_with_delimiters = function
  | None -> None
  | Some scope ->
      match (Stringmap.find scope !scope_map).delimiters with
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
  if not !Options.v7 & Stringmap.mem ntn !notation_level_map then
    error ("Notation "^ntn^" is already assigned a level");
  notation_level_map := Stringmap.add ntn level !notation_level_map

let level_of_notation ntn =
  Stringmap.find ntn !notation_level_map

(* The mapping between notations and their interpretation *)

let declare_notation_interpretation ntn scopt pat df pp8only =
  let scope = match scopt with Some s -> s | None -> default_scope in
  let sc = find_scope scope in
  if Stringmap.mem ntn sc.notations && Options.is_verbose () then
    warning ("Notation "^ntn^" was already used"^
    (if scopt = None then "" else " in scope "^scope));
  let sc = { sc with notations = Stringmap.add ntn (pat,df,pp8only) sc.notations } in
  scope_map := Stringmap.add scope sc !scope_map;
  if scopt = None then scope_stack := SingleNotation ntn :: !scope_stack

let declare_uninterpretation rule (metas,c as pat) =
  let (key,n) = aconstr_key c in
  notations_key_table := Gmapl.add key (rule,pat,n) !notations_key_table

let rec find_interpretation f = function
  | sce :: scopes ->
      let scope = match sce with
	| Scope s -> s 
	| SingleNotation _ -> default_scope in
      (try f scope
      with Not_found -> find_interpretation f scopes)
  | [] -> raise Not_found

let rec interp_notation loc ntn scopes =
  let f sc =
    let scope = find_scope sc in
    let (pat,df,pp8only) = Stringmap.find ntn scope.notations in
    if pp8only then raise Not_found;
    pat,(df,if sc = default_scope then None else Some sc) in
  try find_interpretation f (List.fold_right push_scope scopes !scope_stack)
  with Not_found -> 
    user_err_loc
      (loc,"",str ("Unknown interpretation for notation \""^ntn^"\""))

let uninterp_notations c =
  Gmapl.find (rawconstr_key c) !notations_key_table

let uninterp_cases_pattern_notations c =
  Gmapl.find (cases_pattern_key c) !notations_key_table

let availability_of_notation (ntn_scope,ntn) scopes =
  let f scope =
    Stringmap.mem ntn (Stringmap.find scope !scope_map).notations in
  find_without_delimiters f (ntn_scope,Some ntn) scopes

let rec interp_numeral_gen loc f n = function
  | scope :: scopes ->
      (try f (lookup_numeral_interpreter loc scope)
       with Not_found -> interp_numeral_gen loc f n scopes)
  | [] ->
      user_err_loc (loc,"interp_numeral",
      str "No interpretation for numeral " ++ pr_bigint n)

let interp_numeral loc n scopes =
  interp_numeral_gen loc (fun x -> fst x loc n) n
    (List.fold_right push_scope scopes !scope_stack)

let interp_numeral_as_pattern loc n name scopes =
  let f x = match snd x with
    | None -> raise Not_found
    | Some g -> g loc n name in
  interp_numeral_gen loc f n (List.fold_right push_scope scopes !scope_stack)

let uninterp_numeral c =
  try 
    let (sc,numpr,_) = Hashtbl.find numeral_key_table (rawconstr_key c) in
    match numpr c with
      | None -> raise No_match
      | Some n -> (sc,n)
  with Not_found -> raise No_match

let uninterp_cases_numeral c =
  try 
    match Hashtbl.find numeral_key_table (pattern_key c) with
      | (_,_,None) -> raise No_match
      | (sc,_,Some numpr) ->
	  match numpr c with
	    | None -> raise No_match
	    | Some n -> (sc,n)
  with Not_found -> raise No_match

let availability_of_numeral printer_scope scopes =
  let f scope = Hashtbl.mem numeral_interpreter_tab scope in
  option_app snd (find_without_delimiters f (Some printer_scope,None) scopes)

(* Miscellaneous *)

let exists_notation_in_scope scopt ntn r =
  let scope = match scopt with Some s -> s | None -> default_scope in
  try
    let sc = Stringmap.find scope !scope_map in
    let (r',_,pp8only) = Stringmap.find ntn sc.notations in
    r' = r, pp8only
  with Not_found -> false, false

(* Special scopes associated to arguments of a global reference *)

let arguments_scope = ref Refmap.empty

let cache_arguments_scope (_,(r,scl)) =
  List.iter (option_iter check_scope) scl;
  arguments_scope := Refmap.add r scl !arguments_scope

let subst_arguments_scope (_,subst,(r,scl)) = (subst_global subst r,scl)

let (inArgumentsScope,outArgumentsScope) = 
  declare_object {(default_object "ARGUMENTS-SCOPE") with
      cache_function = cache_arguments_scope;
      load_function = (fun _ o -> cache_arguments_scope o);
      subst_function = subst_arguments_scope;
      classify_function = (fun (_,o) -> Substitute o);
      export_function = (fun x -> Some x) }

let declare_arguments_scope r scl =
  Lib.add_anonymous_leaf (inArgumentsScope (r,scl))

let find_arguments_scope r =
  try Refmap.find r !arguments_scope
  with Not_found -> []

(**********************************************************************)
(* Mapping classes to scopes *)

open Classops

let class_scope_map = ref (Gmap.empty : (cl_typ,scope_name) Gmap.t)

let _ = Gmap.add CL_SORT "type_scope" Gmap.empty

let declare_class_scope sc cl =
  class_scope_map := Gmap.add cl sc !class_scope_map

let find_class_scope cl =
  Gmap.find cl !class_scope_map

open Term

let find_class t =
  let t, _ = decompose_app (Reductionops.whd_betaiotazeta t) in
  match kind_of_term t with
    | Var id -> CL_SECVAR id
    | Const sp -> CL_CONST sp
    | Ind ind_sp -> CL_IND ind_sp
    | Prod (_,_,_) -> CL_FUN
    | Sort _ -> CL_SORT
    |  _ -> raise Not_found

let rec compute_arguments_scope t =
  match kind_of_term (Reductionops.whd_betaiotazeta t) with
    | Prod (_,t,u) ->
	let sc =
	  try Some (find_class_scope (find_class t)) with Not_found -> None in
	sc :: compute_arguments_scope u
    | _ -> []

let declare_ref_arguments_scope ref =
  let t = Global.type_of_global ref in
  declare_arguments_scope ref (compute_arguments_scope t)

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
    if n>=len then dirs else
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

let rec rawconstr_of_aconstr () x =
  rawconstr_of_aconstr_with_binders dummy_loc (fun id () -> (id,())) 
    rawconstr_of_aconstr () x

let pr_notation_info prraw ntn c =
  str "\"" ++ str ntn ++ str "\" := " ++ prraw (rawconstr_of_aconstr () c)

let pr_named_scope prraw scope sc =
 (if scope = default_scope then
   match Stringmap.fold (fun _ _ x -> x+1) sc.notations 0 with
     | 0 -> str "No lonely notation"
     | n -> str "Lonely notation" ++ (if n=1 then mt() else str"s")
  else 
    str "Scope " ++ str scope ++ fnl () ++ pr_delimiters_info sc.delimiters)
  ++ fnl ()
  ++ pr_scope_classes scope
  ++ Stringmap.fold
       (fun ntn ((_,r),(_,df),_) strm ->
	 pr_notation_info prraw df r ++ fnl () ++ strm)
       sc.notations (mt ())

let pr_scope prraw scope = pr_named_scope prraw scope (find_scope scope)

let pr_scopes prraw =
 Stringmap.fold 
   (fun scope sc strm -> pr_named_scope prraw scope sc ++ fnl () ++ strm)
   !scope_map (mt ())

let rec find_default ntn = function
  | Scope scope::_ when Stringmap.mem ntn (find_scope scope).notations ->
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

let browse_notation ntn map =
  let find =
    if String.contains ntn ' ' then (=) ntn
    else fun ntn' -> List.mem (Terminal ntn) (decompose_notation_key ntn') in
  let l =
    Stringmap.fold 
      (fun scope_name sc ->
	Stringmap.fold (fun ntn ((_,r),df,_) l ->
	  if find ntn then (ntn,(scope_name,r,df))::l else l) sc.notations)
      map [] in
  let l = List.sort (fun x y -> Pervasives.compare (fst x) (fst y)) l in
  factorize_entries l

let locate_notation prraw ntn =
  let ntns = browse_notation ntn !scope_map in
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
  Stringmap.fold
    (fun ntn ((_,r),(_,df),_) (l,known as acc) ->
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
	    let ((_,r),(_,df),_) =
	      Stringmap.find ntn (find_scope default_scope).notations in
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
  ref (Stringmap.empty : unparsing_rule Stringmap.t)

let declare_notation_printing_rule ntn unpl =
  printing_rules := Stringmap.add ntn unpl !printing_rules

let find_notation_printing_rule ntn =
  try Stringmap.find ntn !printing_rules
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
  scope_stack := Stringmap.empty
  arguments_scope := Refmap.empty
*)
  notation_level_map := Stringmap.empty;
  delimiters_map := Stringmap.empty;
  notations_key_table := Gmapl.empty;
  printing_rules := Stringmap.empty;
  class_scope_map := Gmap.add CL_SORT "type_scope" Gmap.empty

let _ = 
  declare_summary "symbols"
    { freeze_function = freeze;
      unfreeze_function = unfreeze;
      init_function = init;
      survive_module = false;
      survive_section = false }
