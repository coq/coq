(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open CErrors
open Util
open Pp
open Bigint
open Names
open Term
open Libnames
open Globnames
open Constrexpr
open Notation_term
open Glob_term
open Glob_ops
open Ppextend
open Context.Named.Declaration

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
type notation_location = (DirPath.t * DirPath.t) * string

type notation_data = {
  not_interp : interpretation;
  not_location : notation_location;
  not_onlyprinting : bool;
}

type scope = {
  notations: notation_data String.Map.t;
  delimiters: delimiters option
}

(* Uninterpreted notation map: notation -> level * DirPath.t *)
let notation_level_map = ref String.Map.empty

(* Scopes table: scope_name -> symbol_interpretation *)
let scope_map = ref String.Map.empty

(* Delimiter table : delimiter -> scope_name *)
let delimiters_map = ref String.Map.empty

let empty_scope = {
  notations = String.Map.empty;
  delimiters = None
}

let default_scope = "" (* empty name, not available from outside *)

let init_scope_map () =
  scope_map := String.Map.add default_scope empty_scope !scope_map

(**********************************************************************)
(* Operations on scopes *)

let parenRelation_eq t1 t2 = match t1, t2 with
| L, L | E, E | Any, Any -> true
| Prec l1, Prec l2 -> Int.equal l1 l2
| _ -> false

let level_eq (l1, t1) (l2, t2) =
  let tolerability_eq (i1, r1) (i2, r2) =
    Int.equal i1 i2 && parenRelation_eq r1 r2
  in
  Int.equal l1 l2 && List.equal tolerability_eq t1 t2

let declare_scope scope =
  try let _ = String.Map.find scope !scope_map in ()
  with Not_found ->
(*    Flags.if_warn message ("Creating scope "^scope);*)
    scope_map := String.Map.add scope empty_scope !scope_map

let error_unknown_scope sc =
  user_err ~hdr:"Notation"
    (str "Scope " ++ str sc ++ str " is not declared.")

let find_scope scope =
  try String.Map.find scope !scope_map
  with Not_found -> error_unknown_scope scope

let check_scope sc = let _ = find_scope sc in ()

(* [sc] might be here a [scope_name] or a [delimiter]
   (now allowed after Open Scope) *)

let normalize_scope sc =
  try let _ = String.Map.find sc !scope_map in sc
  with Not_found ->
    try
      let sc = String.Map.find sc !delimiters_map in
      let _ = String.Map.find sc !scope_map in sc
    with Not_found -> error_unknown_scope sc

(**********************************************************************)
(* The global stack of scopes                                         *)

type scope_elem = Scope of scope_name | SingleNotation of string
type scopes = scope_elem list

let scope_eq s1 s2 = match s1, s2 with
| Scope s1, Scope s2
| SingleNotation s1, SingleNotation s2 -> String.equal s1 s2
| Scope _, SingleNotation _
| SingleNotation _, Scope _ -> false

let scope_stack = ref []

let current_scopes () = !scope_stack

let scope_is_open_in_scopes sc l =
  List.exists (function Scope sc' -> String.equal sc sc' | _ -> false) l

let scope_is_open sc = scope_is_open_in_scopes sc (!scope_stack)

(* TODO: push nat_scope, z_scope, ... in scopes summary *)

(* Exportation of scopes *)
let open_scope i (_,(local,op,sc)) =
  if Int.equal i 1 then
    scope_stack :=
      if op then sc :: !scope_stack
      else List.except scope_eq sc !scope_stack

let cache_scope o =
  open_scope 1 o

let subst_scope (subst,sc) = sc

open Libobject

let discharge_scope (_,(local,_,_ as o)) =
  if local then None else Some o

let classify_scope (local,_,_ as o) =
  if local then Dispose else Substitute o

let inScope : bool * bool * scope_elem -> obj =
  declare_object {(default_object "SCOPE") with
      cache_function = cache_scope;
      open_function = open_scope;
      subst_function = subst_scope;
      discharge_function = discharge_scope;
      classify_function = classify_scope }

let open_close_scope (local,opening,sc) =
  Lib.add_anonymous_leaf (inScope (local,opening,Scope (normalize_scope sc)))

let empty_scope_stack = []

let push_scope sc scopes = Scope sc :: scopes

let push_scopes = List.fold_right push_scope

type local_scopes = tmp_scope_name option * scope_name list

let make_current_scopes (tmp_scope,scopes) =
  Option.fold_right push_scope tmp_scope (push_scopes scopes !scope_stack)

(**********************************************************************)
(* Delimiters *)

let declare_delimiters scope key =
  let sc = find_scope scope in
  let newsc = { sc with delimiters = Some key } in
  begin match sc.delimiters with
    | None -> scope_map := String.Map.add scope newsc !scope_map
    | Some oldkey when String.equal oldkey key -> ()
    | Some oldkey ->
        (** FIXME: implement multikey scopes? *)
	Flags.if_verbose Feedback.msg_info
	  (str "Overwriting previous delimiting key " ++ str oldkey ++ str " in scope " ++ str scope);
	scope_map := String.Map.add scope newsc !scope_map
  end;
  try
    let oldscope = String.Map.find key !delimiters_map in
    if String.equal oldscope scope then ()
    else begin
      Flags.if_verbose Feedback.msg_info (str "Hiding binding of key " ++ str key ++ str " to " ++ str oldscope);
      delimiters_map := String.Map.add key scope !delimiters_map
    end
  with Not_found -> delimiters_map := String.Map.add key scope !delimiters_map

let remove_delimiters scope =
  let sc = find_scope scope in
  let newsc = { sc with delimiters = None } in
  match sc.delimiters with
    | None -> CErrors.user_err  (str "No bound key for scope " ++ str scope ++ str ".")
    | Some key ->
       scope_map := String.Map.add scope newsc !scope_map;
       try
         let _ = ignore (String.Map.find key !delimiters_map) in
         delimiters_map := String.Map.remove key !delimiters_map
       with Not_found ->
         assert false (* A delimiter for scope [scope] should exist *)

let find_delimiters_scope ?loc key =
  try String.Map.find key !delimiters_map
  with Not_found ->
    user_err ?loc ~hdr:"find_delimiters"
      (str "Unknown scope delimiting key " ++ str key ++ str ".")

(* Uninterpretation tables *)

type interp_rule =
  | NotationRule of scope_name option * notation
  | SynDefRule of kernel_name

(* We define keys for glob_constr and aconstr to split the syntax entries
   according to the key of the pattern (adapted from Chet Murthy by HH) *)

type key =
  | RefKey of global_reference
  | Oth

let key_compare k1 k2 = match k1, k2 with
| RefKey gr1, RefKey gr2 -> RefOrdered.compare gr1 gr2
| RefKey _, Oth -> -1
| Oth, RefKey _ -> 1
| Oth, Oth -> 0

module KeyOrd = struct type t = key let compare = key_compare end
module KeyMap = Map.Make(KeyOrd)

type notation_rule = interp_rule * interpretation * int option

let keymap_add key interp map =
  let old = try KeyMap.find key map with Not_found -> [] in
  KeyMap.add key (interp :: old) map

let keymap_find key map =
  try KeyMap.find key map
  with Not_found -> []

(* Scopes table : interpretation -> scope_name *)
let notations_key_table = ref (KeyMap.empty : notation_rule list KeyMap.t)

let prim_token_key_table = ref KeyMap.empty

let glob_prim_constr_key = function
  | { CAst.v = GApp ({ CAst.v = GRef (ref,_) } ,_) } | { CAst.v = GRef (ref,_) } -> RefKey (canonical_gr ref)
  | _ -> Oth

let glob_constr_keys = function
  | { CAst.v = GApp ({ CAst.v = GRef (ref,_) },_) } -> [RefKey (canonical_gr ref); Oth]
  | { CAst.v = GRef (ref,_) } -> [RefKey (canonical_gr ref)]
  | _ -> [Oth]

let cases_pattern_key = function
  | { CAst.v = PatCstr (ref,_,_) } -> RefKey (canonical_gr (ConstructRef ref))
  | _ -> Oth

let notation_constr_key = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef ref,args) -> RefKey(canonical_gr ref), Some (List.length args)
  | NList (_,_,NApp (NRef ref,args),_,_)
  | NBinderList (_,_,NApp (NRef ref,args),_) ->
      RefKey (canonical_gr ref), Some (List.length args)
  | NRef ref -> RefKey(canonical_gr ref), None
  | NApp (_,args) -> Oth, Some (List.length args)
  | _ -> Oth, None

(**********************************************************************)
(* Interpreting numbers (not in summary because functional objects)   *)

type required_module = full_path * string list

type 'a prim_token_interpreter =
    ?loc:Loc.t -> 'a -> glob_constr

type cases_pattern_status = bool (* true = use prim token in patterns *)

type 'a prim_token_uninterpreter =
    glob_constr list * (glob_constr -> 'a option) * cases_pattern_status

type internal_prim_token_interpreter =
    ?loc:Loc.t -> prim_token -> required_module * (unit -> glob_constr)

let prim_token_interpreter_tab =
  (Hashtbl.create 7 : (scope_name, internal_prim_token_interpreter) Hashtbl.t)

let add_prim_token_interpreter sc interp =
  try
    let cont = Hashtbl.find prim_token_interpreter_tab sc in
    Hashtbl.replace prim_token_interpreter_tab sc (interp cont)
  with Not_found ->
    let cont = (fun ?loc _p -> raise Not_found) in
    Hashtbl.add prim_token_interpreter_tab sc (interp cont)

let declare_prim_token_interpreter sc interp (patl,uninterp,b) =
  declare_scope sc;
  add_prim_token_interpreter sc interp;
  List.iter (fun pat ->
      prim_token_key_table := KeyMap.add
        (glob_prim_constr_key pat) (sc,uninterp,b) !prim_token_key_table)
    patl

let mkNumeral n = Numeral n
let mkString = function
| None -> None
| Some s -> if Unicode.is_utf8 s then Some (String s) else None

let delay dir int ?loc x = (dir, (fun () -> int ?loc x))

let declare_numeral_interpreter sc dir interp (patl,uninterp,inpat) =
  declare_prim_token_interpreter sc
    (fun cont ?loc -> function Numeral n-> delay dir interp ?loc n | p -> cont ?loc p)
    (patl, (fun r -> Option.map mkNumeral (uninterp r)), inpat)

let declare_string_interpreter sc dir interp (patl,uninterp,inpat) =
  declare_prim_token_interpreter sc
    (fun cont ?loc -> function String s -> delay dir interp ?loc s | p -> cont ?loc p)
    (patl, (fun r -> mkString (uninterp r)), inpat)

let check_required_module ?loc sc (sp,d) =
  try let _ = Nametab.global_of_path sp in ()
  with Not_found ->
    user_err ?loc ~hdr:"prim_token_interpreter"
    (str "Cannot interpret in " ++ str sc ++ str " without requiring first module " ++ str (List.last d) ++ str ".")

(* Look if some notation or numeral printer in [scope] can be used in
   the scope stack [scopes], and if yes, using delimiters or not *)

let find_with_delimiters = function
  | None -> None
  | Some scope ->
      match (String.Map.find scope !scope_map).delimiters with
	| Some key -> Some (Some scope, Some key)
	| None -> None

let rec find_without_delimiters find (ntn_scope,ntn) = function
  | Scope scope :: scopes ->
      (* Is the expected ntn/numpr attached to the most recently open scope? *)
      begin match ntn_scope with
      | Some scope' when String.equal scope scope' ->
	Some (None,None)
      | _ ->
	(* If the most recently open scope has a notation/numeral printer
    	   but not the expected one then we need delimiters *)
	if find scope then
	  find_with_delimiters ntn_scope
	else
	  find_without_delimiters find (ntn_scope,ntn) scopes
      end
  | SingleNotation ntn' :: scopes ->
      begin match ntn_scope, ntn with
      | None, Some ntn when String.equal ntn ntn' ->
	Some (None, None)
      | _ ->
	find_without_delimiters find (ntn_scope,ntn) scopes
      end
  | [] ->
      (* Can we switch to [scope]? Yes if it has defined delimiters *)
      find_with_delimiters ntn_scope

(* Uninterpreted notation levels *)

let declare_notation_level ntn level =
  if String.Map.mem ntn !notation_level_map then
    anomaly (str "Notation " ++ str ntn ++ str " is already assigned a level");
  notation_level_map := String.Map.add ntn level !notation_level_map

let level_of_notation ntn =
  String.Map.find ntn !notation_level_map

(* The mapping between notations and their interpretation *)

let warn_notation_overridden =
  CWarnings.create ~name:"notation-overridden" ~category:"parsing"
                   (fun (ntn,which_scope) ->
                    str "Notation" ++ spc () ++ str ntn ++ spc ()
                    ++ strbrk "was already used" ++ which_scope)

let declare_notation_interpretation ntn scopt pat df ~onlyprint =
  let scope = match scopt with Some s -> s | None -> default_scope in
  let sc = find_scope scope in
  let () =
    if String.Map.mem ntn sc.notations then
    let which_scope = match scopt with
    | None -> mt ()
    | Some _ -> spc () ++ strbrk "in scope" ++ spc () ++ str scope in
    warn_notation_overridden (ntn,which_scope)
  in
  let notdata = {
    not_interp = pat;
    not_location = df;
    not_onlyprinting = onlyprint;
  } in
  let sc = { sc with notations = String.Map.add ntn notdata sc.notations } in
  let () = scope_map := String.Map.add scope sc !scope_map in
  begin match scopt with
  | None -> scope_stack := SingleNotation ntn :: !scope_stack
  | Some _ -> ()
  end

let declare_uninterpretation rule (metas,c as pat) =
  let (key,n) = notation_constr_key c in
  notations_key_table := keymap_add key (rule,pat,n) !notations_key_table

let rec find_interpretation ntn find = function
  | [] -> raise Not_found
  | Scope scope :: scopes ->
      (try let (pat,df) = find scope in pat,(df,Some scope)
       with Not_found -> find_interpretation ntn find scopes)
  | SingleNotation ntn'::scopes when String.equal ntn' ntn ->
      (try let (pat,df) = find default_scope in pat,(df,None)
       with Not_found ->
         (* e.g. because single notation only for constr, not cases_pattern *)
         find_interpretation ntn find scopes)
  | SingleNotation _::scopes ->
      find_interpretation ntn find scopes

let find_notation ntn sc =
  let n = String.Map.find ntn (find_scope sc).notations in
  let () = if n.not_onlyprinting then raise Not_found in
  (n.not_interp, n.not_location)

let notation_of_prim_token = function
  | Numeral n when is_pos_or_zero n -> to_string n
  | Numeral n -> "- "^(to_string (neg n))
  | String _ -> raise Not_found

let find_prim_token check_allowed ?loc p sc =
  (* Try for a user-defined numerical notation *)
  try
    let (_,c),df = find_notation (notation_of_prim_token p) sc in
    let pat = Notation_ops.glob_constr_of_notation_constr ?loc c in
    check_allowed pat;
    pat, df
  with Not_found ->
  (* Try for a primitive numerical notation *)
  let (spdir,interp) = Hashtbl.find prim_token_interpreter_tab sc ?loc p in
  check_required_module ?loc sc spdir;
  let pat = interp () in
  check_allowed pat;
  pat, ((dirpath (fst spdir),DirPath.empty),"")

let interp_prim_token_gen ?loc g p local_scopes =
  let scopes = make_current_scopes local_scopes in
  let p_as_ntn = try notation_of_prim_token p with Not_found -> "" in
  try find_interpretation p_as_ntn (find_prim_token ?loc g p) scopes
  with Not_found ->
    user_err ?loc ~hdr:"interp_prim_token"
    ((match p with
      | Numeral n -> str "No interpretation for numeral " ++ str (to_string n)
      | String s -> str "No interpretation for string " ++ qs s) ++ str ".")

let interp_prim_token ?loc =
  interp_prim_token_gen ?loc (fun _ -> ())

let rec check_allowed_ref_in_pat looked_for = CAst.(with_val (function
  | GVar _ | GHole _ -> ()
  | GRef (g,_) -> looked_for g
  | GApp ({ v = GRef (g,_) },l) ->
    looked_for g; List.iter (check_allowed_ref_in_pat looked_for) l
  | _ -> raise Not_found))

let interp_prim_token_cases_pattern_expr ?loc looked_for p =
  interp_prim_token_gen ?loc (check_allowed_ref_in_pat looked_for) p

let interp_notation ?loc ntn local_scopes =
  let scopes = make_current_scopes local_scopes in
  try find_interpretation ntn (find_notation ntn) scopes
  with Not_found ->
    user_err ?loc 
    (str "Unknown interpretation for notation \"" ++ str ntn ++ str "\".")

let uninterp_notations c =
  List.map_append (fun key -> keymap_find key !notations_key_table)
    (glob_constr_keys c)

let uninterp_cases_pattern_notations c =
  keymap_find (cases_pattern_key c) !notations_key_table

let uninterp_ind_pattern_notations ind =
  keymap_find (RefKey (canonical_gr (IndRef ind))) !notations_key_table

let availability_of_notation (ntn_scope,ntn) scopes =
  let f scope =
    String.Map.mem ntn (String.Map.find scope !scope_map).notations in
  find_without_delimiters f (ntn_scope,Some ntn) (make_current_scopes scopes)

let uninterp_prim_token c =
  try
    let (sc,numpr,_) =
      KeyMap.find (glob_prim_constr_key c) !prim_token_key_table in
    match numpr c with
      | None -> raise Notation_ops.No_match
      | Some n -> (sc,n)
  with Not_found -> raise Notation_ops.No_match

let uninterp_prim_token_ind_pattern ind args =
  let ref = IndRef ind in
  try
    let k = RefKey (canonical_gr ref) in
    let (sc,numpr,b) = KeyMap.find k !prim_token_key_table in
    if not b then raise Notation_ops.No_match;
    let args' = List.map
      (fun x -> snd (glob_constr_of_closed_cases_pattern x)) args in
    let ref = CAst.make @@ GRef (ref,None) in
    match numpr (CAst.make @@ GApp (ref,args')) with
      | None -> raise Notation_ops.No_match
      | Some n -> (sc,n)
  with Not_found -> raise Notation_ops.No_match

let uninterp_prim_token_cases_pattern c =
  try
    let k = cases_pattern_key c in
    let (sc,numpr,b) = KeyMap.find k !prim_token_key_table in
    if not b then raise Notation_ops.No_match;
    let na,c = glob_constr_of_closed_cases_pattern c in
    match numpr c with
      | None -> raise Notation_ops.No_match
      | Some n -> (na,sc,n)
  with Not_found -> raise Notation_ops.No_match

let availability_of_prim_token n printer_scope local_scopes =
  let f scope =
    try ignore ((Hashtbl.find prim_token_interpreter_tab scope) n); true
    with Not_found -> false in
  let scopes = make_current_scopes local_scopes in
  Option.map snd (find_without_delimiters f (Some printer_scope,None) scopes)

(* Miscellaneous *)

let pair_eq f g (x1, y1) (x2, y2) = f x1 x2 && g y1 y2

let ntpe_eq t1 t2 = match t1, t2 with
| NtnTypeConstr, NtnTypeConstr -> true
| NtnTypeOnlyBinder, NtnTypeOnlyBinder -> true
| NtnTypeConstrList, NtnTypeConstrList -> true
| NtnTypeBinderList, NtnTypeBinderList -> true
| (NtnTypeConstr | NtnTypeOnlyBinder | NtnTypeConstrList | NtnTypeBinderList), _ -> false

let var_attributes_eq (_, (sc1, tp1)) (_, (sc2, tp2)) =
  pair_eq (Option.equal String.equal) (List.equal String.equal) sc1 sc2 &&
  ntpe_eq tp1 tp2

let interpretation_eq (vars1, t1) (vars2, t2) =
  List.equal var_attributes_eq vars1 vars2 &&
  Notation_ops.eq_notation_constr (List.map fst vars1, List.map fst vars2) t1 t2

let exists_notation_in_scope scopt ntn r =
  let scope = match scopt with Some s -> s | None -> default_scope in
  try
    let sc = String.Map.find scope !scope_map in
    let n = String.Map.find ntn sc.notations in
    interpretation_eq n.not_interp r
  with Not_found -> false

let isNVar_or_NHole = function NVar _ | NHole _ -> true | _ -> false

(**********************************************************************)
(* Mapping classes to scopes *)

open Classops

type scope_class = cl_typ

let scope_class_compare : scope_class -> scope_class -> int =
  cl_typ_ord

let compute_scope_class t =
  let (cl,_,_) = find_class_type Evd.empty (EConstr.of_constr t) in
  cl

module ScopeClassOrd =
struct
  type t = scope_class
  let compare = scope_class_compare
end

module ScopeClassMap = Map.Make(ScopeClassOrd)

let initial_scope_class_map : scope_name ScopeClassMap.t =
  ScopeClassMap.empty

let scope_class_map = ref initial_scope_class_map

let declare_scope_class sc cl =
  scope_class_map := ScopeClassMap.add cl sc !scope_class_map

let find_scope_class cl =
  ScopeClassMap.find cl !scope_class_map

let find_scope_class_opt = function
  | None -> None
  | Some cl -> try Some (find_scope_class cl) with Not_found -> None

(**********************************************************************)
(* Special scopes associated to arguments of a global reference *)

let rec compute_arguments_classes t =
  match kind_of_term (EConstr.Unsafe.to_constr (Reductionops.whd_betaiotazeta Evd.empty (EConstr.of_constr t))) with
    | Prod (_,t,u) ->
	let cl = try Some (compute_scope_class t) with Not_found -> None in
	cl :: compute_arguments_classes u
    | _ -> []

let compute_arguments_scope_full t =
  let cls = compute_arguments_classes t in
  let scs = List.map find_scope_class_opt cls in
  scs, cls

let compute_arguments_scope t = fst (compute_arguments_scope_full t)

let compute_type_scope t =
  find_scope_class_opt (try Some (compute_scope_class t) with Not_found -> None)

let current_type_scope_name () =
   find_scope_class_opt (Some CL_SORT)

let scope_class_of_class (x : cl_typ) : scope_class =
  x

(** Updating a scope list, thanks to a list of argument classes
    and the current Bind Scope base. When some current scope
    have been manually given, the corresponding argument class
    is emptied below, so this manual scope will be preserved. *)

let update_scope cl sco =
  match find_scope_class_opt cl with
  | None -> sco
  | sco' -> sco'

let rec update_scopes cls scl = match cls, scl with
  | [], _ -> scl
  | _, [] -> List.map find_scope_class_opt cls
  | cl :: cls, sco :: scl -> update_scope cl sco :: update_scopes cls scl

let arguments_scope = ref Refmap.empty

type arguments_scope_discharge_request =
  | ArgsScopeAuto
  | ArgsScopeManual
  | ArgsScopeNoDischarge

let load_arguments_scope _ (_,(_,r,n,scl,cls)) =
  List.iter (Option.iter check_scope) scl;
  let initial_stamp = ScopeClassMap.empty in
  arguments_scope := Refmap.add r (scl,cls,initial_stamp) !arguments_scope

let cache_arguments_scope o =
  load_arguments_scope 1 o

let subst_scope_class subst cs =
  try Some (subst_cl_typ subst cs) with Not_found -> None

let subst_arguments_scope (subst,(req,r,n,scl,cls)) =
  let r' = fst (subst_global subst r) in
  let subst_cl ocl = match ocl with
    | None -> ocl
    | Some cl ->
        match subst_scope_class subst cl with
        | Some cl'  as ocl' when cl' != cl -> ocl'
        | _ -> ocl in
  let cls' = List.smartmap subst_cl cls in
  (ArgsScopeNoDischarge,r',n,scl,cls')

let discharge_arguments_scope (_,(req,r,n,l,_)) =
  if req == ArgsScopeNoDischarge || (isVarRef r && Lib.is_in_section r) then None
  else
    let n =
      try
        let vars = Lib.variable_section_segment_of_reference r in
        vars |> List.map fst |> List.filter is_local_assum |> List.length
      with
        Not_found (* Not a ref defined in this section *) -> 0 in
    Some (req,Lib.discharge_global r,n,l,[])

let classify_arguments_scope (req,_,_,_,_ as obj) =
  if req == ArgsScopeNoDischarge then Dispose else Substitute obj

let rebuild_arguments_scope (req,r,n,l,_) =
  match req with
    | ArgsScopeNoDischarge -> assert false
    | ArgsScopeAuto ->
        let scs,cls = compute_arguments_scope_full (fst(Universes.type_of_global r)(*FIXME?*)) in
	(req,r,List.length scs,scs,cls)
    | ArgsScopeManual ->
	(* Add to the manually given scopes the one found automatically
           for the extra parameters of the section. Discard the classes
           of the manually given scopes to avoid further re-computations. *)
        let l',cls = compute_arguments_scope_full (Global.type_of_global_unsafe r) in
	let l1 = List.firstn n l' in
        let cls1 = List.firstn n cls in
	(req,r,0,l1@l,cls1)

type arguments_scope_obj =
    arguments_scope_discharge_request * global_reference *
    (* Used to communicate information from discharge to rebuild *)
    (* set to 0 otherwise *) int *
    scope_name option list * scope_class option list

let inArgumentsScope : arguments_scope_obj -> obj =
  declare_object {(default_object "ARGUMENTS-SCOPE") with
      cache_function = cache_arguments_scope;
      load_function = load_arguments_scope;
      subst_function = subst_arguments_scope;
      classify_function = classify_arguments_scope;
      discharge_function = discharge_arguments_scope;
      rebuild_function = rebuild_arguments_scope }

let is_local local ref = local || isVarRef ref && Lib.is_in_section ref

let declare_arguments_scope_gen req r n (scl,cls) =
  Lib.add_anonymous_leaf (inArgumentsScope (req,r,n,scl,cls))

let declare_arguments_scope local r scl =
  let req = if is_local local r then ArgsScopeNoDischarge else ArgsScopeManual in
  (* We empty the list of argument classes to disable further scope
     re-computations and keep these manually given scopes. *)
  declare_arguments_scope_gen req r 0 (scl,[])
                              
let find_arguments_scope r =
  try
    let (scl,cls,stamp) = Refmap.find r !arguments_scope in
    let cur_stamp = !scope_class_map in
    if stamp == cur_stamp then scl
    else
      (* Recent changes in the Bind Scope base, we re-compute the scopes *)
      let scl' = update_scopes cls scl in
      arguments_scope := Refmap.add r (scl',cls,cur_stamp) !arguments_scope;
      scl'
  with Not_found -> []

let declare_ref_arguments_scope ref =
  let t = Global.type_of_global_unsafe ref in
  let (scs,cls as o) = compute_arguments_scope_full t in
  declare_arguments_scope_gen ArgsScopeAuto ref (List.length scs) o


(********************************)
(* Encoding notations as string *)

type symbol =
  | Terminal of string
  | NonTerminal of Id.t
  | SProdList of Id.t * symbol list
  | Break of int

let rec symbol_eq s1 s2 = match s1, s2 with
| Terminal s1, Terminal s2 -> String.equal s1 s2
| NonTerminal id1, NonTerminal id2 -> Id.equal id1 id2
| SProdList (id1, l1), SProdList (id2, l2) ->
  Id.equal id1 id2 && List.equal symbol_eq l1 l2
| Break i1, Break i2 -> Int.equal i1 i2
| _ -> false

let rec string_of_symbol = function
  | NonTerminal _ -> ["_"]
  | Terminal "_" -> ["'_'"]
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
      | "_" -> NonTerminal (Id.of_string "_")
      | s -> Terminal (String.drop_simple_quotes s) in
    decomp_ntn (tok::dirs) (pos+1)
  in
    decomp_ntn [] 0

(************)
(* Printing *)

let pr_delimiters_info = function
  | None -> str "No delimiting key"
  | Some key -> str "Delimiting key is " ++ str key

let classes_of_scope sc =
  ScopeClassMap.fold (fun cl sc' l -> if String.equal sc sc' then cl::l else l) !scope_class_map []

let pr_scope_class = pr_class

let pr_scope_classes sc =
  let l = classes_of_scope sc in
  match l with
  | [] -> mt ()
  | _ :: ll ->
    let opt_s = match ll with [] -> mt () | _ -> str "es" in
    hov 0 (str "Bound to class" ++ opt_s ++
      spc() ++ prlist_with_sep spc pr_scope_class l) ++ fnl()

let pr_notation_info prglob ntn c =
  str "\"" ++ str ntn ++ str "\" := " ++
  prglob (Notation_ops.glob_constr_of_notation_constr c)

let pr_named_scope prglob scope sc =
 (if String.equal scope default_scope then
   match String.Map.cardinal sc.notations with
     | 0 -> str "No lonely notation"
     | n -> str "Lonely notation" ++ (if Int.equal n 1 then mt() else str"s")
  else
    str "Scope " ++ str scope ++ fnl () ++ pr_delimiters_info sc.delimiters)
  ++ fnl ()
  ++ pr_scope_classes scope
  ++ String.Map.fold
       (fun ntn { not_interp  = (_, r); not_location = (_, df) } strm ->
	 pr_notation_info prglob df r ++ fnl () ++ strm)
       sc.notations (mt ())

let pr_scope prglob scope = pr_named_scope prglob scope (find_scope scope)

let pr_scopes prglob =
 String.Map.fold
   (fun scope sc strm -> pr_named_scope prglob scope sc ++ fnl () ++ strm)
   !scope_map (mt ())

let rec find_default ntn = function
  | [] -> None
  | Scope scope :: scopes ->
    if String.Map.mem ntn (find_scope scope).notations then
      Some scope
    else find_default ntn scopes
  | SingleNotation ntn' :: scopes ->
    if String.equal ntn ntn' then Some default_scope
    else find_default ntn scopes

let factorize_entries = function
  | [] -> []
  | (ntn,c)::l ->
      let (ntn,l_of_ntn,rest) =
	List.fold_left
          (fun (a',l,rest) (a,c) ->
	    if String.equal a a' then (a',c::l,rest) else (a,[c],(a',l)::rest))
	  (ntn,[c],[]) l in
      (ntn,l_of_ntn)::rest

let browse_notation strict ntn map =
  let find ntn' =
    if String.contains ntn ' ' then String.equal ntn ntn'
    else
      let toks = decompose_notation_key ntn' in
      let get_terminals = function Terminal ntn -> Some ntn | _ -> None in
      let trms = List.map_filter get_terminals toks in
      if strict then String.List.equal [ntn] trms
      else String.List.mem ntn trms
  in
  let l =
    String.Map.fold
      (fun scope_name sc ->
	String.Map.fold (fun ntn { not_interp  = (_, r); not_location = df } l ->
	  if find ntn then (ntn,(scope_name,r,df))::l else l) sc.notations)
      map [] in
  List.sort (fun x y -> String.compare (fst x) (fst y)) l

let global_reference_of_notation test (ntn,(sc,c,_)) =
  match c with
  | NRef ref when test ref -> Some (ntn,sc,ref)
  | NApp (NRef ref, l) when List.for_all isNVar_or_NHole l && test ref ->
      Some (ntn,sc,ref)
  | _ -> None

let error_ambiguous_notation ?loc _ntn =
  user_err ?loc (str "Ambiguous notation.")

let error_notation_not_reference ?loc ntn =
  user_err ?loc 
   (str "Unable to interpret " ++ quote (str ntn) ++
    str " as a reference.")

let interp_notation_as_global_reference ?loc test ntn sc =
  let scopes = match sc with
  | Some sc ->
      let scope = find_scope (find_delimiters_scope sc) in
      String.Map.add sc scope String.Map.empty
  | None -> !scope_map in
  let ntns = browse_notation true ntn scopes in
  let refs = List.map (global_reference_of_notation test) ntns in
  match Option.List.flatten refs with
  | [_,_,ref] -> ref
  | [] -> error_notation_not_reference ?loc ntn
  | refs ->
      let f (ntn,sc,ref) =
        let def = find_default ntn !scope_stack in
        match def with
        | None -> false
        | Some sc' -> String.equal sc sc'
      in
      match List.filter f refs with
      | [_,_,ref] -> ref
      | [] -> error_notation_not_reference ?loc ntn
      | _ -> error_ambiguous_notation ?loc ntn

let locate_notation prglob ntn scope =
  let ntns = factorize_entries (browse_notation false ntn !scope_map) in
  let scopes = Option.fold_right push_scope scope !scope_stack in
  match ntns with
  | [] -> str "Unknown notation"
  | _ ->
    str "Notation" ++ fnl () ++
    prlist (fun (ntn,l) ->
      let scope = find_default ntn scopes in
      prlist
	(fun (sc,r,(_,df)) ->
	  hov 0 (
	    pr_notation_info prglob df r ++
	    (if String.equal sc default_scope then mt ()
             else (spc () ++ str ": " ++ str sc)) ++
	    (if Option.equal String.equal (Some sc) scope
             then spc () ++ str "(default interpretation)" else mt ())
	    ++ fnl ()))
	l) ntns

let collect_notation_in_scope scope sc known =
  assert (not (String.equal scope default_scope));
  String.Map.fold
    (fun ntn { not_interp  = (_, r); not_location = (_, df) } (l,known as acc) ->
      if String.List.mem ntn known then acc else ((df,r)::l,ntn::known))
    sc.notations ([],known)

let collect_notations stack =
  fst (List.fold_left
    (fun (all,knownntn as acc) -> function
      | Scope scope ->
	  if String.List.mem_assoc scope all then acc
	  else
	    let (l,knownntn) =
	      collect_notation_in_scope scope (find_scope scope) knownntn in
	    ((scope,l)::all,knownntn)
      | SingleNotation ntn ->
	  if String.List.mem ntn knownntn then (all,knownntn)
	  else
	    let { not_interp  = (_, r); not_location = (_, df) } =
	      String.Map.find ntn (find_scope default_scope).notations in
	    let all' = match all with
	      | (s,lonelyntn)::rest when String.equal s default_scope ->
		  (s,(df,r)::lonelyntn)::rest
	      | _ ->
		  (default_scope,[df,r])::all in
	    (all',ntn::knownntn))
    ([],[]) stack)

let pr_visible_in_scope prglob (scope,ntns) =
  let strm =
    List.fold_right
      (fun (df,r) strm -> pr_notation_info prglob df r ++ fnl () ++ strm)
      ntns (mt ()) in
  (if String.equal scope default_scope then
     str "Lonely notation" ++ (match ntns with [_] -> mt () | _ -> str "s")
   else
     str "Visible in scope " ++ str scope)
  ++ fnl () ++ strm

let pr_scope_stack prglob stack =
  List.fold_left
    (fun strm scntns -> strm ++ pr_visible_in_scope prglob scntns ++ fnl ())
    (mt ()) (collect_notations stack)

let pr_visibility prglob = function
  | Some scope -> pr_scope_stack prglob (push_scope scope !scope_stack)
  | None -> pr_scope_stack prglob !scope_stack

(**********************************************************************)
(* Mapping notations to concrete syntax *)

type unparsing_rule = unparsing list * precedence
type extra_unparsing_rules = (string * string) list
(* Concrete syntax for symbolic-extension table *)
let notation_rules =
  ref (String.Map.empty : (unparsing_rule * extra_unparsing_rules * notation_grammar) String.Map.t)

let declare_notation_rule ntn ~extra unpl gram =
  notation_rules := String.Map.add ntn (unpl,extra,gram) !notation_rules

let find_notation_printing_rule ntn =
  try pi1 (String.Map.find ntn !notation_rules)
  with Not_found -> anomaly (str "No printing rule found for " ++ str ntn)
let find_notation_extra_printing_rules ntn =
  try pi2 (String.Map.find ntn !notation_rules)
  with Not_found -> []
let find_notation_parsing_rules ntn =
  try pi3 (String.Map.find ntn !notation_rules)
  with Not_found -> anomaly (str "No parsing rule found for " ++ str ntn)

let get_defined_notations () =
  String.Set.elements @@ String.Map.domain !notation_rules

let add_notation_extra_printing_rule ntn k v =
  try
    notation_rules :=
      let p, pp, gr = String.Map.find ntn !notation_rules in
      String.Map.add ntn (p, (k,v) :: pp, gr) !notation_rules
  with Not_found ->
    user_err ~hdr:"add_notation_extra_printing_rule"
      (str "No such Notation.")

(**********************************************************************)
(* Synchronisation with reset *)

let freeze _ =
 (!scope_map, !notation_level_map, !scope_stack, !arguments_scope,
  !delimiters_map, !notations_key_table, !notation_rules,
  !scope_class_map)

let unfreeze (scm,nlm,scs,asc,dlm,fkm,pprules,clsc) =
  scope_map := scm;
  notation_level_map := nlm;
  scope_stack := scs;
  delimiters_map := dlm;
  arguments_scope := asc;
  notations_key_table := fkm;
  notation_rules := pprules;
  scope_class_map := clsc

let init () =
  init_scope_map ();
  notation_level_map := String.Map.empty;
  delimiters_map := String.Map.empty;
  notations_key_table := KeyMap.empty;
  notation_rules := String.Map.empty;
  scope_class_map := initial_scope_class_map

let _ =
  Summary.declare_summary "symbols"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let with_notation_protection f x =
  let fs = freeze false in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = CErrors.push reraise in
    let () = unfreeze fs in
    iraise reraise
