(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Options
open Names
open Nameops
open Sign
open Term
open Termops
open Environ
open Evd
open Reductionops
open Libnames
open Impargs
open Declare
open Rawterm
open Pattern
open Typing
open Pretyping
open Evarutil
open Ast
open Coqast
open Nametab

(*Takes a list of variables which must not be globalized*)
let from_list l = List.fold_right Idset.add l Idset.empty

(* when an head ident is not a constructor in pattern *)
let mssg_hd_is_not_constructor s =
  (str "The symbol " ++ pr_id s ++ str " should be a constructor")

(* checking linearity of a list of ids in patterns *)
let non_linearl_mssg id =
  (str "The variable " ++ str(string_of_id id) ++
     str " is bound several times in pattern") 

let error_capture_loc loc s =
  user_err_loc
    (loc,"ast_to_rawconstr", 
     (str "The variable " ++ pr_id s ++ str " occurs in its type"))

let error_expl_impl_loc loc =
  user_err_loc
    (loc,"ast_to_rawconstr", 
     (str "Found an explicitely given implicit argument but was expecting" ++
	fnl () ++ str "a regular one"))

let error_metavar_loc loc =
  user_err_loc
    (loc,"ast_to_rawconstr", 
     (str "Metavariable numbers must be positive"))

let rec has_duplicate = function 
  | [] -> None
  | x::l -> if List.mem x l then (Some x) else has_duplicate l

let loc_of_lhs lhs = join_loc (loc (List.hd lhs)) (loc (list_last lhs))

let check_linearity lhs ids =
  match has_duplicate ids with
    | Some id -> 
	user_err_loc (loc_of_lhs lhs,"ast_to_eqn",non_linearl_mssg id)
    | None -> ()

let mal_formed_mssg () =
  (str "malformed macro of multiple case")

(* determines if some pattern variable starts with uppercase *)
let warning_uppercase loc uplid = (* Comment afficher loc ?? *)
  let vars =
    prlist_with_sep 
      (fun () -> (str ", ")) (* We avoid spc (), else it breaks the line *)
      (fun v -> (str (string_of_id v))) uplid in
  let (s1,s2) = if List.length uplid = 1 then (" ","s ") else ("s "," ") in
  warn (str ("the variable"^s1) ++ vars ++
	str (" start"^s2^"with an upper case letter in pattern"))

let is_uppercase_var v =
 match (string_of_id v).[0] with
    'A'..'Z' -> true
 | _  -> false

let check_uppercase loc ids =
(* A quoi ça sert ? Pour l'extraction vers ML ? Maintenant elle est externe
  let uplid = List.filter is_uppercase_var ids in
  if uplid <> [] then warning_uppercase loc uplid
*)
  ()

(* check that the number of pattern matches the number of matched args *)
let mssg_number_of_patterns n pl =
  str"Expecting " ++ int n  ++ str" pattern(s) but found " ++
  int (List.length pl) ++ str" in "

let check_number_of_pattern loc n l =
  if n<>(List.length l) then
    user_err_loc (loc,"check_number_of_pattern",mssg_number_of_patterns n l)

(****************************************************************)
(* Arguments normally implicit in the "Implicit Arguments mode" *)
(* but explicitely given                                        *)

(* Dump of globalization (to be used by coqdoc) *)

let add_glob loc ref = 
(*i
  let sp = Nametab.sp_of_global (Global.env ()) ref in
  let dir,_ = repr_path sp in
  let rec find_module d = 
    try 
      let qid = let dir,id = split_dirpath d in make_qualid dir id in
      let _ = Nametab.locate_loaded_library qid in d
    with Not_found -> find_module (dirpath_prefix d) 
  in
  let s = string_of_dirpath (find_module dir) in
  i*)
  let sp = Nametab.sp_of_global None ref in
  let id = let _,id = repr_path sp in string_of_id id in
  let dp = string_of_dirpath (Declare.library_part ref) in
  dump_string (Printf.sprintf "R%d %s.%s\n" (fst loc) dp id)

(* Translation of references *)

let ast_to_sp = function
  | Path(loc,sp) ->
      (try 
	 section_path sp
       with Invalid_argument _ | Failure _ ->
         anomaly_loc(loc,"Astterm.ast_to_sp",
                     (str"ill-formed section-path")))
  | ast -> anomaly_loc(Ast.loc ast,"Astterm.ast_to_sp",
                     (str"not a section-path"))

(* TODO: correct this vulgar hack! *)
let sp_of_kn kn = 
  match repr_kn kn with
    | MPfile dir, _, l -> make_path dir (id_of_label l)
    | _ -> anomaly "MPcomp module path expected"

let kn_of_sp sp = 
  Libnames.encode_kn (dirpath sp) (basename sp)

let is_underscore id = (id = wildcard)

let name_of_nvar s =
  if is_underscore s then Anonymous else Name s

let ident_of_nvar loc s =
  if is_underscore s then
    user_err_loc (loc,"ident_of_nvar", (str "Unexpected wildcard"))
  else s

let interp_qualid p =
  let outnvar = function
    | Nvar (loc,s) -> s
    | _ -> anomaly "interp_qualid: ill-formed qualified identifier" in
  match p with
    | [] -> anomaly "interp_qualid: empty qualified identifier"
    | l -> 
	let p, r = list_chop (List.length l -1) (List.map outnvar l) in
	make_qualid (make_dirpath (List.rev p)) (List.hd r)

let maybe_variable = function
  | [Nvar (_,s)] -> Some s
  | _ -> None

let ids_of_ctxt ctxt =
  Array.to_list
    (Array.map
       (function c -> match kind_of_term c with
	  | Var id -> id
	  | _ ->
      error
	"Astterm: arbitrary substitution of references not yet implemented")
    ctxt)

type pattern_qualid_kind =
  | ConstrPat of loc * constructor
  | VarPat of loc * identifier

let maybe_constructor env = function
  | Node(loc,"QUALID",l) ->
      let qid = interp_qualid l in
      (try 
	match kind_of_term (global_qualified_reference qid) with 
	  | Construct c -> 
	      if !dump then add_glob loc (ConstructRef c); 
	      ConstrPat (loc,c)
	  | _ -> 
	      (match maybe_variable l with
		 | Some s -> 
		     warning ("Defined reference "^(string_of_qualid qid)
			      ^" is here considered as a matching variable");
		     VarPat (loc,s)
		 | _ -> error ("This reference does not denote a constructor: "
			       ^(string_of_qualid qid)))
      with Not_found -> 
	match maybe_variable l with
	  | Some s -> VarPat (loc,s)
	  | _ -> error ("Unknown qualified constructor: "
			^(string_of_qualid qid)))

  (* This may happen in quotations *)
  | Node(loc,"MUTCONSTRUCT",[sp;Num(_,ti);Num(_,n)]) ->
      (* Buggy: needs to compute the context *)
      let c = (ast_to_sp sp,ti),n in
      if !dump then add_glob loc (ConstructRef c); 
      ConstrPat (loc,c)

  | Path(loc,kn) ->
      (let dir,id = decode_kn kn in
       let sp = make_path dir id in
	 match absolute_reference sp with 
	   | ConstructRef c as r -> 
	       if !dump then add_glob loc (ConstructRef c);
	       ConstrPat (loc,c)
	   | _ ->
               error ("Unknown absolute constructor name: "^(string_of_path sp)))
  | Node(loc,("CONST"|"EVAR"|"MUTIND"|"SYNCONST" as key), l) ->
      user_err_loc (loc,"ast_to_pattern",
   (str "Found a pattern involving global references which are not constructors"
))

  | _ -> anomaly "ast_to_pattern: badly-formed ast for Cases pattern"

let ast_to_global loc c =
  match c with
    | ("CONST", [sp]) ->
	let ref = ConstRef (ast_to_sp sp) in
	let imps = implicits_of_global ref in
	RRef (loc, ref), imps
    | ("MUTIND", [sp;Num(_,tyi)]) -> 
	let ref = IndRef (ast_to_sp sp, tyi) in
	let imps = implicits_of_global ref in
	RRef (loc, ref), imps
    | ("MUTCONSTRUCT", [sp;Num(_,ti);Num(_,n)]) ->
	let ref = ConstructRef ((ast_to_sp sp,ti),n) in
	let imps = implicits_of_global ref in
	RRef (loc, ref), imps
    | ("EVAR", [(Num (_,ev))]) ->
	REvar (loc, ev), []
    | ("SYNCONST", [sp]) ->
	Syntax_def.search_syntactic_definition (sp_of_kn (ast_to_sp sp)), []
    | _ -> anomaly_loc (loc,"ast_to_global",
			(str "Bad ast for this global a reference"))

(*
let ref_from_constr c = match kind_of_term c with
  | Const (sp,ctxt) -> RConst (sp, ast_to_constr_ctxt ctxt)
  | Evar (ev,ctxt) -> REVar (ev, ast_to_constr_ctxt ctxt) 
  | Construct (csp,ctxt) -> RConstruct (csp, ast_to_constr_ctxt ctxt)
  | Ind (isp,ctxt) -> RInd (isp, ast_to_constr_ctxt ctxt)
  | Var id -> RVar id  (* utilisé pour coercion_value (tmp) *)
  | _ -> anomaly "Not a reference"
*)

(* [vars1] is a set of name to avoid (used for the tactic language);
   [vars2] is the set of global variables, env is the set of variables
   abstracted until this point *)

let ast_to_var (env,impls) (vars1,vars2) loc id =
  let imps =
    if Idset.mem id env or List.mem id vars1
    then
      try List.assoc id impls
      with Not_found -> []
    else
      let _ = lookup_named id vars2 in
      (* Car Fixpoint met les fns définies tmporairement comme vars de sect *)
      try
	let ref = VarRef id in
	implicits_of_global ref
      with _ -> []
  in RVar (loc, id), imps

(**********************************************************************)

let rawconstr_of_var env vars loc id =
  try
    ast_to_var env vars loc id
  with Not_found ->
    Pretype_errors.error_var_not_found_loc loc id

let rawconstr_of_qualid env vars loc qid =
  (* Is it a bound variable? *)
  try
    match repr_qualid qid with
      | d,s when repr_dirpath d = [] -> ast_to_var env vars loc s
      | _ -> raise Not_found
  with Not_found ->
  (* Is it a global reference or a syntactic definition? *)
  try match Nametab.extended_locate qid with
  | TrueGlobal ref ->
    if !dump then add_glob loc ref;
    let imps = implicits_of_global ref in
    RRef (loc, ref), imps
  | SyntacticDef sp ->
    set_loc_of_rawconstr loc (Syntax_def.search_syntactic_definition sp), []
  with Not_found ->
    error_global_not_found_loc loc qid

let mkLambdaC (x,a,b) = ope("LAMBDA",[a;slam(Some x,b)])
let mkLambdaCit = List.fold_right (fun (x,a) b -> mkLambdaC(x,a,b))
let mkProdC (x,a,b) = ope("PROD",[a;slam(Some x,b)])
let mkProdCit = List.fold_right (fun (x,a) b -> mkProdC(x,a,b))

let destruct_binder = function
  | Node(_,"BINDER",c::idl) -> List.map (fun id -> (nvar_of_ast id,c)) idl
  | _ -> anomaly "BINDER is expected"

(* [merge_aliases] returns the sets of all aliases encountered at this
   point and a substitution mapping extra aliases to the first one *)
let merge_aliases (ids,subst as aliases) = function
  | Anonymous -> aliases
  | Name id   ->
      ids@[id],
      if ids=[] then subst 
      else (id, List.hd ids)::subst

let alias_of = function
  | ([],_) -> Anonymous
  | (id::_,_) -> Name id

let message_redundant_alias (s1,s2) =
  warning ("Alias variable "^(string_of_id s1)
	   ^" is merged with "^(string_of_id s2))

let rec ast_to_pattern env aliases = function
  | Node(_,"PATTAS",[Nvar (loc,s); p]) ->
      let aliases' = merge_aliases aliases (name_of_nvar s) in
      ast_to_pattern env aliases' p

  | Node(_,"PATTCONSTRUCT", head::((_::_) as pl)) ->
      (match maybe_constructor env head with
	 | ConstrPat (loc,c) ->
	     let (idsl,pl') =
	       List.split (List.map (ast_to_pattern env ([],[])) pl) in
	     (aliases::(List.flatten idsl),
	      PatCstr (loc,c,pl',alias_of aliases))
	 | VarPat (loc,s) ->
	     user_err_loc (loc,"ast_to_pattern",mssg_hd_is_not_constructor s))

  | ast ->
      (match maybe_constructor env ast with
	 | ConstrPat (loc,c) -> ([aliases], PatCstr (loc,c,[],alias_of aliases))
	 | VarPat (loc,s) ->
	     let aliases = merge_aliases aliases (name_of_nvar s) in
	     ([aliases], PatVar (loc,alias_of aliases)))

let rec ast_to_fix = function
  | [] -> ([],[],[],[])
  | Node(_,"NUMFDECL", [Nvar(_,fi); Num(_,ni); astA; astT])::rest ->
      let (lf,ln,lA,lt) = ast_to_fix rest in
      (fi::lf, (ni-1)::ln, astA::lA, astT::lt)
  | Node(_,"FDECL", [Nvar(_,fi); Node(_,"BINDERS",bl); astA; astT])::rest->
      let binders = List.flatten (List.map destruct_binder bl) in
      let ni = List.length binders - 1 in
      let (lf,ln,lA,lt) = ast_to_fix rest in
      (fi::lf, ni::ln, (mkProdCit binders astA)::lA,
       (mkLambdaCit binders astT)::lt)
  | _ -> anomaly "FDECL or NUMFDECL is expected"

let rec ast_to_cofix = function
  | [] -> ([],[],[])
  | Node(_,"CFDECL", [Nvar(_,fi); astA; astT])::rest -> 
      let (lf,lA,lt) = ast_to_cofix rest in
      (fi::lf, astA::lA, astT::lt)
  | _ -> anomaly "CFDECL is expected"

let error_fixname_unbound s is_cofix loc name = 
  user_err_loc 
    (loc,"ast_to (COFIX)",
     str "The name" ++ spc () ++ pr_id name ++ 
     spc () ++ str "is not bound in the corresponding" ++ spc () ++
     str ((if is_cofix then "co" else "")^"fixpoint definition"))
(*
let rec collapse_env n env = if n=0 then env else
  add_rel_decl (Anonymous,()) (collapse_env (n-1) (snd (uncons_rel_env env)))
*)

let check_capture loc s ty = function
  | Slam _ when occur_var_ast s ty -> error_capture_loc loc s
  | _ -> ()

let ast_to_rawconstr sigma env allow_soapp lvar =
  let rec dbrec (ids,impls as env) = function
    | Nvar(loc,s) ->
	fst (rawconstr_of_var env lvar loc s)

    | Node(loc,"QUALID", l) ->
        fst (rawconstr_of_qualid env lvar loc (interp_qualid l))
  
    | Node(loc,"FIX", (Nvar (locid,iddef))::ldecl) ->
	let (lf,ln,lA,lt) = ast_to_fix ldecl in
	let n =
	  try 
	    (list_index (ident_of_nvar locid iddef) lf) -1
          with Not_found ->
	    error_fixname_unbound "ast_to_rawconstr (FIX)" false locid iddef in
	let ext_ids = List.fold_right Idset.add lf ids in
	let defl = Array.of_list (List.map (dbrec (ext_ids,impls)) lt) in
	let arityl = Array.of_list (List.map (dbrec env) lA) in
	RRec (loc,RFix (Array.of_list ln,n), Array.of_list lf, arityl, defl)
	  
    | Node(loc,"COFIX", (Nvar(locid,iddef))::ldecl) ->
	let (lf,lA,lt) = ast_to_cofix ldecl in
	let n =
          try 
	    (list_index (ident_of_nvar locid iddef) lf) -1
          with Not_found ->
	    error_fixname_unbound "ast_to_rawconstr (COFIX)" true locid iddef
	in
	let ext_ids = List.fold_right Idset.add lf ids in
	let defl = Array.of_list (List.map (dbrec (ext_ids,impls)) lt) in
	let arityl = Array.of_list (List.map (dbrec env) lA) in
	RRec (loc,RCoFix n, Array.of_list lf, arityl, defl)
	  
    | Node(loc,("PROD"|"LAMBDA"|"LETIN" as k), [c1;Slam(_,ona,c2)]) ->
	let na,ids' = match ona with
	  | Some id -> Name id, Idset.add id ids
	  | _ -> Anonymous, ids in
	let c1' = dbrec env c1 and c2' = dbrec (ids',impls) c2 in
	(match k with
	   | "PROD" -> RProd (loc, na, c1', c2')
	   | "LAMBDA" -> RLambda (loc, na, c1', c2')
	   | "LETIN" -> RLetIn (loc, na, c1', c2')
	   | _ -> assert false)

    | Node(_,("PRODLIST"|"LAMBDALIST" as s), [c1;(Slam _ as c2)]) -> 
	iterated_binder s 0 c1 env c2

    | Node(loc,"APPLISTEXPL", f::args) ->
	RApp (loc,dbrec env f,ast_to_args env args)

    | Node(loc,"APPLIST", f::args) ->
	let (c, impargs) =
	  match f with
	    | Node(locs,"QUALID",p) ->
		rawconstr_of_qualid env lvar locs (interp_qualid p)
	    | Node(loc,
		   ("CONST"|"EVAR"|"MUTIND"|"MUTCONSTRUCT"|"SYNCONST" as key),
		   l) ->
		ast_to_global loc (key,l)
	    | _ -> (dbrec env f, [])
        in
	  RApp (loc, c, ast_to_impargs env impargs args)

    | Node(loc,"CASES", p:: Node(_,"TOMATCH",tms):: eqns) ->
	let po = match p with 
	  | Str(_,"SYNTH") -> None 
	  | _ -> Some(dbrec env p) in
	RCases (loc,PrintCases,po,
		List.map (dbrec env) tms,
		List.map (ast_to_eqn (List.length tms) env) eqns)

    | Node(loc,(("CASE"|"IF"|"LET"|"MATCH")as tag), p::c::cl) ->
	let po = match p with 
	  | Str(_,"SYNTH") -> None 
	  | _ -> Some(dbrec env p) in
	let isrec = match tag with
	  | "MATCH" -> true | ("LET"|"CASE"|"IF") -> false 
	  | _ -> anomaly "ast_to: wrong tag in old case expression" in
	ROldCase (loc,isrec,po,dbrec env c,
		  Array.of_list (List.map (dbrec env) cl))

    | Node(loc,"ISEVAR",[]) -> RHole (Some loc)
    | Node(loc,"META",[Num(_,n)]) ->
	if n<0 then error_metavar_loc loc else RMeta (loc, n)

    | Node(loc,"PROP", []) -> RSort(loc,RProp Null)
    | Node(loc,"SET", [])  -> RSort(loc,RProp Pos)
    | Node(loc,"TYPE", _) -> RSort(loc,RType None)
	  
    (* This case mainly parses things build in a quotation *)
    | Node(loc,("CONST"|"EVAR"|"MUTIND"|"MUTCONSTRUCT"|"SYNCONST" as key),l) ->
	fst (ast_to_global loc (key,l))

    | Node(loc,"CAST", [c1;c2]) ->	   
	RCast (loc,dbrec env c1,dbrec env c2)

    | Node(loc,"SOAPP", args) when allow_soapp ->
	(match List.map (dbrec env) args with
           (* Hack special pour l'interprétation des constr_pattern *)
	   | RMeta (locn,n) :: args -> RApp (loc,RMeta (locn,- n), args)
	   | RHole _ :: _ -> anomaly "Metavariable for 2nd-order pattern-matching cannot be anonymous"
	   | _ -> anomaly "Bad arguments for second-order pattern-matching")

    | Node(loc,"SQUASH",_) ->
        user_err_loc(loc,"ast_to_rawconstr",
                     (str "Ill-formed specification"))

    | Node(loc,opn,tl) -> 
	anomaly ("ast_to_rawconstr found operator "^opn^" with "^
		 (string_of_int (List.length tl))^" arguments")

    | Dynamic (loc,d) -> RDynamic (loc,d)

    | _ -> anomaly "ast_to_rawconstr: unexpected ast"

  and ast_to_eqn n (ids,impls as env) = function
    | Node(loc,"EQN",rhs::lhs) ->
	let (idsl_substl_list,pl) =
	  List.split (List.map (ast_to_pattern env ([],[])) lhs) in
	let idsl, substl = List.split (List.flatten idsl_substl_list) in
	let eqn_ids = List.flatten idsl in
	let subst = List.flatten substl in 
	(* Linearity implies the order in ids is irrelevant *)
	check_linearity lhs eqn_ids;
	check_uppercase loc eqn_ids;
	check_number_of_pattern loc n pl;
	let rhs = replace_vars_ast subst rhs in
	List.iter message_redundant_alias subst;
	let env_ids = List.fold_right Idset.add eqn_ids ids in
	(loc, eqn_ids,pl,dbrec (env_ids,impls) rhs)
    | _ -> anomaly "ast_to_rawconstr: ill-formed ast for Cases equation"

  and iterated_binder oper n ty (ids,impls as env) = function
    | Slam(loc,ona,body) ->
	let na,ids' = match ona with 
	  | Some id ->
	      if n>0 then check_capture loc id ty body;
	      Name id, Idset.add id ids
	  | _ -> Anonymous, ids
	in
	let r = iterated_binder oper (n+1) ty (ids',impls) body in
	(match oper with
	   | "PRODLIST" -> RProd(loc, na, dbrec env ty, r)
	   | "LAMBDALIST" -> RLambda(loc, na, dbrec env ty, r)
	   | _ -> assert false)
    | body -> dbrec env body

  and ast_to_impargs env l args =
    let rec aux n l args = match (l,args) with 
      | (i::l',Node(loc, "EXPL", [Num(_,j);a])::args') ->
	  if i=n & j>=i then
	    if j=i then 
	      (dbrec env a)::(aux (n+1) l' args')
	    else 
	      (RHole None)::(aux (n+1) l' args)
	  else 
	    if i<>n then
	      error ("Bad explicitation number: found "^
		   (string_of_int j)^" but was expecting a regular argument")
	    else
	      error ("Bad explicitation number: found "^
		   (string_of_int j)^" but was expecting "^(string_of_int i))
      | (i::l',a::args') -> 
	  if i=n then 
	    (RHole None)::(aux (n+1) l' args)
	  else 
	    (dbrec env a)::(aux (n+1) l args')
      | ([],args) -> ast_to_args env args
      | (_,[]) -> []
    in 
    aux 1 l args

  and ast_to_args env = function
    | Node(loc, "EXPL", _)::args' ->
        (* To deal with errors *)
	error_expl_impl_loc loc
    | a::args -> (dbrec env a) :: (ast_to_args env args)
    | [] -> []

  in 
  dbrec env

(**************************************************************************)
(* Globalization of AST quotations (mainly used to get statically         *)
(* bound idents in grammar or pretty-printing rules)                      *)
(**************************************************************************)

let ast_of_ref_loc loc ref = set_loc loc (Termast.ast_of_ref ref)

let ast_of_syndef loc sp = Node (loc, "SYNCONST", [path_section loc sp])

let ast_of_extended_ref_loc loc = function
  | TrueGlobal ref -> ast_of_ref_loc loc ref
  | SyntacticDef sp -> ast_of_syndef loc (kn_of_sp sp)

let ast_of_extended_ref = ast_of_extended_ref_loc dummy_loc

let ast_of_var env ast id =
  if isMeta (string_of_id id) or Idset.mem id env then ast
  else raise Not_found

let ast_hole = Node (dummy_loc, "ISEVAR", [])

let implicits_of_extended_reference = function
  | TrueGlobal ref -> implicits_of_global ref
  | SyntacticDef _ -> []

let warning_globalize qid =
  warning ("Could not globalize " ^ (string_of_qualid qid))

let globalize_qualid qid =
  try
    let ref = Nametab.extended_locate qid in
    ast_of_extended_ref_loc dummy_loc ref
  with Not_found ->
    if_verbose warning_globalize qid;
    Termast.ast_of_qualid qid

let adjust_qualid env loc ast qid =
  (* Is it a bound variable? *)
  try
    match repr_qualid qid with
      | d,id when repr_dirpath d = [] -> ast_of_var env ast id
      | _ -> raise Not_found
  with Not_found ->
  (* Is it a global reference or a syntactic definition? *)
  try
    let ref = Nametab.extended_locate qid in
    ast_of_extended_ref_loc loc ref
  with Not_found ->
    if_verbose warning_globalize qid;
    ast

let ast_adjust_consts sigma =
  let rec dbrec env = function
    | Node(loc, ("APPLIST" as key), (Node(locs,"QUALID",p) as ast)::args) ->
	let f = adjust_qualid env loc ast (interp_qualid p) in
	Node(loc, key, f :: List.map (dbrec env) args)
    | Nmeta (loc, s) as ast -> ast
    | Nvar (loc, id) as ast ->
        if Idset.mem id env then ast
        else adjust_qualid env loc ast (make_short_qualid id)
    | Node (loc, "QUALID", p) as ast ->
	adjust_qualid env loc ast (interp_qualid p)
    | Slam (loc, None, t) -> Slam (loc, None, dbrec env t)
    | Slam (loc, Some na, t) ->
        let env' = Idset.add na env in
        Slam (loc, Some na, dbrec env' t)
    | Node (loc, opn, tl) -> Node (loc, opn, List.map (dbrec env) tl)
    | x -> x

  in
  dbrec

let globalize_constr ast =
  let sign = Global.named_context () in
  ast_adjust_consts Evd.empty (from_list (ids_of_named_context sign)) ast

(* Globalizes ast expressing constructions in tactics or vernac *)
(* Actually, it is incomplete, see vernacinterp.ml and tacinterp.ml *)
(* Used mainly to parse Grammar and Syntax expressions *)
let rec glob_ast sigma env =
  function
    Node (loc, "CONSTR", [c]) ->
      Node (loc, "CONSTR", [ast_adjust_consts sigma env c])
  | Node (loc, "CONSTRLIST", l) ->
      Node (loc, "CONSTRLIST", List.map (ast_adjust_consts sigma env) l)
  | Slam (loc, None, t) -> Slam (loc, None, glob_ast sigma env t)
  | Slam (loc, Some na, t) ->
      let env' = Idset.add na env in
      Slam (loc, Some na, glob_ast sigma env' t)
  | Node (loc, opn, tl) -> Node (loc, opn, List.map (glob_ast sigma env) tl)
  | x -> x

let globalize_ast ast =
  let sign = Global.named_context () in
  glob_ast Evd.empty (from_list (ids_of_named_context sign)) ast

(**************************************************************************)
(* Functions to translate ast into rawconstr                              *)
(**************************************************************************)

let interp_rawconstr_gen sigma env impls allow_soapp lvar com =
  ast_to_rawconstr sigma
    (from_list (ids_of_rel_context (rel_context env)), impls)
    allow_soapp (lvar,env) com

let interp_rawconstr sigma env com =
  interp_rawconstr_gen sigma env [] false [] com

let interp_rawconstr_with_implicits sigma env impls com =
  interp_rawconstr_gen sigma env impls false [] com

(*The same as interp_rawconstr but with a list of variables which must not be
  globalized*)

let interp_rawconstr_wo_glob sigma env lvar com =
  interp_rawconstr_gen sigma env [] false lvar com

(*********************************************************************)
(* V6 compat: Functions before in ex-trad                            *)

(* Functions to parse and interpret constructions *)

(* To embed constr in Coqast.t *)
let constrIn t = Dynamic (dummy_loc,constr_in t)
let constrOut = function
  | Dynamic (_,d) ->
    if (Dyn.tag d) = "constr" then
      constr_out d
    else
      anomalylabstrm "constrOut" (str "Dynamic tag should be constr")
  | ast ->
    anomalylabstrm "constrOut"
      (str "Not a Dynamic ast: " ++ print_ast ast)

let interp_constr sigma env c =
  understand sigma env (interp_rawconstr sigma env c)

let interp_openconstr sigma env c =
  understand_gen_tcc sigma env [] [] None (interp_rawconstr sigma env c)

let interp_casted_openconstr sigma env c typ =
  understand_gen_tcc sigma env [] [] (Some typ) (interp_rawconstr sigma env c)

let interp_type sigma env c =
  understand_type sigma env (interp_rawconstr sigma env c)

let interp_type_with_implicits sigma env impls c =
  understand_type sigma env (interp_rawconstr_with_implicits sigma env impls c)

let interp_sort = function
  | Node(loc,"PROP", []) -> Prop Null
  | Node(loc,"SET", [])  -> Prop Pos
  | Node(loc,"TYPE", _) -> new_Type_sort ()
  | a -> user_err_loc (Ast.loc a,"interp_sort", (str "Not a sort"))

let interp_elimination_sort = function
  | Node(loc,"PROP", []) -> InProp
  | Node(loc,"SET", [])  -> InSet
  | Node(loc,"TYPE", _) -> InType
  | a -> user_err_loc (Ast.loc a,"interp_sort", (str "Not a sort"))

let judgment_of_rawconstr sigma env c =
  understand_judgment sigma env (interp_rawconstr sigma env c)

let type_judgment_of_rawconstr sigma env c =
  understand_type_judgment sigma env (interp_rawconstr sigma env c)

(*To retype a list of key*constr with undefined key*)
let retype_list sigma env lst =
  List.fold_right (fun (x,csr) a ->
    try (x,Retyping.get_judgment_of env sigma csr)::a with
    | Anomaly _ -> a) lst []

(*  List.map (fun (x,csr) -> (x,Retyping.get_judgment_of env sigma csr)) lst*)

(* Interprets a constr according to two lists *)
(* of instantiations (variables and metas)    *)
(* Note: typ is retyped *)
let interp_constr_gen sigma env lvar lmeta com exptyp =
  let c = interp_rawconstr_gen sigma env [] false (List.map fst lvar) com
  and rtype lst = retype_list sigma env lst in
  understand_gen sigma env (rtype lvar) (rtype lmeta) exptyp c;;

(*Interprets a casted constr according to two lists of instantiations
  (variables and metas)*)
let interp_openconstr_gen sigma env lvar lmeta com exptyp =
  let c = interp_rawconstr_gen sigma env [] false (List.map fst lvar) com
  and rtype lst = retype_list sigma env lst in
  understand_gen_tcc sigma env (rtype lvar) (rtype lmeta) exptyp c;;

let interp_casted_constr sigma env com typ = 
  understand_gen sigma env [] [] (Some typ) (interp_rawconstr sigma env com)

(* To process patterns, we need a translation from AST to term
   without typing at all. *)

let ctxt_of_ids ids = Array.of_list (List.map mkVar ids)
(*
let rec pat_of_ref metas vars = function
  | RConst (sp,ctxt) -> RConst (sp, ast_to_rawconstr_ctxt ctxt)
  | RInd (ip,ctxt) -> RInd (ip, ast_to_rawconstr_ctxt ctxt)
  | RConstruct(cp,ctxt) ->RConstruct(cp, ast_to_rawconstr_ctxt ctxt)
  | REVar (n,ctxt) -> REVar (n, ast_to_rawconstr_ctxt ctxt)
  | RVar _ -> assert false (* Capturé dans pattern_of_raw *)
*)
let rec pat_of_raw metas vars lvar = function
  | RVar (_,id) ->
      (try PRel (list_index (Name id) vars)
       with Not_found ->
       try List.assoc id lvar
       with Not_found -> PVar id)
  | RMeta (_,n) ->
      metas := n::!metas; PMeta (Some n)
  | RRef (_,r) ->
      PRef r
  (* Hack pour ne pas réécrire une interprétation complète des patterns*)
  | RApp (_, RMeta (_,n), cl) when n<0 ->
      PSoApp (- n, List.map (pat_of_raw metas vars lvar) cl)
  | RApp (_,c,cl) -> 
      PApp (pat_of_raw metas vars lvar c,
	    Array.of_list (List.map (pat_of_raw metas vars lvar) cl))
  | RLambda (_,na,c1,c2) ->
      PLambda (na, pat_of_raw metas vars lvar c1,
	       pat_of_raw metas (na::vars) lvar c2)
  | RProd (_,na,c1,c2) ->
      PProd (na, pat_of_raw metas vars lvar c1,
	       pat_of_raw metas (na::vars) lvar c2)
  | RLetIn (_,na,c1,c2) ->
      PLetIn (na, pat_of_raw metas vars lvar c1,
	       pat_of_raw metas (na::vars) lvar c2)
  | RSort (_,s) ->
      PSort s
  | RHole _ ->
      PMeta None
  | RCast (_,c,t) ->
      warning "Cast not taken into account in constr pattern";
      pat_of_raw metas vars lvar c
  | ROldCase (_,false,po,c,br) ->
      PCase (option_app (pat_of_raw metas vars lvar) po,
             pat_of_raw metas vars lvar c,
             Array.map (pat_of_raw metas vars lvar) br)
  | _ ->
      error "pattern_of_rawconstr: not implemented"

let pattern_of_rawconstr lvar c =
  let metas = ref [] in
  let p = pat_of_raw metas [] lvar c in
  (!metas,p)

let interp_constrpattern_gen sigma env lvar com = 
  let c =
    ast_to_rawconstr sigma
      (from_list (ids_of_rel_context (rel_context env)), [])
      true (List.map fst lvar,env) com
  and nlvar = List.map (fun (id,c) -> (id,pattern_of_constr c)) lvar in
  try 
    pattern_of_rawconstr nlvar c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

let interp_constrpattern sigma env com =
  interp_constrpattern_gen sigma env [] com
