
(* $Id$ *)

open Pp
open Util
open Names
open Sign
open Generic
open Term
open Environ
open Evd
open Reduction
open Impargs
open Rawterm
open Pattern
open Typing
open Pretyping
open Evarutil
open Ast
open Coqast
open Pretype_errors

(* when an head ident is not a constructor in pattern *)
let mssg_hd_is_not_constructor s =
  [< 'sTR ("The symbol "^s^" should be a constructor") >]

(* checking linearity of a list of ids in patterns *)
let non_linearl_mssg id =
  [< 'sTR "The variable " ; 'sTR(string_of_id id);
     'sTR " is bound several times in pattern" >] 

let rec has_duplicate = function 
  | [] -> None
  | x::l -> if List.mem x l then (Some x) else has_duplicate l

let check_linearity loc ids =
  match has_duplicate ids with
    | Some id -> user_err_loc (loc,"dbize_eqn",non_linearl_mssg id)
    | None -> ()

let mal_formed_mssg () =
  [<'sTR "malformed macro of multiple case" >]

(* determines if some pattern variable starts with uppercase *)
let warning_uppercase loc uplid = (* Comment afficher loc ?? *)
  let vars =
    prlist_with_sep pr_spc (fun v -> [< 'sTR (string_of_id v) >]) uplid in
  let (s1,s2) = if List.length uplid = 1 then (" ","s ") else ("s "," ") in
  wARN [<'sTR ("the variable"^s1); vars;
	 'sTR (" start"^s2^"with an upper case letter in pattern"); 'cUT >]

let is_uppercase_var v =
 match (string_of_id v).[0] with
    'A'..'Z' -> true
 | _  -> false

let check_uppercase loc ids =
  let uplid = List.filter is_uppercase_var ids in
  if uplid <> [] then warning_uppercase loc uplid

(* check that the number of pattern matches the number of matched args *)
let mssg_number_of_patterns n pl =
  [< 'sTR"Expecting ";'iNT n ; 'sTR" pattern(s) but found ";
    'iNT (List.length pl); 'sTR" in " >]

let check_number_of_pattern loc n l =
  if n<>(List.length l) then
    user_err_loc (loc,"check_number_of_pattern",mssg_number_of_patterns n l)

(****************************************************************)
(* Arguments normally implicit in the "Implicit Arguments mode" *)
(* but explicitely given                                        *)

let dbize_sp = function
  | Path(loc,sl,s) ->
      (try 
	 section_path sl s
       with Invalid_argument _ | Failure _ ->
         anomaly_loc(loc,"Astterm.dbize_sp",
                     [< 'sTR"malformed section-path" >]))
  | ast -> anomaly_loc(Ast.loc ast,"Astterm.dbize_sp",
                     [< 'sTR"not a section-path" >])

let is_underscore id = (id = "_")

let name_of_nvar s =
  if is_underscore s then Anonymous else Name (id_of_string s)

let ident_of_nvar loc s =
  if is_underscore s then
    user_err_loc (loc,"ident_of_nvar", [< 'sTR "Unexpected wildcard" >])
  else (id_of_string s)

(*
let rctxt_of_ctxt =
  Array.map
    (function
       | VAR id -> RRef (dummy_loc,RVar id)
       | _ ->
     error "Astterm: arbitrary substitution of references not yet implemented")
*)

let ids_of_ctxt ctxt =
  Array.to_list
    (Array.map
       (function
	  | VAR id -> id
	  | _ ->
      error
	"Astterm: arbitrary substitution of references not yet implemented")
    ctxt)

let maybe_constructor env s =
  try 
    match Declare.global_reference CCI (id_of_string s) with 
      | DOPN(MutConstruct (spi,j),cl) -> Some ((spi,j),ids_of_ctxt cl)
      | _ -> warning ("Defined identifier "
		      ^s^" is here considered as a matching variable"); None
  with Not_found -> 
    None

let dbize_ctxt ctxt =
  let l =
    List.map
      (function
	 | Nvar (loc,s) ->
	     (* RRef (dummy_loc,RVar (ident_of_nvar loc s)) *)
	     RRef (loc, RVar (ident_of_nvar loc s))
	 | _ -> anomaly "Bad ast for local ctxt of a global reference") ctxt
  in
  Array.of_list l

let dbize_constr_ctxt =
  Array.map
    (function
       | VAR id ->
	   (* RRef (dummy_loc,RVar (ident_of_nvar loc s)) *)
	   RRef (dummy_loc, RVar id)
       | _ -> anomaly "Bad ast for local ctxt of a global reference")

let dbize_rawconstr_ctxt =
  Array.map
    (function
       | RRef (_, RVar id) -> VAR id
       | _ -> anomaly "Bad ast for local ctxt of a global reference")

let dbize_global loc = function
  | ("CONST", sp::ctxt) -> 
      RRef (loc,RConst (dbize_sp sp,dbize_ctxt ctxt))
  | ("EVAR", (Num (_,ev))::ctxt) ->
      RRef (loc,REVar (ev,dbize_ctxt ctxt))
  | ("MUTIND", sp::Num(_,tyi)::ctxt) -> 
      RRef (loc,RInd ((dbize_sp sp, tyi),dbize_ctxt ctxt))
  | ("MUTCONSTRUCT", sp::Num(_,ti)::Num(_,n)::ctxt) ->
      RRef (loc,RConstruct (((dbize_sp sp,ti),n),dbize_ctxt ctxt))
  (* | ("SYNCONST", [sp]) -> search_synconst_path CCI (dbize_sp sp) *)
  (* | ("ABST", [sp]) -> RRef (loc,Abst (dbize_sp sp)) *)
  | _ -> anomaly_loc (loc,"dbize_global",
		      [< 'sTR "Bad ast for this global a reference">])

let ref_from_constr = function
  | DOPN (Const sp,ctxt) -> RConst (sp, dbize_constr_ctxt ctxt)
  | DOPN (Evar ev,ctxt) -> REVar (ev, dbize_constr_ctxt ctxt) 
  | DOPN (MutConstruct (spi,j),ctxt) -> 
      RConstruct ((spi,j), dbize_constr_ctxt ctxt)
  | DOPN (MutInd (sp,i),ctxt) -> RInd ((sp,i), dbize_constr_ctxt ctxt)
  | VAR id -> RVar id  (* utilisé pour coe_value (tmp) *)
  | _ -> anomaly "Not a reference"

(* [vars1] is a set of name to avoid (used for the tactic language);
   [vars2] is the set of global variables, env is the set of variables
   abstracted until this point *)
let dbize_ref k sigma env loc s (vars1,vars2)=
  let id = ident_of_nvar loc s in
  if Idset.mem id env then
    RRef (loc,RVar id),[]
  else
  if List.mem s vars1 then
    RRef(loc,RVar id),[]
  else
  try
    let _ = lookup_id id vars2 in
    RRef (loc,RVar id), (try implicits_of_var id with _ -> [])
  with Not_found ->
  try 
    let c,il = match k with
      | CCI -> Declare.global_reference_imps CCI id
      | FW  -> Declare.global_reference_imps FW id
      | OBJ -> anomaly "search_ref_cci_fw" in
    RRef (loc,ref_from_constr c), il
  with Not_found ->
  try 
    (Syntax_def.search_syntactic_definition id, [])
  with Not_found -> 
    error_var_not_found_loc loc CCI id
	  
let mkLambdaC (x,a,b) = ope("LAMBDA",[a;slam(Some (string_of_id x),b)])
let mkLambdaCit = List.fold_right (fun (x,a) b -> mkLambdaC(x,a,b))
let mkProdC (x,a,b) = ope("PROD",[a;slam(Some (string_of_id x),b)])
let mkProdCit = List.fold_right (fun (x,a) b -> mkProdC(x,a,b))

let destruct_binder = function
  | Node(_,"BINDER",c::idl) ->
      List.map (fun id -> (id_of_string (nvar_of_ast id),c)) idl
  | _ -> anomaly "BINDER is expected"

let merge_aliases p = function
  | a, Anonymous    -> a, p
  | Anonymous, a    -> a, p
  | Name id1, (Name id2 as na) ->
      let s1 = string_of_id id1 in
      let s2 = string_of_id id2 in
      warning ("Alias variable "^s1^" is merged with "^s2);
      na, replace_var_ast s1 s2 p

let rec dbize_pattern env aliasopt = function
  | Node(_,"PATTAS",[Nvar (loc,s); p]) ->
      let aliasopt',p' = merge_aliases p (aliasopt,name_of_nvar s) in
      dbize_pattern env aliasopt' p'
  | Nvar(loc,s) ->
      (match maybe_constructor env s with
	 | Some c ->
	     let ids = match aliasopt with Anonymous -> [] | Name id -> [id] in
	     (ids,PatCstr (loc,c,[],aliasopt))
	 | None ->
	     (match name_of_nvar s with
		| Anonymous -> ([], PatVar (loc,Anonymous))
		| Name id as name -> ([id], PatVar (loc,name))))
  | Node(_,"PATTCONSTRUCT", Nvar(loc,s)::((_::_) as pl)) ->
      (match maybe_constructor env s with
	 | Some c ->
	     let ids = match aliasopt with Anonymous -> [] | Name id -> [id] in
	     let (idsl,pl') = 
	       List.split (List.map (dbize_pattern env Anonymous) pl) in
	     (List.flatten (ids::idsl),PatCstr (loc,c,pl',aliasopt))
	 | None ->
	     user_err_loc (loc,"dbize_pattern",mssg_hd_is_not_constructor s))
  | _ -> anomaly "dbize: badly-formed ast for Cases pattern"

let rec dbize_fix = function
  | [] -> ([],[],[],[])
  | Node(_,"NUMFDECL", [Nvar(_,fi); Num(_,ni); astA; astT])::rest ->
      let (lf,ln,lA,lt) = dbize_fix rest in
      ((id_of_string fi)::lf, (ni-1)::ln, astA::lA, astT::lt)
  | Node(_,"FDECL", [Nvar(_,fi); Node(_,"BINDERS",bl); astA; astT])::rest ->
      let binders = List.flatten (List.map destruct_binder bl) in
      let ni = List.length binders - 1 in
      let (lf,ln,lA,lt) = dbize_fix rest in
      ((id_of_string fi)::lf, ni::ln, (mkProdCit binders astA)::lA,
       (mkLambdaCit binders astT)::lt)
  | _ -> anomaly "FDECL or NUMFDECL is expected"

let rec dbize_cofix = function
  | [] -> ([],[],[])
  | Node(_,"CFDECL", [Nvar(_,fi); astA; astT])::rest -> 
      let (lf,lA,lt) = dbize_cofix rest in
      ((id_of_string fi)::lf, astA::lA, astT::lt)
  | _ -> anomaly "CFDECL is expected"

let error_fixname_unbound str is_cofix loc name = 
  user_err_loc 
    (loc,"dbize (COFIX)",
       [< 'sTR "The name"; 'sPC ; 'sTR name ; 
	  'sPC ; 'sTR "is not bound in the corresponding"; 'sPC ;
	  'sTR ((if is_cofix then "co" else "")^"fixpoint definition") >])
(*
let rec collapse_env n env = if n=0 then env else
  add_rel (Anonymous,()) (collapse_env (n-1) (snd (uncons_rel_env env)))
*)

let check_capture s ty = function
  | Slam _ when occur_var_ast s ty ->
      errorlabstrm "check_capture"
	[< 'sTR ("The variable "^s^" occurs in its type") >]
  | _ -> ()

let dbize k sigma env allow_soapp lvar =
  let rec dbrec env = function
    | Nvar(loc,s) -> fst (dbize_ref k sigma env loc s lvar)
	  
   (*
   | Slam(_,ona,Node(_,"V$",l)) ->
       let na =
         (match ona with Some s -> Name (id_of_string s) | _ -> Anonymous)
       in DLAMV(na,Array.of_list (List.map (dbrec (Idset.add na env)) l))

   | Slam(_,ona,t) ->
       let na =
         (match ona with Some s -> Name (id_of_string s) | _ -> Anonymous)
       in DLAM(na, dbrec (Idset.add na env) t)
   *)
    | Node(loc,"FIX", (Nvar (locid,iddef))::ldecl) ->
	let (lf,ln,lA,lt) = dbize_fix ldecl in
	let n =
	  try 
	    (list_index (ident_of_nvar locid iddef) lf) -1
          with Not_found ->
	    error_fixname_unbound "dbize (FIX)" false locid iddef in
	let ext_env =
	  List.fold_left (fun env fid -> Idset.add fid env) env lf in
	let defl = Array.of_list (List.map (dbrec ext_env) lt) in
	let arityl = Array.of_list (List.map (dbrec env) lA) in
	RRec (loc,RFix (Array.of_list ln,n), Array.of_list lf, arityl, defl)
	  
    | Node(loc,"COFIX", (Nvar(locid,iddef))::ldecl) ->
	let (lf,lA,lt) = dbize_cofix ldecl in
	let n =
          try 
	    (list_index (ident_of_nvar locid iddef) lf) -1
          with Not_found ->
	    error_fixname_unbound "dbize (COFIX)" true locid iddef in
	let ext_env =
	  List.fold_left (fun env fid -> Idset.add fid env) env lf in
	let defl = Array.of_list (List.map (dbrec ext_env) lt) in
	let arityl = Array.of_list (List.map (dbrec env) lA) in
	RRec (loc,RCofix n, Array.of_list lf, arityl, defl)
	  
    | Node(loc,("PROD"|"LAMBDA" as k), [c1;Slam(_,ona,c2)]) ->
	let na,env' = match ona with
	  | Some s -> let id = id_of_string s in Name id, Idset.add id env
	  | _ -> Anonymous, env in
	let kind = if k="PROD" then BProd else BLambda in
	RBinder(loc, kind, na, dbrec env c1, dbrec env' c2)

    | Node(_,"PRODLIST", [c1;(Slam _ as c2)]) -> 
	iterated_binder BProd 0 c1 env c2
    | Node(_,"LAMBDALIST", [c1;(Slam _ as c2)]) -> 
	iterated_binder BLambda 0 c1 env c2

    | Node(loc,"APPLISTEXPL", f::args) ->
	RApp (loc,dbrec env f,List.map (dbrec env) args)
    | Node(loc,"APPLIST", Nvar(locs,s)::args) ->
	let (c, impargs) = dbize_ref k sigma env locs s lvar
        in
	  RApp (loc, c, dbize_args env impargs args)
    | Node(loc,"APPLIST", f::args) ->	   
	RApp (loc,dbrec env f,List.map (dbrec env) args)
	  
    | Node(loc,"CASES", p:: Node(_,"TOMATCH",tms):: eqns) ->
	let po = match p with 
	  | Str(_,"SYNTH") -> None 
	  | _ -> Some(dbrec env p) in
	RCases (loc,PrintCases,po,
		List.map (dbrec env) tms,
		List.map (dbize_eqn (List.length tms) env) eqns)

    | Node(loc,"CASE",Str(_,isrectag)::p::c::cl) ->
	let po = match p with 
	  | Str(_,"SYNTH") -> None 
	  | _ -> Some(dbrec env p) in
	let isrec = match isrectag with
	  | "REC" -> true | "NOREC" -> false 
	  | _ -> anomaly "dbize: wrong REC tag in CASE" in
	ROldCase (loc,isrec,po,dbrec env c,
		  Array.of_list (List.map (dbrec env) cl))

    | Node(loc,"ISEVAR",[]) -> RHole (Some loc)
    | Node(loc,"META",[Num(_,n)]) ->
	if n<0 then error "Metavariable numbers must be positive"
	else RMeta (loc, n)

    | Node(loc,"PROP", []) -> RSort(loc,RProp Null)
    | Node(loc,"SET", [])  -> RSort(loc,RProp Pos)
    | Node(loc,"TYPE", []) -> RSort(loc,RType)
	  
    (* This case mainly parses things build from   in a quotation *)
    | Node(loc,("CONST"|"EVAR"|"MUTIND"|"MUTCONSTRUCT"|"SYNCONST" as key),l) ->
	dbize_global loc (key,l)

    | Node(loc,"CAST", [c1;c2]) ->	   
	RCast (loc,dbrec env c1,dbrec env c2)

    | Node(loc,"SOAPP", args) when allow_soapp ->
	(match List.map (dbrec env) args with
           (* Hack special pour l'interprétation des constr_pattern *)
	   | RMeta (locn,n) :: args -> RApp (loc,RMeta (locn,- n), args)
	   | RHole _ :: _ -> anomaly "Metavariable for 2nd-order pattern-matching cannot be anonymous"
	   | _ -> anomaly "Bad arguments for second-order pattern-matching")

    | Node(loc,opn,tl) -> 
	anomaly ("dbize found operator "^opn^" with "^
		 (string_of_int (List.length tl))^" arguments")

    | _ -> anomaly "dbize: unexpected ast"

  and dbize_eqn n env = function
    | Node(loc,"EQN",rhs::lhs) ->
	let (idsl,pl) =
	  List.split (List.map (dbize_pattern env Anonymous) lhs) in
	let ids = List.flatten idsl in
	(* Linearity implies the order in ids is irrelevant *)
	check_linearity loc ids;
	check_uppercase loc ids;
	check_number_of_pattern loc n pl;
	let env' =
	  List.fold_left (fun env id -> Idset.add id env) env ids in
	(ids,pl,dbrec env' rhs)
    | _ -> anomaly "dbize: badly-formed ast for Cases equation"

  and iterated_binder oper n ty env = function
    | Slam(loc,ona,body) ->
	let na,env' = match ona with 
	  | Some s ->
	      check_capture s ty body;
	      let id = id_of_string s in Name id, Idset.add id env
	  | _ -> Anonymous, env
	in
	RBinder(loc, oper, na, dbrec env ty,
		(iterated_binder oper n ty env' body))
    | body -> dbrec env body

  and dbize_args env l args =
    let rec aux n l args = match (l,args) with 
      | (i::l',Node(loc, "EXPL", [Num(_,j);a])::args') ->
	  if i=n & j>=i then
	    if j=i then 
	      (dbrec env a)::(aux (n+1) l' args')
	    else 
	      (RHole None)::(aux (n+1) l' args)
	  else 
	    error "Bad explicitation number"
      | (i::l',a::args') -> 
	  if i=n then 
	    (RHole None)::(aux (n+1) l' args)
	  else 
	    (dbrec env a)::(aux (n+1) l' args')
      | ([],args) -> List.map (dbrec env) args
      | (_,[]) -> []
    in 
    aux 1 l args

  in 
  dbrec env

(* constr_of_com takes an environment of typing assumptions,
 * and translates a command to a constr. *)

(*Takes a list of variables which must not be globalized*)
let from_list l = List.fold_right Idset.add l Idset.empty

let interp_rawconstr_gen sigma env allow_soapp lvar com =
  dbize CCI sigma
    (from_list (ids_of_rel_context (rel_context env)))
    allow_soapp (lvar,var_context env) com

let interp_rawconstr sigma env com =
  interp_rawconstr_gen sigma env false [] com

(*The same as interp_rawconstr but with a list of variables which must not be
  globalized*)

let interp_rawconstr_wo_glob sigma env lvar com =
  dbize CCI sigma
    (from_list (ids_of_rel_context (rel_context env)))
    false (lvar,var_context env) com

(*let raw_fconstr_of_com sigma env com =
  dbize_fw sigma (unitize_env (context env)) [] com

let raw_constr_of_compattern sigma env com = 
  dbize_cci sigma (unitize_env env) com*)

(* Globalization of AST quotations (mainly used in command quotations
   to get statically bound idents in grammar or pretty-printing rules) *)

let ast_adjust_consts sigma = (* locations are kept *)
  let rec dbrec env = function
    | Nvar(loc,s) as ast ->
	(let id = id_of_string s in
	 if Ast.isMeta s then 
	   ast
	 else if Idset.mem id env then 
	   ast
	 else 
	   try 
	     match Declare.global_reference CCI id with
	       | DOPN (Const sp,_) -> 
		   Node(loc,"CONST",[path_section loc sp])
	       | DOPN (Evar ev,_) ->
		   Node(loc,"EVAR",[Num(loc,ev)])
	       | DOPN (MutConstruct ((sp,i),j),_) ->
		   Node (loc,"MUTCONSTRUCT",[path_section loc sp;num i;num j])
	       | DOPN (MutInd (sp,i),_) ->
		   Node (loc,"MUTIND",[path_section loc sp;num i])
	       | _ -> anomaly "Not a reference"
	   with UserError _ | Not_found ->
	     try 
	       let _ = Syntax_def.search_syntactic_definition id in 
	       Node(loc,"SYNCONST",[Nvar(loc,s)])
	     with Not_found -> 
	       warning ("Could not globalize "^s); ast)

    | Slam(loc,None,t) -> Slam(loc,None,dbrec env t)
	 
    | Slam(loc,Some na,t) ->
	let env' = Idset.add (id_of_string na) env in
        Slam(loc,Some na,dbrec env' t)
    | Node(loc,opn,tl) -> Node(loc,opn,List.map (dbrec env) tl)
    | x -> x
  in 
  dbrec

let globalize_command ast =
  let sign = Global.var_context () in
  ast_adjust_consts Evd.empty (from_list (ids_of_var_context sign)) ast

(* Avoid globalizing in non command ast for tactics *)
let rec glob_ast sigma env = function 
  | Node(loc,"COMMAND",[c]) ->
      Node(loc,"COMMAND",[ast_adjust_consts sigma env c])
  | Node(loc,"COMMANDLIST",l) -> 
      Node(loc,"COMMANDLIST", List.map (ast_adjust_consts sigma env) l)
  | Slam(loc,None,t) ->
      Slam(loc,None,glob_ast sigma env t)
  | Slam(loc,Some na,t) ->
      let env' = Idset.add (id_of_string na) env in
      Slam(loc,Some na, glob_ast sigma env' t)
  | Node(loc,opn,tl) -> Node(loc,opn,List.map (glob_ast sigma env) tl)
  | x -> x

let globalize_ast ast =
  let sign = Global.var_context () in
  glob_ast Evd.empty (from_list (ids_of_var_context sign)) ast


(* Installation of the AST quotations. "command" is used by default. *)
let _ = 
  Pcoq.define_quotation true "command" 
    (Pcoq.map_entry globalize_command Pcoq.Constr.constr)
let _ = 
  Pcoq.define_quotation false "tactic" 
    (Pcoq.map_entry globalize_ast Pcoq.Tactic.tactic)
let _ = 
  Pcoq.define_quotation false "vernac" 
    (Pcoq.map_entry globalize_ast Pcoq.Vernac.vernac)


(*********************************************************************)
(* V6 compat: Functions before in ex-trad                            *)

(* Endless^H^H^H^H^H^H^HShort list of alternative ways to call pretyping *)

let interp_constr_gen is_ass sigma env com = 
  let c = interp_rawconstr sigma env com in
  try 
    ise_resolve1 is_ass sigma env c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

let interp_constr sigma env c = interp_constr_gen false sigma env c
let interp_type sigma env   c = interp_constr_gen true sigma env c
let interp_sort = function
  | Node(loc,"PROP", []) -> Prop Null
  | Node(loc,"SET", [])  -> Prop Pos
  | Node(loc,"TYPE", []) -> Type Univ.dummy_univ
  | a -> user_err_loc (Ast.loc a,"interp_sort", [< 'sTR "Not a sort" >])

let judgment_of_com sigma env com = 
  let c = interp_rawconstr sigma env com in
  try
    ise_resolve false sigma [] env [] [] c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

(*To retype a list of key*constr with undefined key*)
let retype_list sigma env lst=
  List.map (fun (x,csr) -> (x,Retyping.get_judgment_of env sigma csr)) lst;;

(*Interprets a constr according to two lists of instantiations (variables and
  metas)*)
let interp_constr1 sigma env lvar lmeta com =
  let c =
    interp_rawconstr_gen sigma env false (List.map (fun x -> string_of_id (fst
      x)) lvar) com
  and rtype=fun lst -> retype_list sigma env lst in
  try
    ise_resolve2 sigma env (rtype lvar) (rtype lmeta) c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

let typed_type_of_com sigma env com =
  let c = interp_rawconstr sigma env com in
  try 
    ise_resolve_type true sigma [] env c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

(* Note: typ is retyped *)

let interp_casted_constr sigma env com typ = 
  ise_resolve_casted sigma env typ (interp_rawconstr sigma env com)

(*Interprets a casted constr according to two lists of instantiations
  (variables and metas)*)
let interp_casted_constr1 sigma env lvar lmeta com typ =
  let c =
    interp_rawconstr_gen sigma env false (List.map (fun x -> string_of_id (fst
      x)) lvar) com
  and rtype=fun lst -> retype_list sigma env lst in 
  ise_resolve_casted_gen true sigma env (rtype lvar) (rtype lmeta) typ c;;

(*
let dbize_fw  sigma env com = dbize FW sigma env com

let raw_fconstr_of_com sigma env com = dbize_fw sigma (unitize_env (context env)) com
let raw_constr_of_compattern sigma env com = 
  dbize_cci sigma (unitize_env env) com

let fconstr_of_com1 is_ass sigma env com = 
  let c = raw_fconstr_of_com sigma env com in
  try 
    ise_resolve1 is_ass sigma env c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e
 
let fconstr_of_com sigma hyps com =
  fconstr_of_com1 false sigma hyps com 

*)
(* Typing with Trad, and re-checking with Mach *)
(* Should be done in two passes by library commands ...
let fconstruct_type sigma sign com =
  let c = constr_of_com1 true sigma sign com in 
  Mach.fexecute_type sigma sign c

let fconstruct sigma sign com =
  let c = constr_of_com1 false sigma sign com in 
  Mach.fexecute sigma sign c

let infconstruct_type sigma (sign,fsign) cmd =
  let c = constr_of_com1 true sigma sign cmd in 
  Mach.infexecute_type sigma (sign,fsign) c

let infconstruct sigma (sign,fsign) cmd =
  let c = constr_of_com1 false sigma sign cmd in 
  Mach.infexecute sigma (sign,fsign) c

(* Type-checks a term with the current universe constraints, the resulting
   constraints are dropped. *)

let univ_sp = make_path ["univ"] (id_of_string "dummy") OBJ

let fconstruct_with_univ sigma sign com =
  let c = constr_of_com sigma sign com in
  let (_,j) = with_universes (Mach.fexecute sigma sign)
		(univ_sp, Constraintab.current_constraints(), c) in 
  j
*)

(* To process patterns, we need a translation from AST to term
   without typing at all. *)

let ctxt_of_ids ids =
  Array.of_list (List.map (function id -> VAR id) ids)

let rec pat_of_ref metas vars = function
  | RConst (sp,ctxt) -> RConst (sp, dbize_rawconstr_ctxt ctxt)
  | RInd (ip,ctxt) -> RInd (ip, dbize_rawconstr_ctxt ctxt)
  | RConstruct(cp,ctxt) ->RConstruct(cp, dbize_rawconstr_ctxt ctxt)
  | REVar (n,ctxt) -> REVar (n, dbize_rawconstr_ctxt ctxt)
  | RAbst _ -> error "pattern_of_rawconstr: not implemented"
  | RVar _ -> assert false (* Capturé dans pattern_of_raw *)

and pat_of_raw metas vars lvar = function
  | RRef (_,RVar id) -> 
      (try PRel (list_index (Name id) vars)
       with Not_found ->
         (try (List.assoc id lvar)
          with Not_found -> PRef (RVar id)))
  | RMeta (_,n) ->
      metas := n::!metas; PMeta (Some n)
  | RRef (_,r) ->
      PRef (pat_of_ref metas vars r)
  (* Hack pour ne pas réécrire une interprétation complète des patterns*)
  | RApp (_, RMeta (_,n), cl) when n<0 ->
      PSoApp (- n, List.map (pat_of_raw metas vars lvar) cl)
  | RApp (_,c,cl) -> 
      PApp (pat_of_raw metas vars lvar c,
	    Array.of_list (List.map (pat_of_raw metas vars lvar) cl))
  | RBinder (_,bk,na,c1,c2) ->
      PBinder (bk, na, pat_of_raw metas vars lvar c1,
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
    dbize CCI sigma (from_list (ids_of_rel_context (rel_context env)))
      true (List.map
	      (fun x ->
		 string_of_id (fst x)) lvar,var_context env) com
  and nlvar = List.map (fun (id,c) -> (id,pattern_of_constr c)) lvar in
  try 
    pattern_of_rawconstr nlvar c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

let interp_constrpattern sigma env com =
  interp_constrpattern_gen sigma env [] com
