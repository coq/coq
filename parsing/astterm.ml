
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
open Typing
open Pretyping
open Evarutil
open Ast
open Coqast

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
    wARN [<'sTR ("Warning: the variable"^s1); vars;
	 'sTR (" start"^s2^" with upper case in pattern"); 'cUT >]

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

let ids_of_ctxt = array_map_to_list (function VAR id -> id | _ -> assert false)

let maybe_constructor env s =
  try 
    match Declare.global_reference CCI (id_of_string s) with 
      | DOPN(MutConstruct (spi,j),cl) -> Some ((spi,j),ids_of_ctxt cl)
      | _ -> None
  with Not_found -> 
    None

let dbize_ctxt = 
  List.map 
    (function
       | Nvar (loc,s) -> ident_of_nvar loc s
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
  | DOPN (Const sp,ctxt) -> RConst (sp,ids_of_ctxt ctxt)
  | DOPN (Evar ev,ctxt) -> REVar (ev,ids_of_ctxt ctxt) 
  | DOPN (MutConstruct (spi,j),ctxt) -> RConstruct ((spi,j),ids_of_ctxt ctxt)
  | DOPN (MutInd (sp,i),ctxt) -> RInd ((sp,i),ids_of_ctxt ctxt)
  | VAR id -> RVar id  (* utilisé dans trad pour coe_value (tmp) *)
  | _ -> anomaly "Not a reference"

let error_var_not_found str loc s = 
  Util.user_err_loc 
    (loc,str,
     [< 'sTR "The variable"; 'sPC; 'sTR s;
	'sPC ; 'sTR "was not found"; 
	'sPC ; 'sTR "in the current"; 'sPC ; 'sTR "environment" >])

let dbize_ref k sigma env loc s =
  let id = ident_of_nvar loc s in
  try 
    match lookup_id id env with
      | RELNAME(n,_) -> RRel (loc,n),[]
      | _ -> 
	  RRef(loc,RVar id), (try implicits_of_var k id with _ -> [])
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
	error_var_not_found "dbize_ref" loc s
	  
let mkLambdaC (x,a,b) = ope("LAMBDA",[a;slam(Some (string_of_id x),b)])
let mkLambdaCit = List.fold_right (fun (x,a) b -> mkLambdaC(x,a,b))
let mkProdC (x,a,b) = ope("PROD",[a;slam(Some (string_of_id x),b)])
let mkProdCit = List.fold_right (fun (x,a) b -> mkProdC(x,a,b))

let destruct_binder = function
  | Node(_,"BINDER",c::idl) ->
      List.map (fun id -> (id_of_string (nvar_of_ast id),c)) idl
  | _ -> anomaly "BINDER is expected"
	
let rec dbize_pattern env = function
  | Node(_,"PATTAS",[Nvar (loc,s); p]) ->
      (match name_of_nvar s with
	 | Anonymous -> dbize_pattern env p
	 | Name id   -> 
	     let (ids,p') = dbize_pattern env p in (id::ids,PatAs (loc,id,p')))
  | Node(_,"PATTCONSTRUCT", Nvar(loc,s)::((_::_) as pl)) ->
      (match maybe_constructor env s with
	 | Some c ->
	     let (idsl,pl') = List.split (List.map (dbize_pattern env) pl) in
	     (List.flatten idsl,PatCstr (loc,c,pl'))
	 | None ->
	     user_err_loc (loc,"dbize_pattern",mssg_hd_is_not_constructor s))
  | Nvar(loc,s) ->
      (match name_of_nvar s with
	 | Anonymous -> ([], PatVar (loc,Anonymous))
	 | Name id as name -> ([id], PatVar (loc,name)))
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

let rec collapse_env n env = if n=0 then env else
  add_rel (Anonymous,()) (collapse_env (n-1) (snd (uncons_rel_env env)))

let dbize k sigma =
  let rec dbrec env = function
    | Nvar(loc,s) -> fst (dbize_ref k sigma env loc s)
	  
   (*
   | Slam(_,ona,Node(_,"V$",l)) ->
       let na =
         (match ona with Some s -> Name (id_of_string s) | _ -> Anonymous)
       in DLAMV(na,Array.of_list (List.map (dbrec (add_rel (na,()) env)) l))

   | Slam(_,ona,t) ->
       let na =
         (match ona with Some s -> Name (id_of_string s) | _ -> Anonymous)
       in DLAM(na, dbrec (add_rel (na,()) env) t)
   *)
    | Node(loc,"FIX", (Nvar (locid,iddef))::ldecl) ->
	let (lf,ln,lA,lt) = dbize_fix ldecl in
	let n =
	  try 
	    (list_index (ident_of_nvar locid iddef) lf) -1
          with Failure _ ->
	    error_fixname_unbound "dbize (FIX)" false locid iddef in
	let ext_env =
	  List.fold_left (fun env fid -> add_rel (Name fid,()) env) env lf in
	let defl = Array.of_list (List.map (dbrec ext_env) lt) in
	let arityl = Array.of_list (List.map (dbrec env) lA) in
	RRec (loc,RFix (Array.of_list ln,n), Array.of_list lf, arityl, defl)
	  
    | Node(loc,"COFIX", (Nvar(locid,iddef))::ldecl) ->
	let (lf,lA,lt) = dbize_cofix ldecl in
	let n =
          try 
	    (list_index (ident_of_nvar locid iddef) lf) -1
          with Failure _ ->
	    error_fixname_unbound "dbize (COFIX)" true locid iddef in
	let ext_env =
	  List.fold_left (fun env fid -> add_rel (Name fid,()) env) env lf in
	let defl = Array.of_list (List.map (dbrec ext_env) lt) in
	let arityl = Array.of_list (List.map (dbrec env) lA) in
	RRec (loc,RCofix n, Array.of_list lf, arityl, defl)
	  
    | Node(loc,("PROD"|"LAMBDA" as k), [c1;Slam(_,ona,c2)]) ->
	let na = match ona with
	  | Some s -> Name (id_of_string s)
	  | _ -> Anonymous in
	let kind = if k="PROD" then BProd else BLambda in
	RBinder(loc, kind, na, dbrec env c1, dbrec (add_rel (na,()) env) c2)

    | Node(_,"PRODLIST", [c1;(Slam _ as c2)]) -> 
	iterated_binder BProd 0 c1 env c2
    | Node(_,"LAMBDALIST", [c1;(Slam _ as c2)]) -> 
	iterated_binder BLambda 0 c1 env c2

    | Node(loc,"APPLISTEXPL", f::args) ->
	RApp (loc,dbrec env f,List.map (dbrec env) args)
    | Node(loc,"APPLIST", Nvar(locs,s)::args) ->
	let (c, impargs) = dbize_ref k sigma env locs s in
	RApp (loc, c, dbize_args env impargs args)
    | Node(loc,"APPLIST", f::args) ->	   
	RApp (loc,dbrec env f,List.map (dbrec env) args)
	  
    | Node(loc,"MULTCASE", p:: Node(_,"TOMATCH",tms):: eqns) ->
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
    | Node(loc,"META",[Num(_,n)]) -> RRef (loc,RMeta n)

    | Node(loc,"PROP", []) -> RSort(loc,RProp Null)
    | Node(loc,"SET", [])  -> RSort(loc,RProp Pos)
    | Node(loc,"TYPE", []) -> RSort(loc,RType)
	  
    (* This case mainly parses things build from   in a quotation *)
    | Node(loc,("CONST"|"EVAR"|"MUTIND"|"MUTCONSTRUCT"|"SYNCONST" as key),l) ->
	dbize_global loc (key,l)

    | Node(loc,opn,tl) -> 
	anomaly ("dbize found operator "^opn^" with "^
		 (string_of_int (List.length tl))^" arguments")

    | _ -> anomaly "dbize: unexpected ast"

  and dbize_eqn n env = function
    | Node(loc,"EQN",rhs::lhs) ->
	let (idsl,pl) = List.split (List.map (dbize_pattern env) lhs) in
	let ids = List.flatten idsl in
	check_linearity loc ids;
	check_uppercase loc ids;
	check_number_of_pattern loc n pl;
	let env' =
	  List.fold_left (fun env id -> add_rel (Name id,()) env) env ids in
	(ids,pl,dbrec env' rhs)
    | _ -> anomaly "dbize: badly-formed ast for Cases equation"

  and iterated_binder oper n ty env = function
    | Slam(loc,ona,body) ->
	let na = match ona with 
	  | Some s -> Name (id_of_string s) 
	  | _ -> Anonymous
	in 
	RBinder(loc, oper, na, 
		dbrec (collapse_env n env) ty, (* To avoid capture *)
		(iterated_binder oper n ty (add_rel (na,()) env) body))
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
  dbrec

let dbize_cci sigma env com = dbize CCI sigma env com
let dbize_fw  sigma env com = dbize FW sigma env com

(* constr_of_com takes an environment of typing assumptions,
 * and translates a command to a constr. *)

let raw_constr_of_com sigma env com = dbize_cci sigma (unitize_env env) com
let raw_fconstr_of_com sigma env com = dbize_fw sigma (unitize_env env) com
let raw_constr_of_compattern sigma env com = 
  dbize_cci sigma (unitize_env env) com


(* Globalization of AST quotations (mainly used in command quotations
   to get statically bound idents in grammar or pretty-printing rules) *)

let ast_adjust_consts sigma = (* locations are kept *)
  let rec dbrec env = function
    | Nvar(loc,s) as ast ->
	(let id = id_of_string s in
	 if Ast.isMeta s then 
	   ast
	 else if List.mem id (ids_of_env env) then 
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

    | Slam(loc,None,t) -> Slam(loc,None,dbrec (add_rel (Anonymous,()) env) t)
	 
    | Slam(loc,Some na,t) ->
	let env' = add_rel (Name (id_of_string na),()) env in
        Slam(loc,Some na,dbrec env' t)
    | Node(loc,opn,tl) -> Node(loc,opn,List.map (dbrec env) tl)
    | x -> x
  in 
  dbrec

let globalize_command ast =
  let sign = Global.var_context () in
  ast_adjust_consts Evd.empty (gLOB sign) ast

(* Avoid globalizing in non command ast for tactics *)
let rec glob_ast sigma env = function 
  | Node(loc,"COMMAND",[c]) ->
      Node(loc,"COMMAND",[ast_adjust_consts sigma env c])
  | Node(loc,"COMMANDLIST",l) -> 
      Node(loc,"COMMANDLIST", List.map (ast_adjust_consts sigma env) l)
  | Slam(loc,None,t) ->
      Slam(loc,None,glob_ast sigma (add_rel (Anonymous,()) env) t)
  | Slam(loc,Some na,t) ->
      let env' = add_rel (Name (id_of_string na),()) env in
      Slam(loc,Some na, glob_ast sigma env' t)
  | Node(loc,opn,tl) -> Node(loc,opn,List.map (glob_ast sigma env) tl)
  | x -> x

let globalize_ast ast =
  let sign = Global.var_context () in
  glob_ast Evd.empty (gLOB sign) ast


(* Installation of the AST quotations. "command" is used by default. *)
let _ = 
  Pcoq.define_quotation true "command" 
    (Pcoq.map_entry globalize_command Pcoq.Command.command)
let _ = 
  Pcoq.define_quotation false "tactic" 
    (Pcoq.map_entry globalize_ast Pcoq.Tactic.tactic)
let _ = 
  Pcoq.define_quotation false "vernac" 
    (Pcoq.map_entry globalize_ast Pcoq.Vernac.vernac)


(*********************************************************************)
(* Functions before in ex-trad                                       *)

(* Endless list of alternative ways to call Trad *)

(* With dB *)

let constr_of_com_env1 is_ass sigma env com = 
  let c = raw_constr_of_com sigma (context env) com in
  try 
    ise_resolve1 is_ass sigma env c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

let constr_of_com_env sigma env com =
  constr_of_com_env1 false sigma env com
    
let fconstr_of_com_env1 is_ass sigma env com = 
  let c = raw_fconstr_of_com sigma (context env) com in
  try 
    ise_resolve1 is_ass sigma env c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e
 
let fconstr_of_com_env sigma hyps com =
  fconstr_of_com_env1 false sigma hyps com 
    
let judgment_of_com1 is_ass sigma env com = 
  let c = raw_constr_of_com sigma (context env) com in
  try 
    ise_resolve is_ass sigma [] env c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

let judgment_of_com sigma env com =
  judgment_of_com1 false sigma env com

(* Without dB *)
let type_of_com env com =
  let sign = context env in
  let c = raw_constr_of_com Evd.empty sign com in
  try 
    ise_resolve_type true Evd.empty [] env c
  with e -> 
    Stdpp.raise_with_loc (Ast.loc com) e

let constr_of_com1 is_ass sigma env com = 
  constr_of_com_env1 is_ass sigma env com
    
let constr_of_com sigma env com =
  constr_of_com1 false sigma env com

let constr_of_com_sort sigma sign com =
  constr_of_com1 true sigma sign com

let constr_of_com_pattern sigma sign com =
  constr_of_com1 true sigma sign com

let fconstr_of_com1 is_ass sigma env com = 
  fconstr_of_com_env1 is_ass sigma env com

let fconstr_of_com sigma sign com  =
  fconstr_of_com1 false sigma sign com
let fconstr_of_com_sort sigma sign com  =
  fconstr_of_com1 true sigma sign com

(* Note: typ is retyped *)

let constr_of_com_casted sigma env com typ = 
  let sign = context env in
  ise_resolve_casted sigma env typ (raw_constr_of_com sigma sign com)

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

open Closure
open Tacred

(* Translation of reduction expression: we need trad because of Fold
 * Moreover, reduction expressions are used both in tactics and in
 * vernac. *)

let glob_nvar com =
  let s = nvar_of_ast com in
  try 
    Nametab.sp_of_id CCI (id_of_string s)
  with Not_found -> 
    error ("unbound variable "^s)

let cvt_pattern sigma env = function
  | Node(_,"PATTERN", Node(_,"COMMAND",[com])::nums) ->
      let occs = List.map num_of_ast nums in
      let c = constr_of_com sigma env com in
      let j = Typing.unsafe_machine env sigma c in
      (occs, j.uj_val, j.uj_type)
  | arg -> invalid_arg_loc (Ast.loc arg,"cvt_pattern")

let cvt_unfold = function
  | Node(_,"UNFOLD", com::nums) -> (List.map num_of_ast nums, glob_nvar com)
  | arg -> invalid_arg_loc (Ast.loc arg,"cvt_unfold")

let cvt_fold sigma sign = function
  | Node(_,"COMMAND",[c]) -> constr_of_com sigma sign c
  | arg -> invalid_arg_loc (Ast.loc arg,"cvt_fold")

let flag_of_ast lf =
  let beta = ref false in
  let delta = ref false in
  let iota = ref false in
  let idents = ref (None: (sorts oper -> bool) option) in
  let set_flag = function
    | Node(_,"Beta",[]) -> beta := true
    | Node(_,"Delta",[]) -> delta := true
    | Node(_,"Iota",[]) -> iota := true
    | Node(loc,"Unf",l) ->
        if !delta then
          if !idents = None then
            let idl = List.map glob_nvar l in
            idents := Some
              (function
                 | Const sp -> List.mem sp idl
                 | Abst sp -> List.mem sp idl
                 | _ -> false)
          else 
	    user_err_loc
	      (loc,"flag_of_ast",
	       [< 'sTR"Cannot specify identifiers to unfold twice" >])
        else 
	  user_err_loc(loc,"flag_of_ast",
                       [< 'sTR"Delta must be specified before" >])
    | Node(loc,"UnfBut",l) ->
        if !delta then
          if !idents = None then
            let idl = List.map glob_nvar l in
            idents := Some
              (function
                 | Const sp -> not (List.mem sp idl)
                 | Abst sp -> not (List.mem sp idl)
                 | _ -> false)
          else 
	    user_err_loc
	      (loc,"flag_of_ast",
	       [< 'sTR"Cannot specify identifiers to unfold twice" >])
        else 
	  user_err_loc(loc,"flag_of_ast",
                       [< 'sTR"Delta must be specified before" >])
    | arg -> invalid_arg_loc (Ast.loc arg,"flag_of_ast")
  in
  List.iter set_flag lf;
  { r_beta = !beta;
    r_iota = !iota;
    r_delta = match (!delta,!idents) with
      | (false,_) -> (fun _ -> false)
      | (true,None) -> (fun _ -> true)
      | (true,Some p) -> p }
  
let redexp_of_ast sigma sign = function
  | ("Red", []) -> Red
  | ("Hnf", []) -> Hnf
  | ("Simpl", []) -> Simpl
  | ("Unfold", ul) -> Unfold (List.map cvt_unfold ul)
  | ("Fold", cl) -> Fold (List.map (cvt_fold sigma sign) cl)
  | ("Cbv",lf) -> Cbv(UNIFORM, flag_of_ast lf)
  | ("Lazy",lf) -> Lazy(UNIFORM, flag_of_ast lf)
  | ("Pattern",lp) -> Pattern (List.map (cvt_pattern sigma sign) lp)
  | (s,_) -> invalid_arg ("malformed reduction-expression: "^s)

