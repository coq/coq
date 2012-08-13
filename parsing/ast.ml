(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Libnames
open Coqast
open Topconstr
open Genarg

let isMeta s = String.length s <> 0 & s.[0]='$'

let loc = function
  | Node (loc,_,_) -> loc
  | Nvar (loc,_) -> loc
  | Nmeta (loc,_) -> loc
  | Slam (loc,_,_) -> loc
  | Smetalam (loc,_,_) -> loc
  | Num (loc,_) -> loc
  | Id (loc,_) -> loc
  | Str (loc,_) -> loc
  | Path (loc,_) -> loc
  | Dynamic (loc,_) -> loc

(* patterns of ast *)
type astpat =
  | Pquote of t
  | Pmeta of string * tok_kind
  | Pnode of string * patlist
  | Pslam of identifier option * astpat
  | Pmeta_slam of string * astpat

and patlist =
  | Pcons of astpat * patlist
  | Plmeta of string
  | Pnil

and tok_kind = Tnum | Tid | Tstr | Tpath | Tvar | Tany | Tlist

type pat =
  | AstListPat of patlist
  | PureAstPat of astpat

(* building a node with dummy location *)

let ope(op,l) = Node(dummy_loc,op,l)
let slam(idl,b) = Slam(dummy_loc,idl,b)
let ide s = Id(dummy_loc,s)
let nvar s = Nvar(dummy_loc,s)
let num n = Num(dummy_loc,n)
let string s = Str(dummy_loc,s)
let path sl = Path(dummy_loc,sl)
let dynamic d = Dynamic(dummy_loc,d)

let rec set_loc loc = function
  | Node(_,op,al) -> Node(loc, op, List.map (set_loc loc) al)
  | Slam(_,idl,b) -> Slam(loc,idl, set_loc loc b)
  | Smetalam(_,idl,b) -> Smetalam(loc,idl, set_loc loc b)
  | Nvar(_,s) -> Nvar(loc,s)
  | Nmeta(_,s) -> Nmeta(loc,s)
  | Id(_,s) -> Id(loc,s)
  | Str(_,s) -> Str(loc,s)
  | Num(_,s) -> Num(loc,s)
  | Path(_,sl) -> Path(loc,sl)
  | Dynamic(_,d) -> Dynamic(loc,d)

let path_section loc sp = Coqast.Path(loc, sp)

let section_path sp = sp

(* ast destructors *)
let num_of_ast = function
  | Num(_,n) -> n
  | ast -> invalid_arg_loc (loc ast, "Ast.num_of_ast")

let nvar_of_ast = function
  | Nvar(_,s) -> s
  | ast -> invalid_arg_loc (loc ast, "Ast.nvar_of_ast")

let meta_of_ast = function
  | Nmeta(_,s) -> s
  | ast -> invalid_arg_loc (loc ast, "Ast.nvar_of_ast")

let id_of_ast =  function
  | Id(_,s) -> s
  | ast -> invalid_arg_loc (loc ast, "Ast.nvar_of_ast")

(* semantic actions of grammar rules *)
type act =
  | Act of constr_expr
  | ActCase of act * (pat * act) list
  | ActCaseList of act * (pat * act) list

(* values associated to variables *)
(*
type typed_ast =
  | AstListNode of Coqast.t list
  | PureAstNode of Coqast.t
*)
type typed_ast =
  | AstListNode of Coqast.t list
  | PureAstNode of Coqast.t

type ast_action_type = ETast | ETastl

type dynamic_grammar =
  | ConstrNode of constr_expr
  | CasesPatternNode of cases_pattern_expr

type grammar_action =
  | SimpleAction of loc * dynamic_grammar
  | CaseAction of
      loc * grammar_action * ast_action_type * (t list * grammar_action) list

type env = (string * typed_ast) list

let string_of_dirpath = function
  | [] -> "<empty>"
  | sl ->
      String.concat "." (List.map string_of_id (List.rev sl))

let pr_id id = str (string_of_id id)

let print_kn kn =
  let (mp,dp,l) = repr_kn kn in
  let dpl = repr_dirpath dp in
  str (string_of_mp mp) ++ str "." ++
  prlist_with_sep (fun _ -> str".") pr_id dpl ++
  str (string_of_label l)

(* Pretty-printing *)
let rec print_ast ast =
  match ast with
    | Num(_,n) -> int n
    | Str(_,s) -> qs s
    | Path(_,sl) -> print_kn sl
    | Id (_,s) -> str "{" ++ str s ++ str "}"
    | Nvar(_,s) -> pr_id s
    | Nmeta(_,s) -> str s
    | Node(_,op,l) ->
        hov 3 (str "(" ++ str op ++ spc () ++ print_astl l ++ str ")")
    | Slam(_,None,ast) -> hov 1 (str "[<>]" ++ print_ast ast)
    | Slam(_,Some x,ast) ->
        hov 1
          (str "[" ++ pr_id x ++ str "]" ++ cut () ++ 
	   print_ast ast)
    | Smetalam(_,id,ast) -> hov 1 (str id ++ print_ast ast)
    | Dynamic(_,d) ->
	hov 0 (str "<dynamic: " ++ str (Dyn.tag d) ++ str ">")

and print_astl astl =
  prlist_with_sep pr_spc print_ast astl

let print_ast_cast = function
  | Tany -> (mt ())
  | Tvar -> (str":var")
  | Tid -> (str":id")
  | Tstr -> (str":str")
  | Tpath -> (str":path")
  | Tnum -> (str":num")
  | Tlist -> (str":list")

let rec print_astpat = function
  | Pquote ast -> 
      str"'" ++ print_ast ast 
  | Pmeta(s,tk) -> 
      str s ++ print_ast_cast tk 
  | Pmeta_slam(s,b) ->
      hov 1 (str "[" ++ str s ++ str"]" ++ cut () ++ print_astpat b)
  | Pnode(op,al) ->
      hov 2 (str"("  ++ str op ++ spc () ++ print_astlpat al ++ str")" )
  | Pslam(None,b) -> 
      hov 1 (str"[<" ++ cut () ++ print_astpat b)
  | Pslam(Some id,b) ->
      hov 1
        (str"[" ++ str(string_of_id id) ++ str"]" ++ cut () ++ print_astpat b)

and print_astlpat = function
  | Pnil -> mt ()
  | Pcons(h,Pnil) -> hov 1 (print_astpat h)
  | Pcons(h,t) -> hov 1 (print_astpat h ++ spc () ++ print_astlpat t)
  | Plmeta(s) -> str"| " ++ str s


let print_val = function
  | PureAstNode a -> print_ast a
  | AstListNode al -> 
      hov 1 (str"[" ++ prlist_with_sep pr_spc print_ast al ++ str"]")

(* Ast values environments *)

let grammar_type_error (loc,s) =
  anomaly_loc (loc,s,(str"grammar type error: " ++ str s))


(* Coercions enforced by the user *)
let check_cast loc a k =
  match (k,a) with
    | (Tany, _) -> ()
    | (Tid, Id _) -> ()
    | (Tvar, Nvar _) -> ()
    | (Tpath, Path _) -> ()
    | (Tstr, Str _) -> ()
    | (Tnum, Num _) -> ()
    | (Tlist, _) -> grammar_type_error (loc,"Ast.cast_val")
    | _ -> user_err_loc (loc,"Ast.cast_val",
                         (str"cast _" ++ print_ast_cast k ++ str"failed"))

let rec coerce_to_var = function
  | Nvar(_,id) as var -> var
  | Nmeta(_,id) as var -> var
  | Node(_,"QUALID",[Nvar(_,id) as var]) -> var
  | ast -> user_err_loc
        (loc ast,"Ast.coerce_to_var",
         (str"This expression should be a simple identifier"))

let coerce_to_id_ast a = match coerce_to_var a with
  | Nvar (_,id) -> id
  | ast -> user_err_loc
        (loc ast,"Ast.coerce_to_id",
         str"This expression should be a simple identifier")

let coerce_to_id = function
  | CRef (Ident (loc,id)) -> (loc,id)
  | a -> user_err_loc
        (constr_loc a,"Ast.coerce_to_id",
         str"This expression should be a simple identifier")

let coerce_reference_to_id = function
  | Ident (_,id) -> id
  | Qualid (loc,_) ->
      user_err_loc (loc, "Ast.coerce_reference_to_id",
        str"This expression should be a simple identifier")

let coerce_global_to_id = coerce_reference_to_id

(* Pattern-matching on ast *)

let env_assoc_value loc v env =
  try 
    List.assoc v env
  with Not_found -> 
    anomaly_loc
      (loc,"Ast.env_assoc_value",
       (str"metavariable " ++ str v ++ str" is unbound"))

let env_assoc_list sigma (loc,v) =
  match env_assoc_value loc v sigma with
    | AstListNode al -> al
    | PureAstNode a -> [a]

let env_assoc sigma k (loc,v) =
  match env_assoc_value loc v sigma with
    | PureAstNode a -> check_cast loc a k; a
    | _ -> grammar_type_error (loc,"Ast.env_assoc: "^v^" is an ast list")

let env_assoc_nvars sigma (dloc,v) =
  match env_assoc_value dloc v sigma with
    | AstListNode al -> List.map coerce_to_id_ast al
    | PureAstNode ast -> [coerce_to_id_ast ast]

let build_lams dloc idl ast =
  List.fold_right (fun id lam -> Slam(dloc,Some id,lam)) idl ast

(* Alpha-conversion *)
	  
let rec alpha_var id1 id2 = function
  | (i1,i2)::_ when i1=id1 -> i2 = id2
  | (i1,i2)::_ when i2=id2 -> i1 = id1
  | _::idl -> alpha_var id1 id2 idl
  | [] -> id1 = id2

let rec alpha alp a1 a2 =
  match (a1,a2) with
    | (Node(_,op1,tl1),Node(_,op2,tl2)) ->
        (op1 = op2) & (List.length tl1 = List.length tl2)
        & (List.for_all2 (alpha alp) tl1 tl2)
    | (Nvar(_,id1),Nvar(_,id2)) -> alpha_var id1 id2 alp
    | (Slam(_,None,body1),Slam(_,None,body2)) -> alpha alp body1 body2
    | (Slam(_,Some s1,body1),Slam(_,Some s2,body2)) ->
        alpha ((s1,s2)::alp) body1 body2
    | (Id(_,s1),Id(_,s2)) -> s1=s2
    | (Str(_,s1),Str(_,s2)) -> s1=s2
    | (Num(_,n1),Num(_,n2)) -> n1=n2
    | (Path(_,sl1),Path(_,sl2)) -> sl1=sl2
    | ((Smetalam _ | Nmeta _ | Dynamic _), _) -> false
    | (_, (Smetalam _ | Nmeta _ | Dynamic _)) -> false
    | _ -> false

let alpha_eq (a1,a2)= alpha [] a1 a2

let alpha_eq_val (x,y) = x = y
(*
let alpha_eq_val = function
  | (Vast a1, Vast a2) -> alpha_eq (a1,a2)
  | (Vastlist al1, Vastlist al2) ->
      (List.length al1 = List.length al2)
      & List.for_all2 (fun x y -> alpha_eq (x,y)) al1 al2
  | _ ->  false
*)

exception No_match of string

let no_match_loc (loc,s) = Stdpp.raise_with_loc loc (No_match s)

(* Binds value v to variable var. If var is already bound, checks if
   its value is alpha convertible with v. This allows non-linear patterns.

   Important note: The Metavariable $_ is a special case; it cannot be
   bound, which is like _ in the ML matching. *)

let bind_env sigma var v =
  if var = "$_" then 
    sigma
  else
    try
      let vvar = List.assoc var sigma in
      if alpha_eq_val (v,vvar) then sigma
      else raise (No_match "Ast.bind_env: values do not match")
    with Not_found -> 
      (var,v)::sigma

let bind_env_ast sigma var ast =
  try 
    bind_env sigma var (PureAstNode ast)
  with e -> 
    Stdpp.raise_with_loc (loc ast) e

let alpha_define sigma loc ps s =
  try 
    let _ = List.assoc ps sigma in sigma
  with Not_found ->
    if ps = "$_" then sigma else (ps, PureAstNode(Nvar(loc,s)))::sigma


(* Match an ast with an ast pattern. Returns the new environnement. *)

let rec amatch alp sigma spat ast =
  match (spat,ast) with
    | (Pquote a, _) ->
        if alpha alp a ast then 
	  sigma
        else 
	  no_match_loc (loc ast,"quote does not match")
    | (Pmeta(pv,Tany), _) -> bind_env_ast sigma pv ast
    | (Pmeta(pv,Tvar), Nvar _) -> bind_env_ast sigma pv ast
    | (Pmeta(pv,Tid), Id _) -> bind_env_ast sigma pv ast
    | (Pmeta(pv,Tnum), Num _) -> bind_env_ast sigma pv ast
    | (Pmeta(pv,Tstr), Str _) -> bind_env_ast sigma pv ast
    | (Pmeta(pv,Tpath), Path _) -> bind_env_ast sigma pv ast
    | (Pmeta(pv,Tlist),_) -> grammar_type_error (loc ast,"Ast.amatch")
    | (Pmeta_slam(pv,pb), Slam(loc, Some s, b)) ->
        amatch alp (bind_env_ast sigma pv (Nvar(loc,s))) pb b
    | (Pmeta_slam(pv,pb), Slam(loc, None, b)) ->
        amatch alp (bind_env_ast sigma pv (Nvar(loc,id_of_string "_"))) pb b
    | (Pmeta_slam(pv,pb), Smetalam(loc, s, b)) ->
	anomaly "amatch: match a pattern with an open ast"
    | (Pnode(nodp,argp), Node(loc,op,args)) when nodp = op ->
        (try amatchl alp sigma argp args
         with e -> Stdpp.raise_with_loc loc e)
    | (Pslam(None,bp), Slam(_,None,b)) -> amatch alp sigma bp b
    | (Pslam(Some ps,bp), Slam(_,Some s,b)) -> amatch ((ps,s)::alp) sigma bp b
    | _ -> no_match_loc (loc ast, "Ast.amatch")

and amatchl alp sigma spatl astl =
  match (spatl,astl) with
    | (Pnil, []) -> sigma
    | (Pcons(pat,patl), ast::asttl) ->
        amatchl alp (amatch alp sigma pat ast) patl asttl
    | (Plmeta pv, _) -> bind_env sigma pv (AstListNode astl)
    | _ -> raise (No_match "Ast.amatchl")

let ast_match = amatch []

let typed_ast_match env p a = match (p,a) with
  | PureAstPat p, PureAstNode a -> amatch [] env p a
  | AstListPat pl, AstListNode al -> amatchl [] env pl al
  | _ -> failwith "Ast.typed_ast_match: TODO"

let astl_match = amatchl []

let first_match pat_of_fun env ast sl =
  let rec aux = function
    | [] -> None
    | h::t ->
        (try Some (h, ast_match env (pat_of_fun h) ast)
         with (No_match _| Compat.Exc_located (_,No_match _)) -> aux t)
  in 
  aux sl

let find_all_matches pat_of_fun env ast sl =
  let rec aux = function
    | [] -> []
    | (h::t) ->
        let l = aux t in
        (try (h, ast_match env (pat_of_fun h) ast)::l
         with (No_match _| Compat.Exc_located (_,No_match _)) -> l)
  in 
  aux sl

let first_matchl patl_of_fun env astl sl =
  let rec aux = function
    | [] -> None
    | (h::t) ->
        (try Some (h, astl_match env (patl_of_fun h) astl)
         with (No_match _| Compat.Exc_located (_,No_match _)) -> aux t)
  in 
  aux sl
    
let bind_patvar env loc v etyp =
  try
    if List.assoc v env = etyp then 
      env
    else 
      user_err_loc
	(loc,"Ast.bind_patvar",
	 (str"variable " ++ str v ++
            str" is bound several times with different types"))
  with Not_found -> 
    if v="$_" then env else (v,etyp)::env
      
let make_astvar env loc v cast =
  let env' = bind_patvar env loc v ETast in
  (Pmeta(v,cast), env')

(* Note: no metavar in operator position. necessary ? *)
let rec pat_of_ast env ast =
  match ast with
    | Nmeta(loc,pv) -> make_astvar env loc pv Tany
(* Obsolète
    | Id(loc,pv) when isMeta pv -> make_astvar env loc pv Tid
*)
    | Smetalam(loc,s,a) ->
        let senv = bind_patvar env loc s ETast in
        let (pa,env') = pat_of_ast senv a in
        (Pmeta_slam(s, pa), env')
    | Node(_,"$VAR",[Nmeta(loc,pv)]) ->
        make_astvar env loc pv Tvar
    | Node(_,"$ID",[Nmeta(loc,pv)]) ->
        make_astvar env loc pv Tid
    | Node(_,"$NUM",[Nmeta(loc,pv)]) ->
        make_astvar env loc pv Tnum
    | Node(_,"$STR",[Nmeta(loc,pv)]) ->
        make_astvar env loc pv Tstr
    | Node(_,"$PATH",[Nmeta(loc,pv)]) ->
        make_astvar env loc pv Tpath
    | Node(_,"$QUOTE",[qast]) -> (Pquote (set_loc dummy_loc qast), env)

   (* This may occur when the meta is not textual but bound by coerce_to_id*)
    | Slam(loc,Some id,b) when isMeta (string_of_id id) ->
	let s = string_of_id id in
        let senv = bind_patvar env loc s ETast in
        let (pb,env') = pat_of_ast senv b in
        (Pmeta_slam(s, pb), env')

    | Slam(_,os,b) ->
        let (pb,env') = pat_of_ast env b in
        (Pslam(os,pb), env')
    | Node(loc,op,_) when isMeta op ->
        user_err_loc(loc,"Ast.pat_of_ast",
                     (str"no patvar in operator position."))
    | Node(_,op,args) ->
        let (pargs, env') = patl_of_astl env args in
        (Pnode(op,pargs), env')
(* Compatibility with new parsing mode *)
    | Nvar(loc,id) when (string_of_id id).[0] = '$' -> make_astvar env loc (string_of_id id) Tany
    | (Path _|Num _|Id _|Str _ |Nvar _) -> (Pquote (set_loc dummy_loc ast), env)
    | Dynamic(loc,_) ->
        invalid_arg_loc(loc,"pat_of_ast: dynamic")
	  
and patl_of_astl env astl =
  match astl with
    | [Node(_,"$LIST",[Nmeta(loc,pv)])] ->
        let penv = bind_patvar env loc pv ETastl in
        (Plmeta pv, penv)
    | [] -> (Pnil,env)
    | ast::asttl ->
        let (p1,env1) = pat_of_ast env ast in
        let (ptl,env2) = patl_of_astl env1 asttl in
        (Pcons (p1,ptl), env2)

type entry_env = (string * ast_action_type) list
	
let to_pat = pat_of_ast

(* Substitution *)

(* Locations in quoted ast are wrong (they refer to the right hand
   side of a grammar rule). A default location dloc is used whenever
   we create an ast constructor. Locations in the binding list are trusted. *)

(* For old ast printer *)
let rec pat_sub dloc sigma pat =
  match pat with
    | Pmeta(pv,c) -> env_assoc sigma c (dloc,pv) 
    | Pmeta_slam(pv,p) ->
        let idl = env_assoc_nvars sigma (dloc,pv) in
        build_lams dloc idl (pat_sub dloc sigma p)
    | Pquote a -> set_loc dloc a
    | Pnode(op,pl) -> Node(dloc, op, patl_sub dloc sigma pl)
    | Pslam(os,p) -> Slam(dloc, os, pat_sub dloc sigma p)
	  
and patl_sub dloc sigma pl =
  match pl with
    | Pnil -> 
	[]
    | Plmeta pv -> 
	env_assoc_list sigma (dloc,pv)
    | Pcons(Pmeta(pv,Tlist), ptl) ->
        (env_assoc_list sigma (dloc,pv))@(patl_sub dloc sigma ptl)
    | Pcons(p1,ptl) -> 
	(pat_sub dloc sigma p1)::(patl_sub dloc sigma ptl)

(* Converting and checking free meta-variables *)

(* For old ast printer *)
let type_of_meta env loc pv =
  try 
    List.assoc pv env
  with Not_found ->
    user_err_loc (loc,"Ast.type_of_meta",
                  (str"variable " ++ str pv ++ str" is unbound"))

(* For old ast printer *)
let check_ast_meta env loc pv =
  match type_of_meta env loc pv with
    | ETast -> ()
    | _ ->
	user_err_loc (loc,"Ast.check_ast_meta",
                      (str"variable " ++ str pv ++ str" is not of ast type"))

(* For old ast printer *)
let rec val_of_ast env = function
  | Nmeta(loc,pv) -> 
      check_ast_meta env loc pv;
      Pmeta(pv,Tany)
  | Node(_,"$QUOTE",[qast]) -> Pquote (set_loc dummy_loc qast)
  | Smetalam(loc,s,a) ->
    let _ = type_of_meta env loc s in (* ids are coerced to id lists *)
    Pmeta_slam(s, val_of_ast env a)
  | (Path _|Num _|Id _|Str _|Nvar _ as ast) -> Pquote (set_loc dummy_loc ast)
  | Slam(_,os,b) -> Pslam(os, val_of_ast env b)
  | Node(loc,op,_) when isMeta op ->
      user_err_loc(loc,"Ast.val_of_ast",
                   (str"no patvar in operator position."))
  | Node(_,op,args) -> Pnode(op, vall_of_astl env args)
  | Dynamic(loc,_) ->
      invalid_arg_loc(loc,"val_of_ast: dynamic")
	  
and vall_of_astl env = function
  | (Node(loc,"$LIST",[Nmeta(locv,pv)]))::asttl ->
      if type_of_meta env locv pv = ETastl then
	if asttl = [] then 
	  Plmeta pv
	else 
	  Pcons(Pmeta(pv,Tlist), vall_of_astl env asttl)
      else
	user_err_loc
	  (loc,"Ast.vall_of_astl",
	    str"variable " ++ str pv ++ str" is not a List")
  | ast::asttl -> Pcons (val_of_ast env ast, vall_of_astl env asttl)
  | [] -> Pnil

(* For old ast printer *)
let rec occur_var_ast s = function
  | Node(_,"QUALID",_::_::_) -> false
  | Node(_,"QUALID",[Nvar(_,s2)]) -> s = s2
  | Nvar(_,s2) -> s = s2
  | Node(loc,op,args) -> List.exists (occur_var_ast s) args
  | Smetalam _ | Nmeta _ -> anomaly "occur_var: metas should not occur here"
  | Slam(_,sopt,body) -> (Some s <> sopt) & occur_var_ast s body
  | Id _ | Str _ | Num _ | Path _ -> false
  | Dynamic _ -> (* Hum... what to do here *) false


(**********************************************************************)
(* Object substitution in modules *)

let rec subst_astpat subst = function
  | Pquote a -> Pquote (subst_ast subst a)
  | Pmeta _ as p -> p
  | Pnode (s,pl) -> Pnode (s,subst_astpatlist subst pl)
  | Pslam (ido,p) -> Pslam (ido,subst_astpat subst p)
  | Pmeta_slam (s,p) -> Pmeta_slam (s,subst_astpat subst p)

and subst_astpatlist subst = function
  | Pcons (p,pl) -> Pcons (subst_astpat subst p, subst_astpatlist subst pl)
  | (Plmeta _ | Pnil) as pl -> pl

let subst_pat subst = function
  | AstListPat pl -> AstListPat (subst_astpatlist subst pl)
  | PureAstPat p -> PureAstPat (subst_astpat subst p)
