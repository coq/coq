
(* $Id$ *)

open Pp
open Util
open Names
open Coqast
open Pcoq

let isMeta s = String.length s <> 0 & s.[0]='$'

let dummy_loc = (0,0)

let loc = function
  | Node (loc,_,_) -> loc
  | Nvar (loc,_) -> loc
  | Slam (loc,_,_) -> loc
  | Num (loc,_) -> loc
  | Id (loc,_) -> loc
  | Str (loc,_) -> loc
  | Path (loc,_,_) -> loc
  | Dynamic (loc,_) -> loc

(* building a node with dummy location *)

let ope(op,l) = Node(dummy_loc,op,l)
let slam(idl,b) = Slam(dummy_loc,idl,b)
let ide s = Id(dummy_loc,s)
let nvar s = Nvar(dummy_loc,s)
let num n = Num(dummy_loc,n)
let str s = Str(dummy_loc,s)
let path sl s = Path(dummy_loc,sl,s)
let dynamic d = Dynamic(dummy_loc,d)

let rec set_loc loc = function
  | Node(_,op,al) -> Node(loc, op, List.map (set_loc loc) al)
  | Slam(_,idl,b) -> Slam(loc,idl, set_loc loc b)
  | Nvar(_,s) -> Nvar(loc,s)
  | Id(_,s) -> Id(loc,s)
  | Str(_,s) -> Str(loc,s)
  | Num(_,s) -> Num(loc,s)
  | Path(_,sl,s) -> Path(loc,sl,s)
  | Dynamic(_,d) -> Dynamic(loc,d)

let path_section loc sp =
  let (sl,bn,pk) = repr_path sp in
  Coqast.Path(loc,List.rev(string_of_id bn :: sl), string_of_kind pk)

let section_path sl k =
  match List.rev sl with
    | s::pa -> 
	make_path pa (id_of_string s) (kind_of_string k)
    | [] -> invalid_arg "section_path"

(* ast destructors *)
let num_of_ast = function
  | Num(_,n) -> n
  | ast -> invalid_arg_loc (loc ast, "Ast.num_of_ast")

let nvar_of_ast = function
  | Nvar(_,s) -> s
  | ast -> invalid_arg_loc (loc ast, "Ast.nvar_of_ast")

let id_of_ast =  function
  | Id(_,s) -> s
  | ast -> invalid_arg_loc (loc ast, "Ast.nvar_of_ast")

(* patterns of ast *)
type pat =
  | Pquote of t
  | Pmeta of string * tok_kind
  | Pnode of string * patlist
  | Pslam of string option * pat
  | Pmeta_slam of string * pat

and patlist =
  | Pcons of pat * patlist
  | Plmeta of string
  | Pnil

and tok_kind = Tnum | Tid | Tstr | Tpath | Tvar | Tany | Tlist

(* semantic actions of grammar rules *)
type act =
  | Aast of pat
  | Aastlist of patlist
  | Acase of act * (pat * act) list
  | Acaselist of act * (patlist * act) list

(* values associated to variables *)
type v =
  | Vast of t
  | Vastlist of t list

type env = (string * v) list

(* Pretty-printing *)
let rec print_ast ast =
  match ast with
    | Num(_,n) -> [< 'iNT n >]
    | Str(_,s) -> [< 'qS s >]
    | Path(_,sl,u) -> 
	[< prlist (fun s -> [< 'sTR"#"; 'sTR s >]) sl; 'sTR"."; 'sTR u >]
    | Id (_,s) -> [< 'sTR"{" ; 'sTR s ; 'sTR"}" >]
    | Nvar(_,s) -> [< 'sTR s >]
    | Node(_,op,l) ->
        hOV 3 [< 'sTR"(" ; 'sTR op ; 'sPC ; print_astl l; 'sTR")" >]
    | Slam(_,None,ast) -> hOV 1 [< 'sTR"[<>]"; print_ast ast >]
    | Slam(_,Some x,ast) ->
        hOV 1 [< 'sTR"["; 'sTR x; 'sTR"]"; 'cUT; print_ast ast >]
    | Dynamic(_,d) ->
	hOV 0 [< 'sTR"<dynamic: "; 'sTR(Dyn.tag d); 'sTR">" >]

and print_astl astl =
  prlist_with_sep pr_spc print_ast astl

let print_ast_cast = function
  | Tany -> [< >]
  | Tvar -> [< 'sTR":var" >]
  | Tid -> [< 'sTR":id" >]
  | Tstr -> [< 'sTR":str" >]
  | Tpath -> [< 'sTR":path" >]
  | Tnum -> [< 'sTR":num" >]
  | Tlist -> [< 'sTR":list" >]

let rec print_astpat = function
  | Pquote ast -> [< 'sTR"'"; print_ast ast >]
  | Pmeta(s,tk) -> [< 'sTR s; print_ast_cast tk >]
  | Pmeta_slam(s,b) ->
      hOV 1 [< 'sTR"["; 'sTR s; 'sTR"]"; 'cUT; print_astpat b >]
  | Pnode(op,al) ->
      hOV 2 [< 'sTR"(" ; 'sTR op; 'sPC; print_astlpat al; 'sTR")" >]
  | Pslam(None,b) -> hOV 1 [< 'sTR"[<>]"; 'cUT; print_astpat b >]
  | Pslam(Some s,b) ->
      hOV 1 [< 'sTR"["; 'sTR s; 'sTR"]"; 'cUT; print_astpat b >]

and print_astlpat = function
  | Pnil -> [< >]
  | Pcons(h,Pnil) -> hOV 1 [< print_astpat h >]
  | Pcons(h,t) -> hOV 1 [< print_astpat h; 'sPC; print_astlpat t >]
  | Plmeta(s) -> [< 'sTR"| "; 'sTR s >]


let print_val = function
  | Vast a -> print_ast a
  | Vastlist al -> 
      hOV 1 [< 'sTR"["; prlist_with_sep pr_spc print_ast al; 'sTR"]" >]


(* Ast values environments *)

let grammar_type_error (loc,s) =
  anomaly_loc (loc,s,[< 'sTR"grammar type error: "; 'sTR s >])


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
                         [< 'sTR"cast _"; print_ast_cast k; 'sTR"failed" >])

let rec coerce_to_var v = function
  | Nvar(_,id) -> id 
  | ast -> user_err_loc
        (loc ast,"Ast.coerce_to_var",
         [< 'sTR"the variable "; 'sTR v;
            'sTR" was bound to"; 'bRK(1,1); print_ast ast; 'sPC;
            'sTR"instead of a (list of) variable(s)." >])

let env_assoc_value loc v env =
  try 
    List.assoc v env
  with Not_found -> 
    anomaly_loc
      (loc,"Ast.env_assoc_value",
       [< 'sTR"metavariable "; 'sTR v; 'sTR" is unbound." >])

let env_assoc_list sigma (loc,v) =
  match env_assoc_value loc v sigma with
    | Vastlist al -> al
    | Vast a -> [a]

let env_assoc sigma k (loc,v) =
  match env_assoc_value loc v sigma with
    | Vast a -> check_cast loc a k; a
    | _ -> grammar_type_error (loc,"Ast.env_assoc: "^v^" is an ast list")

let env_assoc_nvars sigma (dloc,v) =
  match env_assoc_value dloc v sigma with
    | Vastlist al -> List.map (coerce_to_var v) al
    | Vast ast -> [coerce_to_var v ast]

let build_lams dloc idl ast =
  List.fold_right (fun id lam -> Slam(dloc,Some id,lam)) idl ast


(* Substitution *)

(* Locations in quoted ast are wrong (they refer to the right hand
   side of a grammar rule). A default location dloc is used whenever
   we create an ast constructor. Locations in the binding list are trusted. *)

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

type entry_env = (string * entry_type) list

let type_of_meta env loc pv =
  try 
    List.assoc pv env
  with Not_found ->
    user_err_loc (loc,"Ast.type_of_meta",
                  [< 'sTR"variable "; 'sTR pv; 'sTR" is unbound" >])

let check_ast_meta env loc pv =
  if (type_of_meta env loc pv) <> ETast then
    user_err_loc (loc,"Ast.check_ast_meta",
                  [< 'sTR"variable "; 'sTR pv; 'sTR" is a List" >])

let rec val_of_ast env ast =
  match ast with
    | Nvar(loc,pv) when isMeta pv ->
        check_ast_meta env loc pv;
        Pmeta(pv,Tany)
    | Id(loc,pv) when isMeta pv ->
        check_ast_meta env loc pv;
        Pmeta(pv,Tid)
    | Node(_,"$QUOTE",[qast]) -> Pquote (set_loc dummy_loc qast)
    | Slam(loc,Some s,a) when isMeta s ->
        let _ = type_of_meta env loc s in (* ids are coerced to id lists *)
        Pmeta_slam(s, val_of_ast env a)
    | (Path _|Num _|Id _|Str _|Nvar _) -> Pquote (set_loc dummy_loc ast)
    | Slam(_,os,b) -> Pslam(os, val_of_ast env b)
    | Node(loc,op,_) when isMeta op ->
        user_err_loc(loc,"Ast.val_of_ast",
                     [< 'sTR"no metavariable in operator position." >])
    | Node(_,op,args) -> Pnode(op, vall_of_astl env args)
    | Dynamic(loc,_) ->
	invalid_arg_loc(loc,"val_of_ast: dynamic")
	  
and vall_of_astl env astl =
  match astl with 
    | (Node(loc,"$LIST",[Nvar(locv,pv)]))::asttl when isMeta pv ->
        if type_of_meta env locv pv = ETastl then
          if asttl = [] then 
	    Plmeta pv
          else 
	    Pcons(Pmeta(pv,Tlist), vall_of_astl env asttl)
        else 
	  user_err_loc (loc,"Ast.vall_of_astl",
                        [< 'sTR"variable "; 'sTR pv;
                           'sTR" is not a List" >])
    | ast::asttl -> 
	Pcons (val_of_ast env ast, vall_of_astl env asttl)
    | [] -> Pnil


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
    | (Path(_,sl1,s1),Path(_,sl2,s2)) -> sl1=sl2 & s1=s2
    | _ -> false

let alpha_eq (a1,a2)= alpha [] a1 a2

let alpha_eq_val = function
  | (Vast a1, Vast a2) -> alpha_eq (a1,a2)
  | (Vastlist al1, Vastlist al2) ->
      (List.length al1 = List.length al2)
      & List.for_all2 (fun x y -> alpha_eq (x,y)) al1 al2
  | _ ->  false

let rec occur_var_ast s = function
  | Node(loc,op,args) -> List.exists (occur_var_ast s) args
  | Nvar(_,s2) -> s = s2
  | Slam(_,sopt,body) -> (Some s <> sopt) & occur_var_ast s body
  | Id _ | Str _ | Num _ | Path _ -> false
  | Dynamic _ -> (* Hum... what to do here *) false

exception No_match of string

let no_match_loc (loc,s) = Stdpp.raise_with_loc loc (No_match s)

(* Binds value v to variable var. If var is already bound, checks if the
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
    bind_env sigma var (Vast ast)
  with e -> 
    Stdpp.raise_with_loc (loc ast) e

let alpha_define sigma loc ps s =
  try 
    let _ = List.assoc ps sigma in sigma
  with Not_found ->
    if ps = "$_" then sigma else (ps, Vast(Nvar(loc,s)))::sigma


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
    | (Plmeta pv, _) -> bind_env sigma pv (Vastlist astl)
    | _ -> raise (No_match "Ast.amatchl")

let ast_match = amatch []
let astl_match = amatchl []

let first_match pat_of_fun env ast sl =
  let rec aux = function
    | [] -> None
    | (h::t) ->
        (try Some (h, ast_match env (pat_of_fun h) ast)
         with (No_match _| Stdpp.Exc_located (_,No_match _)) -> aux t)
  in 
  aux sl

let first_matchl patl_of_fun env astl sl =
  let rec aux = function
    | [] -> None
    | (h::t) ->
        (try Some (h, astl_match env (patl_of_fun h) astl)
         with (No_match _| Stdpp.Exc_located (_,No_match _)) -> aux t)
  in 
  aux sl
    
let bind_patvar env loc v etyp =
  try
    if List.assoc v env = etyp then 
      env
    else 
      user_err_loc
	(loc,"Ast.bind_patvar",
	 [< 'sTR"variable "; 'sTR v;
            'sTR" is bound several times with different types" >])
  with Not_found -> 
    if v="$_" then env else (v,etyp)::env
      
let make_astvar env loc v cast =
  let env' = bind_patvar env loc v ETast in
  (Pmeta(v,cast), env')

(* Note: no metavar in operator position. necessary ? *)
(* TODO: $SLAM pour recuperer tous les Slam d'un coup dans une liste *)
let rec pat_of_ast env ast =
  match ast with
    | Nvar(loc,pv) when isMeta pv -> make_astvar env loc pv Tany
    | Id(loc,pv) when isMeta pv -> make_astvar env loc pv Tid
    | Slam(loc,Some s,a) when isMeta s ->
        let senv = bind_patvar env loc s ETast in
        let (pa,env') = pat_of_ast senv a in
        (Pmeta_slam(s, pa), env')
    | Node(_,"$VAR",[Nvar(loc,pv)]) when isMeta pv ->
        make_astvar env loc pv Tvar
    | Node(_,"$ID",[Nvar(loc,pv)]) when isMeta pv ->
        make_astvar env loc pv Tid
    | Node(_,"$NUM",[Nvar(loc,pv)]) when isMeta pv ->
        make_astvar env loc pv Tnum
    | Node(_,"$STR",[Nvar(loc,pv)]) when isMeta pv ->
        make_astvar env loc pv Tstr
    | Node(_,"$PATH",[Nvar(loc,pv)]) when isMeta pv ->
        make_astvar env loc pv Tpath
    | Node(_,"$QUOTE",[qast]) -> (Pquote (set_loc dummy_loc qast), env)
    | Slam(_,os,b) ->
        let (pb,env') = pat_of_ast env b in
        (Pslam(os,pb), env')
    | Node(loc,op,_) when isMeta op ->
        user_err_loc(loc,"Ast.pat_of_ast",
                     [< 'sTR"no metavariable in operator position." >])
    | Node(_,op,args) ->
        let (pargs, env') = patl_of_astl env args in
        (Pnode(op,pargs), env')
    | (Path _|Num _|Id _|Str _|Nvar _) -> (Pquote (set_loc dummy_loc ast), env)
    | Dynamic(loc,_) ->
        invalid_arg_loc(loc,"pat_of_ast: dynamic")
	  
and patl_of_astl env astl =
  match astl with
    | [Node(_,"$LIST",[Nvar(loc,pv)])] when isMeta pv ->
        let penv = bind_patvar env loc pv ETastl in
        (Plmeta pv, penv)
    | [] -> (Pnil,env)
    | ast::asttl ->
        let (p1,env1) = pat_of_ast env ast in
        let (ptl,env2) = patl_of_astl env1 asttl in
        (Pcons (p1,ptl), env2)
	
let to_pat env ast =
  match ast with
    | Node(_,"ASTPAT",[p]) -> pat_of_ast env p
    | _ -> invalid_arg_loc (loc ast,"Ast.to_pat")


(* Ast with cases and metavariables *)

let print_sig = function
  | [] -> [< >]
  | sigma ->
      [< 'sTR"with constraints :"; 'bRK(1,1);
         v 0 (prlist_with_sep pr_spc
                (fun (x,v) -> [< 'sTR x; 'sTR" = "; hOV 0 (print_val v) >])
                sigma) >]

let case_failed loc sigma e pats =
  user_err_loc
    (loc,"Ast.eval_act",
     [< 'sTR"Grammar case failure. The ast"; 'sPC; print_ast e;
        'sPC; 'sTR"does not match any of the patterns :";
        'bRK(1,1); v 0 (prlist_with_sep pr_spc print_astpat pats); 'fNL;
        print_sig sigma >])

let caselist_failed loc sigma el pats =
  user_err_loc
    (loc,"Ast.eval_act",
     [< 'sTR"Grammar case failure. The ast list"; 'bRK(1,1); print_astl el;
        'sPC; 'sTR"does not match any of the patterns :";
        'bRK(1,1); v 0 (prlist_with_sep pr_spc print_astlpat pats); 'fNL;
        print_sig sigma >])

let rec eval_act dloc sigma act =
  match act with
    | Aast pat -> Vast (pat_sub dloc sigma pat)
    | Aastlist patl -> Vastlist (patl_sub dloc sigma patl)
    | Acase(e,ml) ->
        (match eval_act dloc sigma e with
           | Vast esub ->
               (match first_match fst sigma esub ml with
                  | Some((_,a),sigma_pat) -> eval_act dloc sigma_pat a
                  | _ -> case_failed dloc sigma esub (List.map fst ml))
           | _ -> grammar_type_error (dloc,"Ast.eval_act"))
    | Acaselist(e,ml) ->
        (match eval_act dloc sigma e with
           | Vastlist elsub ->
               (match first_matchl fst sigma elsub ml with
                  | Some((_,a),sigma_pat) -> eval_act dloc sigma_pat a
                  | _ -> caselist_failed dloc sigma elsub (List.map fst ml))
           | _ -> grammar_type_error (dloc,"Ast.eval_act"))

(* TODO: case sur des variables uniquement -> pas de pb de conflit Ast/List *)
let rec act_of_ast vars etyp ast =
  match ast with
    | Node(_,"$CASE",(a::et::cl)) ->
        let atyp = entry_type et in
        let pa = act_of_ast vars atyp a in
        (match atyp with
           | ETast ->
               let acl = List.map (case vars etyp) cl in
               Acase (pa,acl)
           | ETastl ->
               let acl = List.map (caselist vars etyp) cl in
               Acaselist (pa,acl))
    | Node(_,"ASTLIST",al) ->
        (match (etyp,al) with
           | (ETast,[a]) -> Aast (val_of_ast vars a)
           | (ETastl,_) -> Aastlist (vall_of_astl vars al)
           | (ETast,_) -> user_err_loc
                 (loc ast,"Ast.act_of_ast",
                  [< 'sTR
                       "entry type is Ast, but the right hand side is a list"
                  >]))
    | _ -> invalid_arg_loc (loc ast,"Ast.act_of_ast: ill-formed")

and case vars etyp ast =
  match ast with
    | Node(_,"CASE",[Node(loca,"ASTLIST",pl);a]) ->
        (match pl with
           | [p] ->
               let (apl,penv) = pat_of_ast vars p in
               let aa = act_of_ast penv etyp a in
               (apl,aa)
           | _ -> user_err_loc
                 (loca,"Ast.case",
                  [< 'sTR"case pattern for an ast should be a single ast" >]))
    | _ -> invalid_arg_loc (loc ast,"Ast.case")
	  
and caselist vars etyp ast =
  match ast with
    | Node(_,"CASE",[Node(_,"ASTLIST",pl);a]) ->
        let (apl,penv) = patl_of_astl vars pl in
        let aa = act_of_ast penv etyp a in
        (apl,aa)
    | _ -> invalid_arg_loc (loc ast,"Ast.caselist")

let to_act_check_vars env etyp ast =
  match ast with
    | Node(_,"ASTACT",[a]) -> act_of_ast env etyp a
    | _ -> invalid_arg_loc (loc ast,"Ast.to_act_env")


(* Hash-consing *)
module Hloc = Hashcons.Make(
  struct
    type t = Coqast.loc
    type u = unit
    let equal (b1,e1) (b2,e2) = b1=b2 & e1=e2
    let hash_sub () x = x
    let hash = Hashtbl.hash
  end)

module Hast = Hashcons.Make(
  struct
    type t = Coqast.t
    type u = (Coqast.t -> Coqast.t) * ((loc -> loc) * (string -> string))
    let hash_sub (hast,(hloc,hstr)) = function
      | Node(l,s,al) -> Node(hloc l, hstr s, List.map hast al)
      | Nvar(l,s) -> Nvar(hloc l, hstr s)
      | Slam(l,None,t) -> Slam(hloc l, None, hast t)
      | Slam(l,Some s,t) -> Slam(hloc l, Some (hstr s), hast t)
      | Num(l,n) -> Num(hloc l, n)
      | Id(l,s) -> Id(hloc l, hstr s)
      | Str(l,s) -> Str(hloc l, hstr s)
      | Path(l,d,k) -> Path(hloc l, List.map hstr d, hstr k)
      | Dynamic(l,d) -> Dynamic(hloc l, d)
    let equal a1 a2 =
      match (a1,a2) with
        | (Node(l1,s1,al1), Node(l2,s2,al2)) ->
            (l1==l2 & s1==s2 & List.length al1 = List.length al2)
            & List.for_all2 (==) al1 al2
        | (Nvar(l1,s1), Nvar(l2,s2)) -> l1==l2 & s1==s2
        | (Slam(l1,None,t1), Slam(l2,None,t2)) -> l1==l2 & t1==t2
        | (Slam(l1,Some s1,t1), Slam(l2,Some s2,t2)) -> l1==l2 & t1==t2
        | (Num(l1,n1), Num(l2,n2)) -> l1==l2 & n1=n2
        | (Id(l1,s1), Id(l2,s2)) -> l1==l2 & s1==s2
        | (Str(l1,s1),Str(l2,s2)) -> l1==l2 & s1==s2
        | (Path(l1,d1,k1), Path(l2,d2,k2)) ->
            (l1==l2 & k1==k2 & List.length d1 = List.length d2)
            & List.for_all2 (==) d1 d2
        | _ -> false
    let hash = Hashtbl.hash
  end)

let hcons_ast hstr =
  let hloc = Hashcons.simple_hcons Hloc.f () in
  let hast = Hashcons.recursive_hcons Hast.f (hloc,hstr) in
  (hast,hloc)
