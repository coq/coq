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
open Nametab
open Names
open Nameops
open Libnames
open Ppextend
open Topconstr
open Term
open Pattern
open Rawterm
open Constrextern
open Termops
(*i*)

let sep_p = fun _ -> str"."
let sep_v = fun _ -> str"," ++ spc()
let sep_pp = fun _ -> str":"
let sep_bar = fun _ -> spc() ++ str"| "
let pr_tight_coma () = str "," ++ cut ()

let latom = 0
let lannot = 100
let lprod = 200
let llambda = 200
let lif = 200
let lletin = 200
let lfix = 200
let larrow = 90
let lcast = 100
let larg = 9
let lapp = 10
let lposint = 0
let lnegint = 35 (* must be consistent with Notation "- x" *)
let ltop = (200,E)
let lproj = 1
let lsimple = (1,E)

let prec_less child (parent,assoc) =
  if parent < 0 && child = lprod then true
  else
    let parent = abs parent in
    match assoc with
      | E -> (<=) child parent
      | L -> (<) child parent
      | Prec n -> child<=n
      | Any -> true

let prec_of_prim_token = function
  | Numeral p -> if Bigint.is_pos_or_zero p then lposint else lnegint
  | String _ -> latom

let env_assoc_value v env =
  try List.nth env (v-1)
  with Not_found -> anomaly ("Inconsistent environment for pretty-print rule")

let decode_constrlist_value = function
  | CAppExpl (_,_,l) -> l
  | CApp (_,_,l) -> List.map fst l
  | _ -> anomaly "Ill-formed list argument of notation"

let decode_patlist_value = function
  | CPatCstr (_,_,l) -> l
  | _ -> anomaly "Ill-formed list argument of notation"

open Notation

let rec print_hunk n decode pr env = function
  | UnpMetaVar (e,prec) -> pr (n,prec) (env_assoc_value e env)
  | UnpListMetaVar (e,prec,sl) -> 
      prlist_with_sep (fun () -> prlist (print_hunk n decode pr env) sl)
      (pr (n,prec)) (decode (env_assoc_value e env))
  | UnpTerminal s -> str s
  | UnpBox (b,sub) -> ppcmd_of_box b (prlist (print_hunk n decode pr env) sub)
  | UnpCut cut -> ppcmd_of_cut cut

let pr_notation_gen decode pr s env =
  let unpl, level = find_notation_printing_rule s in
  prlist (print_hunk level decode pr env) unpl, level

let pr_notation = pr_notation_gen decode_constrlist_value
let pr_patnotation = pr_notation_gen decode_patlist_value

let pr_delimiters key strm =
  strm ++ str ("%"^key)

let pr_located pr (loc,x) =
  if Options.do_translate() && loc<>dummy_loc then
    let (b,e) = unloc loc in
    comment b ++ pr x ++ comment e
  else pr x

let pr_com_at n =
  if Options.do_translate() && n <> 0 then comment n 
  else mt()

let pr_with_comments loc pp = pr_located (fun x -> x) (loc,pp)

let pr_sep_com sep f c = pr_with_comments (constr_loc c) (sep() ++ f c)

let pr_optc pr = function
  | None -> mt ()
  | Some x -> pr_sep_com spc pr x

let pr_in_comment pr x = str "(* " ++ pr x ++ str " *)"

let pr_universe = Univ.pr_uni 

let pr_rawsort = function
  | RProp Term.Null -> str "Prop"
  | RProp Term.Pos -> str "Set"
  | RType u -> hov 0 (str "Type" ++ pr_opt (pr_in_comment pr_universe) u)

let pr_id = pr_id
let pr_name = pr_name
let pr_qualid = pr_qualid

let pr_expl_args pr (a,expl) =
  match expl with
  | None -> pr (lapp,L) a
  | Some (_,ExplByPos n) ->
      anomaly("Explicitation by position not implemented")
  | Some (_,ExplByName id) -> 
      str "(" ++ pr_id id ++ str ":=" ++ pr ltop a ++ str ")"

let pr_opt_type pr = function
  | CHole _ -> mt ()
  | t -> cut () ++ str ":" ++ pr t

let pr_opt_type_spc pr = function
  | CHole _ -> mt ()
  | t ->  str " :" ++ pr_sep_com (fun()->brk(1,2)) (pr ltop) t

let pr_lident (loc,id) =
  if loc <> dummy_loc then
    let (b,_) = unloc loc in
    pr_located pr_id (make_loc (b,b+String.length(string_of_id id)),id)
  else pr_id id

let pr_lname = function
    (loc,Name id) -> pr_lident (loc,id)
  | lna -> pr_located pr_name lna

let pr_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar (loc,s) -> pr_lident (loc,s)

let pr_prim_token = function
  | Numeral n -> Bigint.pr_bigint n
  | String s -> qs s

let las = lapp
let lpator = 100

let rec pr_patt sep inh p =
  let (strm,prec) = match p with
  | CPatAlias (_,p,id) ->
      pr_patt mt (las,E) p ++ str " as " ++ pr_id id, las
  | CPatCstr (_,c,[]) -> pr_reference c, latom
  | CPatCstr (_,c,args) ->
      pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp
  | CPatAtom (_,None) -> str "_", latom
  | CPatAtom (_,Some r) -> pr_reference r, latom
  | CPatOr (_,pl) ->
      hov 0 (prlist_with_sep pr_bar (pr_patt spc (lpator,L)) pl), lpator
  | CPatNotation (_,"( _ )",[p]) ->
      pr_patt (fun()->str"(") (max_int,E) p ++ str")", latom
  | CPatNotation (_,s,env) -> pr_patnotation (pr_patt mt) s env
  | CPatPrim (_,p) -> pr_prim_token p, latom
  | CPatDelimiters (_,k,p) -> pr_delimiters k (pr_patt mt lsimple p), 1
  in
  let loc = cases_pattern_expr_loc p in
  pr_with_comments loc
    (sep() ++ if prec_less prec inh then strm else surround strm)

let pr_patt = pr_patt mt

let pr_eqn pr (loc,pl,rhs) =
  spc() ++ hov 4
    (pr_with_comments loc
      (str "| " ++
      hov 0 (prlist_with_sep pr_bar (prlist_with_sep sep_v (pr_patt ltop)) pl 
             ++ str " =>") ++
      pr_sep_com spc (pr ltop) rhs))

let begin_of_binder = function
    LocalRawDef((loc,_),_) -> fst (unloc loc)
  | LocalRawAssum((loc,_)::_,_) -> fst (unloc loc)
  | _ -> assert false

let begin_of_binders = function
  | b::_ -> begin_of_binder b
  | _ -> 0

let pr_binder many pr (nal,t) =
  match t with
  | CHole _ -> prlist_with_sep spc pr_lname nal
  | _ ->
    let s = prlist_with_sep spc pr_lname nal ++ str" : " ++ pr t in
    hov 1 (if many then surround s else s)

let pr_binder_among_many pr_c = function
  | LocalRawAssum (nal,t) ->
      pr_binder true pr_c (nal,t)
  | LocalRawDef (na,c) ->
      let c,topt = match c with
        | CCast(_,c, CastConv (_,t)) -> c, t
        | _ -> c, CHole dummy_loc in
      hov 1 (surround
        (pr_lname na ++ pr_opt_type pr_c topt ++
         str":=" ++ cut() ++ pr_c c))

let pr_undelimited_binders pr_c =
  prlist_with_sep spc (pr_binder_among_many pr_c)

let pr_delimited_binders kw pr_c bl =
  let n = begin_of_binders bl in
  match bl with
  | [LocalRawAssum (nal,t)] ->
      pr_com_at n ++ kw() ++ pr_binder false pr_c (nal,t)
  | LocalRawAssum _ :: _ as bdl ->
      pr_com_at n ++ kw() ++ pr_undelimited_binders pr_c bdl
  | _ -> assert false

let pr_let_binder pr x a =
  hov 0 (hov 0 (pr_name x ++ brk(0,1) ++ str ":=") ++
         pr_sep_com (fun () -> brk(0,1)) (pr ltop) a)

let rec extract_prod_binders = function
(*  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_prod_binders c in
      if bl = [] then [], x else LocalRawDef (na,b) :: bl, c*)
  | CProdN (loc,[],c) ->
      extract_prod_binders c
  | CProdN (loc,(nal,t)::bl,c) ->
      let bl,c = extract_prod_binders (CProdN(loc,bl,c)) in
      LocalRawAssum (nal,t) :: bl, c
  | c -> [], c

let rec extract_lam_binders = function
(*  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_lam_binders c in
      if bl = [] then [], x else LocalRawDef (na,b) :: bl, c*)
  | CLambdaN (loc,[],c) ->
      extract_lam_binders c
  | CLambdaN (loc,(nal,t)::bl,c) ->
      let bl,c = extract_lam_binders (CLambdaN(loc,bl,c)) in
      LocalRawAssum (nal,t) :: bl, c
  | c -> [], c
    
let split_lambda = function
  | CLambdaN (loc,[[na],t],c) -> (na,t,c)
  | CLambdaN (loc,([na],t)::bl,c) -> (na,t,CLambdaN(loc,bl,c))
  | CLambdaN (loc,(na::nal,t)::bl,c) -> (na,t,CLambdaN(loc,(nal,t)::bl,c))
  | _ -> anomaly "ill-formed fixpoint body"

let rename na na' t c =
  match (na,na') with
    | (_,Name id), (_,Name id') -> (na',t,replace_vars_constr_expr [id,id'] c)
    | (_,Name id), (_,Anonymous) -> (na,t,c)
    | _ -> (na',t,c)
  
let split_product na' = function
  | CArrow (loc,t,c) -> (na',t,c)
  | CProdN (loc,[[na],t],c) -> rename na na' t c
  | CProdN (loc,([na],t)::bl,c) -> rename na na' t (CProdN(loc,bl,c))
  | CProdN (loc,(na::nal,t)::bl,c) ->
      rename na na' t (CProdN(loc,(nal,t)::bl,c))
  | _ -> anomaly "ill-formed fixpoint body"

let merge_binders (na1,ty1) cofun (na2,ty2) codom =
  let na =
    match snd na1, snd na2 with
        Anonymous, Name id ->
          if occur_var_constr_expr id cofun then
            failwith "avoid capture"
          else na2
      | Name id, Anonymous ->
          if occur_var_constr_expr id codom then
            failwith "avoid capture"
          else na1
      | Anonymous, Anonymous -> na1
      | Name id1, Name id2 ->
          if id1 <> id2 then failwith "not same name" else na1 in
  let ty =
    match ty1, ty2 with
        CHole _, _ -> ty2
      | _, CHole _ -> ty1
      | _ ->
          Constrextern.check_same_type ty1 ty2;
          ty2 in
  (LocalRawAssum ([na],ty), codom)
            
let rec strip_domain bvar cofun c =
  match c with
    | CArrow(loc,a,b) ->
        merge_binders bvar cofun ((dummy_loc,Anonymous),a) b
    | CProdN(loc,[([na],ty)],c') ->
        merge_binders bvar cofun (na,ty) c'
    | CProdN(loc,([na],ty)::bl,c') ->
        merge_binders bvar cofun (na,ty) (CProdN(loc,bl,c'))
    | CProdN(loc,(na::nal,ty)::bl,c') ->
        merge_binders bvar cofun (na,ty) (CProdN(loc,(nal,ty)::bl,c'))
    | _ -> failwith "not a product"

(* Note: binder sharing is lost *)
let rec strip_domains (nal,ty) cofun c =
  match nal with
      [] -> assert false
    | [na] ->
        let bnd, c' = strip_domain (na,ty) cofun c in
        ([bnd],None,c')
    | na::nal ->
        let f = CLambdaN(dummy_loc,[(nal,ty)],cofun) in
        let bnd, c1 = strip_domain (na,ty) f c in
        (try
          let bl, rest, c2 = strip_domains (nal,ty) cofun c1 in
          (bnd::bl, rest, c2)
        with Failure _ -> ([bnd],Some (nal,ty), c1))

(* Re-share binders *)
let rec factorize_binders = function
  | ([] | [_] as l) -> l
  | LocalRawAssum (nal,ty) as d :: (LocalRawAssum (nal',ty')::l as l') ->
      (try
	let _ = Constrextern.check_same_type ty ty' in
	factorize_binders (LocalRawAssum (nal@nal',ty)::l)
      with _ ->
	d :: factorize_binders l')
  | d :: l -> d :: factorize_binders l

(* Extract lambdas when a type constraint occurs *)
let rec extract_def_binders c ty =
  match c with
    | CLambdaN(loc,bvar::lams,b) ->
        (try
          let f = CLambdaN(loc,lams,b) in
          let bvar', rest, ty' = strip_domains bvar f ty in
          let c' =
            match rest, lams with
                None,[] -> b
              | None, _ -> f
              | Some bvar,_ -> CLambdaN(loc,bvar::lams,b) in
          let (bl,c2,ty2) = extract_def_binders c' ty' in
          (factorize_binders (bvar'@bl), c2, ty2)
        with Failure _ ->
          ([],c,ty))
    | _ -> ([],c,ty)

let rec split_fix n typ def =
  if n = 0 then ([],typ,def)
  else
    let (na,_,def) = split_lambda def in
    let (na,t,typ) = split_product na typ in
    let (bl,typ,def) = split_fix (n-1) typ def in
    (LocalRawAssum ([na],t)::bl,typ,def)

let pr_recursive_decl pr pr_dangling dangling_with_for id bl annot t c =
  let pr_body =
    if dangling_with_for then pr_dangling else pr in
  pr_id id ++ str" " ++
  hov 0 (pr_undelimited_binders (pr ltop) bl ++ annot) ++
  pr_opt_type_spc pr t ++ str " :=" ++
  pr_sep_com (fun () -> brk(1,2)) (pr_body ltop) c

let pr_fixdecl pr prd dangling_with_for (id,(n,ro),bl,t,c) =
  let annot =
    let ids = names_of_local_assums bl in
      match ro with
	  CStructRec ->
	    if List.length ids > 1 && n <> None then 
	      spc() ++ str "{struct " ++ pr_name (snd (List.nth ids (out_some n))) ++ str"}"
	    else mt() 
	| CWfRec c ->
	    spc () ++ str "{wf " ++ pr lsimple c ++ pr_name (snd (List.nth ids (out_some n))) ++ str"}"
	| CMeasureRec c ->
	    spc () ++ str "{measure " ++ pr lsimple c ++ pr_name (snd (List.nth ids (out_some n))) ++ str"}"
  in
    pr_recursive_decl pr prd dangling_with_for id bl annot t c

let pr_cofixdecl pr prd dangling_with_for (id,bl,t,c) =
  pr_recursive_decl pr prd dangling_with_for id bl (mt()) t c

let pr_recursive pr_decl id = function
  | [] -> anomaly "(co)fixpoint with no definition"
  | [d1] -> pr_decl false d1
  | dl ->
      prlist_with_sep (fun () -> fnl() ++ str "with ")
        (pr_decl true) dl ++
      fnl() ++ str "for " ++ pr_id id

let is_var id = function
  | CRef (Ident (_,id')) when id=id' -> true
  | _ -> false

let tm_clash = function
  | (CRef (Ident (_,id)), Some (CApp (_,_,nal))) 
      when List.exists (function CRef (Ident (_,id')),_ -> id=id' | _ -> false)
	nal
      -> Some id
  | (CRef (Ident (_,id)), Some (CAppExpl (_,_,nal))) 
      when List.exists (function CRef (Ident (_,id')) -> id=id' | _ -> false)
	nal
      -> Some id
  | _ -> None

let pr_case_item pr (tm,(na,indnalopt)) =
  hov 0 (pr (lcast,E) tm ++
(*
  (match na with
    | Name id when not (is_var id tm) -> spc () ++ str "as " ++  pr_id id
    | Anonymous when tm_clash (tm,indnalopt) <> None ->
	(* hide [tm] name to avoid conflicts *)
	spc () ++ str "as _" (* ++ pr_id (out_some (tm_clash (tm,indnalopt)))*)
    | _ -> mt ()) ++
*)
  (match na with (* Decision of printing "_" or not moved to constrextern.ml *)
    | Some na -> spc () ++ str "as " ++  pr_name na
    | None -> mt ()) ++
  (match indnalopt with
    | None -> mt ()
(*
    | Some (_,ind,nal) ->
        spc () ++ str "in " ++ 
        hov 0 (pr_reference ind ++ prlist (pr_arg pr_name) nal))
*)
    | Some t -> spc () ++ str "in " ++ pr lsimple t))

let pr_case_type pr po =
  match po with
    | None | Some (CHole _) -> mt()
    | Some p ->
        spc() ++ hov 2 (str "return" ++ pr_sep_com spc (pr lsimple) p)

let pr_return_type pr po = pr_case_type pr po

let pr_simple_return_type pr na po =
  (match na with
    | Some (Name id) ->
        spc () ++ str "as " ++  pr_id id
    | _ -> mt ()) ++
  pr_case_type pr po

let pr_proj pr pr_app a f l =
  hov 0 (pr lsimple a ++ cut() ++ str ".(" ++ pr_app pr f l ++ str ")")

let pr_appexpl pr f l =
      hov 2 (
	str "@" ++ pr_reference f ++
	prlist (pr_sep_com spc (pr (lapp,L))) l)

let pr_app pr a l =
  hov 2 (
    pr (lapp,L) a  ++ 
    prlist (fun a -> spc () ++ pr_expl_args pr a) l)

let rec pr sep inherited a =
  let (strm,prec) = match a with
  | CRef r -> pr_reference r, latom
  | CFix (_,id,fix) ->
      hov 0 (str"fix " ++
             pr_recursive
               (pr_fixdecl (pr mt) (pr_dangling_with_for mt)) (snd id) fix),
      lfix
  | CCoFix (_,id,cofix) ->
      hov 0 (str "cofix " ++
             pr_recursive
              (pr_cofixdecl (pr mt) (pr_dangling_with_for mt)) (snd id) cofix),
      lfix
  | CArrow (_,a,b) ->
      hov 0 (pr mt (larrow,L) a ++ str " ->" ++
             pr (fun () ->brk(1,0)) (-larrow,E) b),
      larrow
  | CProdN _ ->
      let (bl,a) = extract_prod_binders a in
      hov 0 (
	hov 2 (pr_delimited_binders (fun () -> str"forall" ++ spc())
                 (pr mt ltop) bl) ++
        str "," ++ pr spc ltop a),
      lprod
  | CLambdaN _ ->
      let (bl,a) = extract_lam_binders a in
      hov 0 (
        hov 2 (pr_delimited_binders (fun () -> str"fun" ++ spc())
                 (pr mt ltop) bl) ++

        str " =>" ++ pr spc ltop a),
      llambda
  | CLetIn (_,(_,Name x),(CFix(_,(_,x'),[_])|CCoFix(_,(_,x'),[_]) as fx), b)
      when x=x' ->
      hv 0 (
        hov 2 (str "let " ++ pr mt ltop fx ++ str " in") ++
        pr spc ltop b),
      lletin
  | CLetIn (_,x,a,b) ->
      hv 0 (
        hov 2 (str "let " ++ pr_lname x ++ str " :=" ++
               pr spc ltop a ++ str " in") ++
        pr spc ltop b),
      lletin
  | CAppExpl (_,(Some i,f),l) ->
      let l1,l2 = list_chop i l in
      let c,l1 = list_sep_last l1 in
      let p = pr_proj (pr mt) pr_appexpl c f l1 in
      if l2<>[] then
	p ++ prlist (pr spc (lapp,L)) l2, lapp
      else
	p, lproj
  | CAppExpl (_,(None,Ident (_,var)),[t])
  | CApp (_,(_,CRef(Ident(_,var))),[t,None])
        when var = Topconstr.ldots_var ->
      hov 0 (str ".." ++ pr spc (latom,E) t ++ spc () ++ str ".."), larg
  | CAppExpl (_,(None,f),l) -> pr_appexpl (pr mt) f l, lapp
  | CApp (_,(Some i,f),l) ->
      let l1,l2 = list_chop i l in
      let c,l1 = list_sep_last l1 in
      assert (snd c = None);
      let p = pr_proj (pr mt) pr_app (fst c) f l1 in
      if l2<>[] then 
	p ++ prlist (fun a -> spc () ++ pr_expl_args (pr mt) a) l2, lapp
      else
	p, lproj
  | CApp (_,(None,a),l) -> pr_app (pr mt) a l, lapp
  | CCases (_,rtntypopt,c,eqns) ->
      v 0
        (hv 0 (str "match" ++ brk (1,2) ++
	  hov 0 (
	    prlist_with_sep sep_v
              (pr_case_item (pr_dangling_with_for mt)) c
            ++ pr_case_type (pr_dangling_with_for mt) rtntypopt) ++
	spc () ++ str "with") ++
        prlist (pr_eqn (pr mt)) eqns ++ spc() ++ str "end"),
      latom
  | CLetTuple (_,nal,(na,po),c,b) ->
      hv 0 (
        str "let " ++
	hov 0 (str "(" ++
               prlist_with_sep sep_v pr_name nal ++
               str ")" ++
	       pr_simple_return_type (pr mt) na po ++ str " :=" ++
               pr spc ltop c ++ str " in") ++
        pr spc ltop b),
      lletin
  | CIf (_,c,(na,po),b1,b2) ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
	 parsing est lui plus tolérant) *)
      hv 0 (
	hov 1 (str "if " ++ pr mt ltop c ++ pr_simple_return_type (pr mt) na po) ++
	spc () ++
	hov 0 (str "then" ++ pr (fun () -> brk (1,1)) ltop b1) ++ spc () ++
	hov 0 (str "else" ++ pr (fun () -> brk (1,1)) ltop b2)),
      lif
     
  | CHole _ -> str "_", latom
  | CEvar (_,n) -> str (Evd.string_of_existential n), latom
  | CPatVar (_,(_,p)) -> str "?" ++ pr_patvar p, latom
  | CSort (_,s) -> pr_rawsort s, latom
  | CCast (_,a,CastConv (k,b)) ->
      let s = match k with VMcast -> "<:" | DEFAULTcast -> ":" in
      hv 0 (pr mt (lcast,L) a ++ cut () ++ str s ++ pr mt (-lcast,E) b),
      lcast
  | CCast (_,a,CastCoerce) ->
      hv 0 (pr mt (lcast,L) a ++ cut () ++ str ":>"),
      lcast
  | CNotation (_,"( _ )",[t]) ->
      pr (fun()->str"(") (max_int,L) t ++ str")", latom
  | CNotation (_,s,env) -> pr_notation (pr mt) s env
  | CPrim (_,p) -> pr_prim_token p, prec_of_prim_token p
  | CDelimiters (_,sc,a) -> pr_delimiters sc (pr mt lsimple a), 1
  | CDynamic _ -> str "<dynamic>", latom
  in
  let loc = constr_loc a in
  pr_with_comments loc
    (sep() ++ if prec_less prec inherited then strm else surround strm)

and pr_dangling_with_for sep inherited a =
  match a with
  | (CFix (_,_,[_])|CCoFix(_,_,[_])) -> pr sep (latom,E) a
  | _ -> pr sep inherited a

let pr = pr mt

let rec strip_context n iscast t =
  if n = 0 then
    [], if iscast then match t with CCast (_,c,_) -> c | _ -> t else t
  else match t with
    | CLambdaN (loc,(nal,t)::bll,c) ->
	let n' = List.length nal in
	if n' > n then
	  let nal1,nal2 = list_chop n nal in
	  [LocalRawAssum (nal1,t)], CLambdaN (loc,(nal2,t)::bll,c)
	else
	let bl', c = strip_context (n-n') iscast
	  (if bll=[] then c else CLambdaN (loc,bll,c)) in
	LocalRawAssum (nal,t) :: bl', c 
    | CProdN (loc,(nal,t)::bll,c) ->
	let n' = List.length nal in
	if n' > n then
	  let nal1,nal2 = list_chop n nal in
	  [LocalRawAssum (nal1,t)], CProdN (loc,(nal2,t)::bll,c)
	else
	let bl', c = strip_context (n-n') iscast
	  (if bll=[] then c else CProdN (loc,bll,c)) in
	LocalRawAssum (nal,t) :: bl', c 
    | CArrow (loc,t,c) ->
	let bl', c = strip_context (n-1) iscast c in
	LocalRawAssum ([loc,Anonymous],t) :: bl', c 
    | CCast (_,c,_) -> strip_context n false c
    | CLetIn (_,na,b,c) -> 
	let bl', c = strip_context (n-1) iscast c in
	LocalRawDef (na,b) :: bl', c
    | _ -> anomaly "strip_context"

let pr_constr_expr c = pr lsimple c
let pr_lconstr_expr c = pr ltop c
let pr_pattern_expr c = pr lsimple c
let pr_lpattern_expr c = pr ltop c

let pr_cases_pattern_expr = pr_patt ltop

let pr_binders = pr_undelimited_binders (pr ltop)

let pr_with_occurrences pr = function
    ([],c) -> pr c
  | (nl,c) -> hov 1 (pr c ++ spc() ++ str"at " ++
                     hov 0 (prlist_with_sep spc (pr_or_var int) nl))

let pr_red_flag pr r =
  (if r.rBeta then pr_arg str "beta" else mt ()) ++
  (if r.rIota then pr_arg str "iota" else mt ()) ++
  (if r.rZeta then pr_arg str "zeta" else mt ()) ++
  (if r.rConst = [] then
     if r.rDelta then pr_arg str "delta"
     else mt ()
   else
     pr_arg str "delta " ++ (if r.rDelta then str "-" else mt ()) ++
     hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]"))

open Genarg

let pr_metaid id = str"?" ++ pr_id id

let pr_red_expr (pr_constr,pr_lconstr,pr_ref) = function
  | Red false -> str "red"
  | Hnf -> str "hnf"
  | Simpl o -> str "simpl" ++ pr_opt (pr_with_occurrences pr_constr) o  
  | Cbv f ->
      if f = {rBeta=true;rIota=true;rZeta=true;rDelta=true;rConst=[]} then
	str "compute"
      else
	hov 1 (str "cbv" ++ pr_red_flag pr_ref f)
  | Lazy f -> 
      hov 1 (str "lazy" ++ pr_red_flag pr_ref f)
  | Unfold l ->
      hov 1 (str "unfold" ++ spc() ++
             prlist_with_sep pr_coma (pr_with_occurrences pr_ref) l)
  | Fold l -> hov 1 (str "fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l ->
      hov 1 (str "pattern" ++
        pr_arg (prlist_with_sep pr_coma (pr_with_occurrences pr_constr)) l)
        
  | Red true -> error "Shouldn't be accessible from user"
  | ExtraRedExpr s -> str s
  | CbvVm -> str "vm_compute"

let rec pr_may_eval test prc prlc pr2 = function
  | ConstrEval (r,c) ->
      hov 0
        (str "eval" ++ brk (1,1) ++
         pr_red_expr (prc,prlc,pr2) r ++
	 str " in" ++ spc() ++ prc c)
  | ConstrContext ((_,id),c) ->
      hov 0
	(str "context " ++ pr_id id ++ spc () ++
	 str "[" ++ prlc c ++ str "]")
  | ConstrTypeOf c -> hov 1 (str "type of" ++ spc() ++ prc c)
  | ConstrTerm c when test c -> h 0 (str "(" ++ prc c ++ str ")")
  | ConstrTerm c -> prc c

let pr_may_eval a = pr_may_eval (fun _ -> false) a
