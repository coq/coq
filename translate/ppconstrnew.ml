(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)      

(*i*)
open Ast
open Util
open Pp
open Nametab
open Names
open Nameops
open Libnames
open Coqast
open Ppextend
open Topconstr
open Term
open Pattern
(*i*)

let pr_id id = Nameops.pr_id (Constrextern.v7_to_v8_id id)

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

open Symbols

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

let surround p = hov 1 (str"(" ++ p ++ str")")

let pr_located pr ((b,e),x) =
  if Options.do_translate() && (b,e)<>dummy_loc then
    let (b,e) = unloc (b,e) in
    comment b ++ pr x ++ comment e
  else pr x

let pr_com_at n =
  if Options.do_translate() && n <> 0 then comment n 
  else mt()

let pr_with_comments loc pp = pr_located (fun x -> x) (loc,pp)

let pr_sep_com sep f c = pr_with_comments (constr_loc c) (sep() ++ f c)

open Rawterm

let pr_opt pr = function
  | None -> mt ()
  | Some x -> spc() ++ pr x

let pr_optc pr = function
  | None -> mt ()
  | Some x -> pr_sep_com spc pr x

let pr_universe u = str "<univ>"

let pr_sort = function
  | RProp Term.Null -> str "Prop"
  | RProp Term.Pos -> str "Set"
  | RType u -> str "Type" ++ pr_opt pr_universe u

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

let pr_name = function
  | Anonymous -> str"_"
  | Name id -> pr_id id

let pr_lident (b,_ as loc,id) =
  if loc <> dummy_loc then
    let (b,_) = unloc loc in
    pr_located pr_id (make_loc (b,b+String.length(string_of_id id)),id)
  else pr_id id

let pr_lname = function
    (loc,Name id) -> pr_lident (loc,id)
  | lna -> pr_located pr_name lna

let pr_or_var pr = function
  | Genarg.ArgArg x -> pr x
  | Genarg.ArgVar (loc,s) -> pr_lident (loc,s)

let las = lapp

let rec pr_patt sep inh p =
  let (strm,prec) = match p with
  | CPatAlias (_,p,id) ->
      pr_patt mt (las,E) p ++ str " as " ++ pr_id id, las
  | CPatCstr (_,c,[]) -> pr_reference c, latom
  | CPatCstr (_,c,args) ->
      pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp
  | CPatAtom (_,None) -> str "_", latom
  | CPatAtom (_,Some r) -> pr_reference r, latom
  | CPatNotation (_,"( _ )",[p]) ->
      pr_patt (fun()->str"(") (max_int,E) p ++ str")", latom
  | CPatNotation (_,s,env) -> pr_patnotation (pr_patt mt) s env
  | CPatNumeral (_,i) -> Bignat.pr_bigint i, latom
  | CPatDelimiters (_,k,p) -> pr_delimiters k (pr_patt mt lsimple p), 1
  in
  let loc = cases_pattern_loc p in
  pr_with_comments loc
    (sep() ++ if prec_less prec inh then strm else surround strm)

let pr_patt = pr_patt mt


let pr_eqn pr (loc,pl,rhs) =
  spc() ++ hov 4
    (pr_with_comments loc
      (str "| " ++
      hov 0 (prlist_with_sep sep_v (pr_patt ltop) pl ++ str " =>") ++
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
        | CCast(_,c,t) -> c, t
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
    
let pr_global vars ref =
  (* pr_global_env vars ref *)
  let s = string_of_qualid (Constrextern.shortest_qualid_of_v7_global vars ref) in
  (str s)

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

let pr_fixdecl pr prd dangling_with_for (id,n,bl,t,c) =
  let annot =
    let ids = names_of_local_assums bl in
    if List.length ids > 1 then 
      spc() ++ str "{struct " ++ pr_name (snd (List.nth ids n)) ++ str"}"
    else mt() in
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

let pr_arg pr x = spc () ++ pr x

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
  | CCases (_,(po,rtntypopt),c,eqns) ->
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
     
  | COrderedCase (_,st,po,c,[b1;b2]) when st = IfStyle ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
	 parsing est lui plus tolérant) *)
      hv 0 (
	hov 1 (str "if " ++ pr mt ltop c ++
                 pr_return_type (pr mt) po) ++ spc () ++
	hov 0 (str "then" ++ pr (fun () -> brk (1,1)) ltop b1) ++ spc () ++
	hov 0 (str "else" ++ pr (fun () -> brk (1,1)) ltop b2)),
      lif
  | COrderedCase (_,st,po,c,[CLambdaN(_,[nal,_],b)]) when st = LetStyle ->
      hv 0 (
        str "let " ++
	hov 0 (str "(" ++
               prlist_with_sep sep_v (fun (_,n) -> pr_name n) nal ++
               str ")" ++
	       pr_return_type (pr mt) po ++ str " :=" ++
               pr spc ltop c ++ str " in") ++
        pr spc ltop b),
      lletin

  | COrderedCase (_,style,po,c,bl) ->
      hv 0 (
	str (if style=MatchStyle then "old_match " else "match ") ++ 
	pr mt ltop c ++
	pr_return_type (pr_dangling_with_for mt) po ++
	str " with" ++ brk (1,0) ++
	hov 0 (prlist
          (fun b -> str "| ??? =>" ++ pr spc ltop b ++ fnl ()) bl) ++
        str "end"),
      latom
  | CHole _ -> str "_", latom
  | CEvar (_,n) -> str (Evd.string_of_existential n), latom
  | CPatVar (_,(_,p)) -> str "?" ++ pr_patvar p, latom
  | CSort (_,s) -> pr_sort s, latom
  | CCast (_,a,b) ->
      hv 0 (pr mt (lcast,L) a ++ cut () ++ str ":" ++ pr mt (-lcast,E) b),
      lcast
  | CNotation (_,"( _ )",[t]) ->
      pr (fun()->str"(") (max_int,L) t ++ str")", latom
  | CNotation (_,s,env) -> pr_notation (pr mt) s env
  | CNumeral (_,(Bignat.POS _ as p)) -> Bignat.pr_bigint p, lposint
  | CNumeral (_,(Bignat.NEG _ as p)) -> Bignat.pr_bigint p, lnegint
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

let rec abstract_constr_expr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,abstract_constr_expr c bl)
  | LocalRawAssum (idl,t)::bl ->
      List.fold_right (fun x b -> mkLambdaC([x],t,b)) idl
      (abstract_constr_expr c bl)
      
let rec prod_constr_expr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,prod_constr_expr c bl)
  | LocalRawAssum (idl,t)::bl ->
      List.fold_right (fun x b -> mkProdC([x],t,b)) idl
      (prod_constr_expr c bl)

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
    | _ -> anomaly "ppconstrnew: strip_context"

let transf istype env iscast bl c =
  let c' =
    if istype then prod_constr_expr c bl
    else abstract_constr_expr c bl in
  if Options.do_translate() then
    let r = 
      Constrintern.for_grammar
        (Constrintern.interp_rawconstr_gen istype Evd.empty env false ([],[]))
	c' in
    begin try
      (* Try to infer old case and type annotations *)
      let _ = Pretyping.understand_gen_tcc Evd.empty env [] None r in 
      (*msgerrnl (str "Typage OK");*) ()
    with e -> (*msgerrnl (str "Warning: can't type")*) () end;
    let c =
      (if istype then Constrextern.extern_rawtype
      else Constrextern.extern_rawconstr)
      (Termops.vars_of_env env) r in
    let n = local_binders_length bl in
    strip_context n iscast c
  else bl, c

let pr_constr_env env c = pr lsimple (snd (transf false env false [] c))
let pr_lconstr_env env c = pr ltop (snd (transf false env false [] c))
let pr_constr c = pr_constr_env (Global.env()) c
let pr_lconstr c = pr_lconstr_env (Global.env()) c

let pr_binders = pr_undelimited_binders (pr ltop)

let is_Eval_key c =
  Options.do_translate () &
  (let f id = let s = string_of_id id in s = "Eval" in
  let g = function
    | Ident(_,id) -> f id
    | Qualid (_,qid) -> let d,id = repr_qualid qid in d = empty_dirpath & f id
  in
  match c with
    | CRef ref | CApp (_,(_,CRef ref),_) when g ref -> true
    | _ -> false)

let pr_protect_eval c =
  if is_Eval_key c then h 0 (str "(" ++ pr ltop c ++ str ")") else pr ltop c

let pr_lconstr_env_n env iscast bl c =
  let bl, c = transf false env iscast bl c in
  bl, pr_protect_eval c
let pr_type_env_n env bl c = pr ltop (snd (transf true env false bl c))
let pr_type c = pr ltop (snd (transf true (Global.env()) false [] c))

let transf_pattern env c =
  if Options.do_translate() then
    Constrextern.extern_rawconstr (Termops.vars_of_env env)
      (Constrintern.for_grammar
	(Constrintern.interp_rawconstr_gen false Evd.empty env true ([],[]))
	c)
  else c

let pr_pattern c = pr lsimple (transf_pattern (Global.env()) c)

let pr_rawconstr_env env c =
  pr_constr (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)
let pr_lrawconstr_env env c =
  pr_lconstr (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)

let pr_cases_pattern = pr_patt ltop

let pr_pattern_occ prc = function
    ([],c) -> prc c
  | (nl,c) -> hov 1 (prc c ++ spc() ++ str"at " ++
                     hov 0 (prlist_with_sep spc int nl))

let pr_unfold_occ pr_ref = function
    ([],qid) -> pr_ref qid
  | (nl,qid) -> hov 1 (pr_ref qid ++ spc() ++ str"at " ++
                       hov 0 (prlist_with_sep spc int nl))

let pr_qualid qid = str (string_of_qualid qid)

open Rawterm

let pr_arg pr x = spc () ++ pr x

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
  | Simpl o -> str "simpl" ++ pr_opt (pr_pattern_occ pr_constr) o  
  | Cbv f ->
      if f = {rBeta=true;rIota=true;rZeta=true;rDelta=true;rConst=[]} then
	str "compute"
      else
	hov 1 (str "cbv" ++ pr_red_flag pr_ref f)
  | Lazy f -> 
      hov 1 (str "lazy" ++ pr_red_flag pr_ref f)
  | Unfold l ->
      hov 1 (str "unfold" ++ spc() ++
             prlist_with_sep pr_coma (pr_unfold_occ pr_ref) l)
  | Fold l -> hov 1 (str "fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l ->
      hov 1 (str "pattern" ++
        pr_arg (prlist_with_sep pr_coma (pr_pattern_occ pr_constr)) l)
        
  | Red true -> error "Shouldn't be accessible from user"
  | ExtraRedExpr (s,c) ->
      hov 1 (str s ++ pr_arg pr_constr c)

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

let pr_rawconstr_env_no_translate env c =
  pr lsimple (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)
let pr_lrawconstr_env_no_translate env c =
  pr ltop (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)

(* Printing reference with translation *)

let pr_reference r =
  let loc = loc_of_reference r in
  try match Nametab.extended_locate (snd (qualid_of_reference r)) with
    | TrueGlobal ref ->
        pr_with_comments loc
	  (pr_reference (Constrextern.extern_reference loc Idset.empty ref))
    | SyntacticDef kn ->
	let is_coq_root d =
	  let d = repr_dirpath d in
	  d <> [] & string_of_id (list_last d) = "Coq" in
        let dir,id = repr_path (sp_of_syntactic_definition kn) in
	let r =
          if (is_coq_root (Lib.library_dp()) or is_coq_root dir) then
	    (match Syntax_def.search_syntactic_definition loc kn with
	      | RRef (_,ref) ->
		  Constrextern.extern_reference dummy_loc Idset.empty ref
              | _ -> r)
          else r
	in pr_with_comments loc (pr_reference r)
  with Not_found ->
    error_global_not_found (snd (qualid_of_reference r))

(** constr printers *)

let pr_term_env env  c = pr lsimple (Constrextern.extern_constr false env c)
let pr_lterm_env env c = pr ltop    (Constrextern.extern_constr false env c)
let pr_term  c = pr_term_env  (Global.env()) c
let pr_lterm c = pr_lterm_env (Global.env()) c

let pr_constr_pattern_env env c =
  pr lsimple (Constrextern.extern_pattern env Termops.empty_names_context c)

let pr_constr_pattern t =
  pr lsimple
    (Constrextern.extern_pattern (Global.env()) Termops.empty_names_context t)


(************************************************************************)
(* Automatic standardisation of names in Arith and ZArith by translator *)
(* Very not robust *)

let is_to_rename dir id =
  let dirs = List.map string_of_id (repr_dirpath dir) in
  match List.rev dirs with
  | "Coq"::"Arith"::"Between"::_ -> false
  | "Coq"::"ZArith"::
    ("Wf_Z"|"Zpower"|"Zlogarithm"|"Zbinary"|"Zdiv"|"Znumtheory")::_ -> false
  | "Coq"::("Arith"|"NArith"|"ZArith")::_ -> true
  | "Coq"::"Init"::"Peano"::_ -> true
  | "Coq"::"Init"::"Logic"::_ when string_of_id id = "iff_trans" -> true
  | "Coq"::"Reals"::"RIneq"::_ -> true
  | _ -> false

let is_ref_to_rename ref =
  let sp = sp_of_global ref in
  is_to_rename (dirpath sp) (basename sp)

let get_name (ln,lp,lz,ll,lr,lr') id refbase n =
  let id' = string_of_id n in
  (match id' with
    | "nat" -> (id_of_string (List.hd ln),(List.tl ln,lp,lz,ll,lr,lr'))
    | "positive" -> (id_of_string (List.hd lp),(ln,List.tl lp,lz,ll,lr,lr'))
    | "Z" -> (id_of_string (List.hd lz),(ln,lp,List.tl lz,ll,lr,lr'))
    | "Prop" when List.mem (string_of_id id) ["a";"b";"c"] -> 
	(* pour iff_trans *)
	(id_of_string (List.hd ll),(ln,lp,lz,List.tl ll,lr,lr'))
    | "R" when (* Noms r,r1,r2 *)
	refbase = "Rle_refl" or
	refbase = "Rlt_monotony_contra" or 
	refbase = "Rmult_le_reg_l" or 
	refbase = "Rle_monotony_contra" or 
	refbase = "Rge_monotony" ->
	(id_of_string (List.hd lr')),(ln,lp,lz,ll,lr,List.tl lr')
    | "R" when (* Noms r1,r2,r3,r4 *)
	List.mem (string_of_id id)
	  ["x";"y";"x'";"y'";"z";"t";"n";"m";"a";"b";"c";"p";"q"] 
	& refbase <> "sum_inequa_Rle_lt"
	-> 
	(id_of_string (List.hd lr),(ln,lp,lz,ll,List.tl lr,lr'))
    | _ -> id,(ln,lp,lz,ll,lr,lr'))

let get_name_constr names id refbase t = match kind_of_term t with
  | Ind ind ->
      let n = basename (sp_of_global (IndRef ind)) in
      get_name names id refbase n
  | Const sp ->
      let n = basename (sp_of_global (ConstRef sp)) in
      get_name names id refbase n
  | Sort _ -> get_name names id refbase (id_of_string "Prop")
  | _ -> id,names

let names = 
  (["n";"m";"p";"q"],["p";"q";"r";"s"],["n";"m";"p";"q"],["A";"B";"C"],
   ["r1";"r2";"r3";"r4"],["r";"r1";"r2"])

let znames refbase t =
  let rec aux c names = match kind_of_term c with
    | Prod (Name id as na,t,c) ->
	let (id,names) = get_name_constr names id refbase t in
	(na,id) :: aux c names
    | Prod (Anonymous,t,c) ->
	(Anonymous,id_of_string "ZZ") :: aux c names
    | _ -> []
  in aux t names

let get_name_raw names id refbase t = match t with
  | CRef(Ident (_,n)) -> get_name names id refbase n
  | CSort _ -> get_name names id refbase (id_of_string "Prop")
  | _ -> id,names

let rename_bound_variables id0 t =
  if is_to_rename (Lib.library_dp()) id0 then
  let refbase = string_of_id id0 in
  let rec aux c names subst = match c with
    | CProdN (loc,bl,c) ->
	let rec aux2 names subst = function
	  | (nal,t)::bl ->
	      let rec aux3 names subst = function
		| (loc,Name id)::nal ->
		    let (id',names) = get_name_raw names id refbase t in
		    let (nal,names,subst) = aux3 names ((id,id')::subst) nal in
		    (loc,Name id')::nal, names, subst
		| x::nal -> 
		    let (nal,names,subst) = aux3 names subst nal in
		    x::nal,names,subst
		| [] -> [],names,subst in
	      let t = replace_vars_constr_expr subst t in
	      let nal,names,subst = aux3 names subst nal in
	      let bl,names,subst = aux2 names subst bl in
	      (nal,t)::bl, names, subst
	  | [] -> [],names,subst in
	let bl,names,subst = aux2 names subst bl in
	CProdN (loc,bl,aux c names subst)
    | CArrow (loc,t,u) ->
	let u = aux u names subst in
	CArrow (loc,replace_vars_constr_expr subst t,u)
    | _ -> replace_vars_constr_expr subst c
  in aux t names []
  else t

let translate_binding kn n ebl =
  let t = Retyping.get_type_of (Global.env()) Evd.empty (mkConst kn) in
  let subst= znames (string_of_id (basename (sp_of_global (ConstRef kn)))) t in
  try
    let _,subst' = list_chop n subst in
    List.map (function
      | (x,NamedHyp id,c) -> (x,NamedHyp (List.assoc (Name id) subst'),c)
      |  x -> x) ebl
  with _ -> ebl

let translate_with_bindings c bl =
  match bl with
  | ExplicitBindings l ->
      let l = match c with
	| RRef (_,(ConstRef kn as ref)) when is_ref_to_rename ref -> 
	    translate_binding kn 0 l
	| RApp (_,RRef (_,(ConstRef kn as ref)),args) when is_ref_to_rename ref
	    -> translate_binding kn (List.length args) l
	| _ ->
	    l
      in ExplicitBindings l
    | x -> x
