(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)      

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

let sep = fun _ -> brk(1,0)
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
let larrow = 80
let lnegint = 40
let lcast = 100
let lapp = 1
let ltop = (200,E)
let lsimple = (0,E)

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

open Symbols

let rec print_hunk n pr env = function
  | UnpMetaVar (e,prec) -> pr (n,prec) (env_assoc_value e env)
  | UnpTerminal s -> str s
  | UnpBox (b,sub) -> ppcmd_of_box b (prlist (print_hunk n pr env) sub)
  | UnpCut cut -> ppcmd_of_cut cut

let pr_notation pr s env =
  let unpl, level = find_notation_printing_rule s in
  prlist (print_hunk level pr env) unpl, level

let pr_delimiters key strm =
  strm ++ str ("%"^key)

open Rawterm

let pr_opt pr = function
  | None -> mt ()
  | Some x -> spc () ++ pr x

let pr_universe u = str "<univ>"

let pr_sort = function
  | RProp Term.Null -> str "Prop"
  | RProp Term.Pos -> str "Set"
  | RType u -> str "Type" ++ pr_opt pr_universe u

let pr_explicitation = function
  | None -> mt ()
  | Some n -> str "@" ++ int n ++ str ":="

let pr_expl_args pr (a,expl) =
  pr_explicitation expl ++ pr (lapp,L) a

let pr_opt_type pr = function
  | CHole _ -> mt ()
  | t -> cut () ++ str ":" ++ pr (if !Options.p1 then ltop else (latom,E)) t

let pr_opt_type_spc pr = function
  | CHole _ -> mt ()
  | t ->  str " :" ++ brk(1,2) ++ pr ltop t

let pr_name = function
  | Anonymous -> str"_"
  | Name id -> pr_id id

let pr_located pr (loc,x) = pr x

let las = 2

let rec pr_patt inh p =
  let (strm,prec) = match p with
  | CPatAlias (_,p,id) ->
      pr_patt (las,E) p ++ str " as " ++ pr_id id, las
  | CPatCstr (_,c,[]) -> pr_reference c, latom
  | CPatCstr (_,c,args) ->
      pr_reference c ++ spc() ++
      prlist_with_sep sep (pr_patt (lapp,L)) args, lapp
  | CPatAtom (_,None) -> str "_", latom
  | CPatAtom (_,Some r) -> pr_reference r, latom
  | CPatNumeral (_,i) -> Bignat.pr_bigint i, latom
  | CPatDelimiters (_,k,p) ->
      pr_delimiters k (pr_patt (latom,E) p), latom
  in
  if prec_less prec inh then strm
  else str"(" ++ strm ++ str")"

let pr_eqn pr (_,pl,rhs) =
  spc() ++ hov 4
    (str "| " ++
     hv 0 (prlist_with_sep sep_v (pr_patt ltop) pl ++ str " =>") ++
     spc() ++ pr ltop rhs)


(*
let pr_binder pr (nal,t) =
  hov 0 (
    prlist_with_sep sep (pr_located pr_name) nal ++
    pr_opt_type pr t)
*)
(* Option 1a *)
let pr_oneb pr t na =
  match t with
      CHole _ -> pr_located pr_name na
    | _ -> hov 1
        (str "(" ++  pr_located pr_name na ++ pr_opt_type pr t ++ str ")")
let pr_binder1 pr (nal,t) =
  hov 0 (prlist_with_sep sep (pr_oneb pr t) nal)

let pr_binders1 pr bl =
  hv 0 (prlist_with_sep sep (pr_binder1 pr) bl)

(* Option 1b *)
let pr_binder1 pr (nal,t) =
  match t with
      CHole _ -> prlist_with_sep sep (pr_located pr_name) nal
    | _ -> hov 1
	(str "(" ++ prlist_with_sep sep (pr_located pr_name) nal ++ str ":" ++
	 pr ltop t ++ str ")")

let pr_binders1 pr bl =
  hv 0 (prlist_with_sep sep (pr_binder1 pr) bl)

let pr_opt_type' pr = function
  | CHole _ -> mt ()
  | t -> cut () ++ str ":" ++ pr (latom,E) t

let pr_prod_binders1 pr = function
(*  | [nal,t] -> hov 1 (prlist_with_sep sep (pr_located pr_name) nal ++ pr_opt_type' pr t)*)
  | bl -> pr_binders1 pr bl

(* Option 2 *)
let pr_let_binder pr x a =
  hov 0 (hov 0 (pr_name x ++ brk(0,1) ++ str ":=") ++ brk(0,1) ++ pr ltop a)

let pr_binder2 pr (nal,t) =
  hov 0 (
    prlist_with_sep sep (pr_located pr_name) nal ++
    pr_opt_type pr t)

let pr_binders2 pr bl =
  hv 0 (prlist_with_sep sep (pr_binder2 pr) bl)

let pr_prod_binder2 pr (nal,t) =
  str "forall " ++ hov 0 (
    prlist_with_sep sep (pr_located pr_name) nal ++
    pr_opt_type pr t) ++ str ","

let pr_prod_binders2 pr bl =
  hv 0 (prlist_with_sep sep (pr_prod_binder2 pr) bl)

(**)
let pr_binders pr = (if !Options.p1 then pr_binders1 else pr_binders2) pr
let pr_prod_binders pr bl = 
  if !Options.p1 then 
    str "!" ++ pr_prod_binders1 pr bl ++ str "."
  else
    pr_prod_binders2 pr bl

let pr_arg_binders pr bl =
  if bl = [] then mt() else (spc() ++ pr_binders pr bl)

let pr_global vars ref = pr_global_env vars ref

let split_lambda = function
  | CLambdaN (loc,[[na],t],c) -> (na,t,c)
  | CLambdaN (loc,([na],t)::bl,c) -> (na,t,CLambdaN(loc,bl,c))
  | CLambdaN (loc,(na::nal,t)::bl,c) -> (na,t,CLambdaN(loc,(nal,t)::bl,c))
  | _ -> anomaly "ill-formed fixpoint body"

let split_product = function
  | CArrow (loc,t,c) -> ((loc,Anonymous),t,c)
  | CProdN (loc,[[na],t],c) -> (na,t,c)
  | CProdN (loc,([na],t)::bl,c) -> (na,t,CProdN(loc,bl,c))
  | CProdN (loc,(na::nal,t)::bl,c) -> (na,t,CProdN(loc,(nal,t)::bl,c))
  | _ -> anomaly "ill-formed fixpoint body"

let rec extract_lam_binders c =
  match c with
      CLambdaN(loc,bl1,c') ->
        let (bl,bd) = extract_lam_binders c' in
        (bl1@bl, bd)
    | _ -> ([],c)

let rec extract_prod_binders c =
  match c with
      CProdN(loc,bl1,c') ->
        let (bl,bd) = extract_prod_binders c' in
        (bl1@bl, bd)
    | _ -> ([],c)

let rec check_same_pattern p1 p2 =
  match p1, p2 with
    | CPatAlias(_,a1,i1), CPatAlias(_,a2,i2) when i1=i2 ->
        check_same_pattern a1 a2
    | CPatCstr(_,c1,a1), CPatCstr(_,c2,a2) when c1=c2 ->
        List.iter2 check_same_pattern a1 a2
    | CPatAtom(_,r1), CPatAtom(_,r2) when r1=r2 -> ()
    | CPatNumeral(_,i1), CPatNumeral(_,i2) when i1=i2 -> ()
    | CPatDelimiters(_,s1,e1), CPatDelimiters(_,s2,e2) when s1=s2 ->
        check_same_pattern e1 e2
    | _ -> failwith "not same pattern"

let check_same_ref r1 r2 =
  match r1,r2 with
  | Qualid(_,q1), Qualid(_,q2) when q1=q2 -> ()
  | Ident(_,i1), Ident(_,i2) when i1=i2 -> ()
  | _ -> failwith "not same ref"

let rec check_same_type ty1 ty2 =
  match ty1, ty2 with
  | CRef r1, CRef r2 -> check_same_ref r1 r2
  | CFix(_,(_,id1),fl1), CFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,i1,a1,b1) (id2,i2,a2,b2) ->
        if id1<>id2 || i1<>i2 then failwith "not same fix";
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CCoFix(_,(_,id1),fl1), CCoFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,a1,b1) (id2,a2,b2) ->
        if id1<>id2 then failwith "not same fix";
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CArrow(_,a1,b1), CArrow(_,a2,b2) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CProdN(_,bl1,a1), CProdN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLambdaN(_,bl1,a1), CLambdaN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLetIn(_,(_,na1),a1,b1), CLetIn(_,(_,na2),a2,b2) when na1=na2 ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CAppExpl(_,r1,al1), CAppExpl(_,r2,al2) when r1=r2 ->
      List.iter2 check_same_type al1 al2
  | CApp(_,e1,al1), CApp(_,e2,al2) ->
      check_same_type e1 e2;
      List.iter2 (fun (a1,e1) (a2,e2) ->
                    if e1<>e2 then failwith "not same expl";
                    check_same_type a1 a2) al1 al2
  | CCases(_,_,a1,brl1), CCases(_,_,a2,brl2) ->
      List.iter2 check_same_type a1 a2;
      List.iter2 (fun (_,pl1,r1) (_,pl2,r2) ->
        List.iter2 check_same_pattern pl1 pl2;
        check_same_type r1 r2) brl1 brl2
  | COrderedCase(_,_,_,a1,bl1), COrderedCase(_,_,_,a2,bl2) ->
      check_same_type a1 a2;
      List.iter2 check_same_type bl1 bl2
  | CHole _, CHole _ -> ()
  | CMeta(_,i1), CMeta(_,i2) when i1=i2 -> ()
  | CSort(_,s1), CSort(_,s2) when s1=s2 -> ()
  | CCast(_,a1,b1), CCast(_,a2,b2) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CNotation(_,n1,e1), CNotation(_,n2,e2) when n1=n2 ->
      List.iter2 check_same_type e1 e2
  | CNumeral(_,i1), CNumeral(_,i2) when i1=i2 -> ()
  | CDelimiters(_,s1,e1), CDelimiters(_,s2,e2) when s1=s2 ->
      check_same_type e1 e2
  | _ when ty1=ty2 -> ()
  | _ -> failwith "not same type"

and check_same_binder (nal1,e1) (nal2,e2) =
  List.iter2 (fun (_,na1) (_,na2) ->
    if na1<>na2 then failwith "not same name") nal1 nal2;
  check_same_type e1 e2

let merge_binders (na1,ty1) (na2,ty2) =
  let na =
    match snd na1, snd na2 with
        Anonymous, Name id -> na2
      | Name id, Anonymous -> na1
      | Anonymous, Anonymous -> na1
      | Name id1, Name id2 ->
          if id1 <> id2 then failwith "not same name" else na1 in
  let ty =
    match ty1, ty2 with
        CHole _, _ -> ty2
      | _, CHole _ -> ty1
      | _ ->
          check_same_type ty1 ty2;
          ty2 in
  ([na],ty)
            
let rec strip_domain bvar c =
  match c with
    | CArrow(loc,a,b) ->
        (merge_binders bvar ((dummy_loc,Anonymous),a), b)
    | CProdN(loc,[([na],ty)],c') ->
        (merge_binders bvar (na,ty), c')
    | CProdN(loc,([na],ty)::bl,c') ->
        (merge_binders bvar (na,ty), CProdN(loc,bl,c'))
    | CProdN(loc,(na::nal,ty)::bl,c') ->
        (merge_binders bvar (na,ty), CProdN(loc,(nal,ty)::bl,c'))
    | _ -> failwith "not a product"

(* Note: binder sharing is lost *)
let rec strip_domains (nal,ty) c =
  match nal with
      [] -> assert false
    | [na] ->
        let bnd, c' = strip_domain (na,ty) c in
        ([bnd],None,c')
    | na::nal ->
        let bnd, c1 = strip_domain (na,ty) c in
        (try
          let bl, rest, c2 = strip_domains (nal,ty) c1 in
          (bnd::bl, rest, c2)
        with Failure _ -> ([bnd],Some (nal,ty), c1))

let rec extract_def_binders c ty =
  match c with
    | CLambdaN(loc,bvar::lams,b) ->
        (try
          let bvar', rest, ty' = strip_domains bvar ty in
          let c' =
            match rest, lams with
                None,[] -> b
              | None, _ -> CLambdaN(loc,lams,b)
              | Some bvar,_ -> CLambdaN(loc,bvar::lams,b) in
          let (bl,c2,ty2) = extract_def_binders c' ty' in
          (bvar'@bl, c2, ty2)
        with Failure _ ->
          ([],c,ty))
    | _ -> ([],c,ty)

let rec split_fix n typ def =
  if n = 0 then ([],typ,def)
  else
    let (na,_,def) = split_lambda def in
    let (_,t,typ) = split_product typ in
    let (bl,typ,def) = split_fix (n-1) typ def in
    (([na],t)::bl,typ,def)

let pr_recursive_decl pr id b t c =
  pr_id id ++ b ++ pr_opt_type_spc pr t ++ str " :=" ++
  brk(1,2) ++ pr ltop c

let pr_fixdecl pr (id,n,t0,c0) =
  let (bl,t,c) = extract_def_binders t0 c0 in
  let (bl,t,c) =
    if List.length bl <= n then split_fix (n+1) t0 c0 else (bl,t,c) in
  let annot =
    let ids = List.flatten (List.map fst bl) in
    if List.length ids > 1 then 
      spc() ++ str "{struct " ++ pr_name (snd (list_last ids)) ++ str"}"
    else mt() in
  pr_recursive_decl pr id (str" " ++ hov 0 (pr_binders pr bl) ++ annot) t c

let pr_cofixdecl pr (id,t,c) =
  pr_recursive_decl pr id (mt ()) t c

let pr_recursive pr_decl id = function
  | [] -> anomaly "(co)fixpoint with no definition"
  | [d1] -> pr_decl d1
  | dl ->
      prlist_with_sep (fun () -> fnl() ++ str "with ") pr_decl dl ++
      fnl() ++ str "for " ++ pr_id id

let pr_annotation pr po =
  match po with
      None -> mt()
    | Some p -> spc() ++ str "=> " ++ hov 0 (pr ltop p)

let rec pr inherited a =
  let (strm,prec) = match a with
  | CRef r -> pr_reference r, latom
  | CFix (_,id,fix) ->
      hov 0 (str "fix " ++ pr_recursive (pr_fixdecl pr) (snd id) fix),
      lfix
  | CCoFix (_,id,cofix) ->
      hov 0 (str "cofix " ++ pr_recursive (pr_cofixdecl pr) (snd id) cofix),
      lfix
  | CArrow (_,a,b) ->
      hov 0 (pr (larrow,L) a ++ str " ->" ++ brk(1,0) ++ pr (-larrow,E) b),
      larrow
  | CProdN _ ->
      let (bl,a) = extract_prod_binders a in
      hv 0 (pr_prod_binders pr bl ++ spc() ++ pr ltop a),
      lprod
  | CLambdaN _ ->
      let (bl,a) = extract_lam_binders a in
      let left, mid = str"fun" ++ spc(), " =>" in
      hov 2 (
	left ++ pr_binders pr bl ++
        str mid ++ spc() ++ pr ltop a),
      llambda
  | CLetIn (_,x,a,b) ->
      let (bl,a) = extract_lam_binders a in
      hv 0 (
        hov 2 (str "let " ++ pr_located pr_name x ++
               pr_arg_binders pr bl ++ str " :=" ++ spc() ++
               pr ltop a ++ str " in") ++
        spc () ++ pr ltop b),
      lletin
  | CAppExpl (_,f,l) ->
      hov 2 (
	str "@" ++ pr_reference f ++
	prlist (fun a -> spc () ++ pr (lapp,L) a) l),
      lapp
  | CApp (_,a,l) ->
      hov 2 (
	pr (lapp,L) a  ++ 
	prlist (fun a -> spc () ++ pr_expl_args pr a) l),
      lapp
  | CCases (_,po,c,eqns) ->
      v 0
        (hov 4 (str "match " ++ prlist_with_sep sep_v (pr ltop) c ++
                str " with") ++
        prlist (pr_eqn pr) eqns ++
        spc() ++ pr_annotation pr po ++ str "end"),
      latom
  | COrderedCase (_,_,po,c,[b1;b2]) ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
	 parsing est lui plus tolérant) *)
      hv 0 (
	str "if " ++ pr ltop c ++ pr_annotation pr po ++ spc () ++
	hov 0 (str "then" ++ brk (1,1) ++ pr ltop b1) ++ spc () ++
	hov 0 (str "else" ++ brk (1,1) ++ pr ltop b2)),
      lif
  | COrderedCase (_,_,po,c,[CLambdaN(_,[nal,_],b)]) ->
      hv 0 (
        str "let " ++
	hov 0 (str "(" ++
               prlist_with_sep sep_v (fun (_,n) -> pr_name n) nal ++
               str ")" ++
	       pr_annotation pr po ++ str " :=" ++
               spc() ++ pr ltop c ++ str " in") ++
        spc() ++ pr ltop b),
      lletin
  | COrderedCase (_,style,po,c,bl) ->
      hv 0 (
	str (if style=MatchStyle then "old_match " else "match ") ++ 
	pr ltop c ++
	pr_annotation pr po ++
	str " with" ++ brk (1,0) ++
	hov 0 (prlist
          (fun b -> str "| ??? =>" ++ spc() ++ pr ltop b ++ fnl ()) bl) ++
        str "end"),
      latom
  | CHole _ -> str "_", latom
  | CMeta (_,p) -> str "?" ++ int p, latom
  | CSort (_,s) -> pr_sort s, latom
  | CCast (_,a,b) ->
      hv 0 (pr (lcast,L) a ++ cut () ++ str ":" ++ pr (-lcast,E) b), lcast
  | CNotation (_,s,env) -> pr_notation pr s env
  | CNumeral (_,(Bignat.POS _ as p)) -> Bignat.pr_bigint p, latom
  | CNumeral (_,(Bignat.NEG _ as p)) -> Bignat.pr_bigint p, lnegint
  | CDelimiters (_,sc,a) -> pr_delimiters sc (pr (latom,E) a), latom
  | CDynamic _ -> str "<dynamic>", latom
  in
  if prec_less prec inherited then strm
  else str"(" ++ strm ++ str")"

let transf env c =
  if Options.do_translate() then
    Constrextern.extern_rawconstr (Termops.vars_of_env env)
      (Constrintern.for_grammar
        (Constrintern.interp_rawconstr Evd.empty env) c)
  else c

let pr_constr_env env c = pr lsimple (transf env c)
let pr_lconstr_env env c = pr ltop (transf env c)
let pr_constr c = pr_constr_env (Global.env()) c
let pr_lconstr c = pr_lconstr_env (Global.env()) c

let pr_rawconstr_env env c =
  pr_constr (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)
let pr_lrawconstr_env env c =
  pr_lconstr (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)

let anonymize_binder na c =
  if Options.do_translate() then
    Constrextern.extern_rawconstr (Termops.vars_of_env (Global.env()))
      (Reserve.anonymize_if_reserved na
      (Constrintern.for_grammar
        (Constrintern.interp_rawconstr Evd.empty (Global.env())) c))
  else c

let pr_binders l =
  prlist_with_sep sep
    (fun (nal,t) -> prlist_with_sep sep
      (fun (_,na as x) -> pr_oneb pr (anonymize_binder na t) x) nal) l

let pr_cases_pattern = pr_patt ltop

let pr_pattern = pr_constr
let pr_occurrences prc (nl,c) =
  prlist (fun n -> int n ++ spc ()) nl ++
  str"(" ++ prc c ++ str")"

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
  | Simpl o -> str "simpl" ++ pr_opt (pr_occurrences pr_lconstr) o  
  | Cbv f ->
      if f = {rBeta=true;rIota=true;rZeta=true;rDelta=true;rConst=[]} then
	str "compute"
      else
	hov 1 (str "cbv" ++ pr_red_flag pr_ref f)
  | Lazy f -> 
      hov 1 (str "lazy" ++ pr_red_flag pr_ref f)
  | Unfold l ->
      hov 1 (str "unfold" ++
        prlist (fun (nl,qid) ->
	  prlist (pr_arg int) nl ++ spc () ++ pr_ref qid) l)
  | Fold l -> hov 1 (str "fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l ->
      hov 1 (str "pattern" ++ pr_arg (prlist (pr_occurrences pr_lconstr)) l)
        
  | Red true -> error "Shouldn't be accessible from user"
  | ExtraRedExpr (s,c) ->
      hov 1 (str s ++ pr_arg pr_constr c)

let rec pr_may_eval prc prlc pr2 = function
  | ConstrEval (r,c) ->
      hov 0
        (str "eval" ++ brk (1,1) ++
         pr_red_expr (prc,prlc,pr2) r ++
	 str " in" ++ spc() ++ prlc c)
  | ConstrContext ((_,id),c) ->
      hov 0
	(str "inst " ++ pr_id id ++ spc () ++
	 str "[" ++ prlc c ++ str "]")
  | ConstrTypeOf c -> hov 1 (str "check" ++ spc() ++ prlc c)
  | ConstrTerm c -> prlc c
