(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
let lapp = 10
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
  | t -> cut () ++ str ":" ++ pr t

let pr_opt_type_spc pr = function
  | CHole _ -> mt ()
  | t ->  str " :" ++ brk(1,2) ++ pr ltop t

let pr_name = function
  | Anonymous -> str"_"
  | Name id -> pr_id (Constrextern.v7_to_v8_id id)

let pr_located pr (loc,x) = pr x

let las = 12

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
     hov 0 (prlist_with_sep sep_v (pr_patt ltop) pl ++ str " =>") ++
     spc() ++ pr ltop rhs)

let surround p = str"(" ++ p ++ str")"

let pr_binder many pr (nal,t) =
  match t with
  | CHole _ -> prlist_with_sep sep (pr_located pr_name) nal
  | _ ->
    let s = prlist_with_sep sep (pr_located pr_name) nal ++ str ":" ++ pr t in
    hov 1 (if many then surround s else s)

let pr_binder_among_many pr_c = function
  | LocalRawAssum (nal,t) ->
      pr_binder true pr_c (nal,t)
  | LocalRawDef (na,c) ->
      let c,topt = match c with
        | CCast(_,c,t) -> c, t
        | _ -> c, CHole dummy_loc in
      hov 1 (surround
        (pr_located pr_name na ++ pr_opt_type pr_c topt ++
         str":=" ++ cut() ++ pr_c c))

let pr_undelimited_binders pr_c =
  prlist_with_sep sep (pr_binder_among_many pr_c)

let pr_delimited_binders pr_c = function
  | [LocalRawAssum (nal,t)] -> pr_binder false pr_c (nal,t)
  | LocalRawAssum _ :: _ as bdl -> pr_undelimited_binders pr_c bdl
  | _ -> assert false

let pr_let_binder pr x a =
  hov 0 (hov 0 (pr_name x ++ brk(0,1) ++ str ":=") ++ brk(0,1) ++ pr ltop a)

let rec extract_prod_binders = function
  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_prod_binders c in
      if bl = [] then [], x else LocalRawDef (na,b) :: bl, c
  | CProdN (loc,[],c) ->
      extract_prod_binders c
  | CProdN (loc,(nal,t)::bl,c) ->
      let bl,c = extract_prod_binders (CProdN(loc,bl,c)) in
      LocalRawAssum (nal,t) :: bl, c
  | c -> [], c

let rec extract_lam_binders = function
  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_lam_binders c in
      if bl = [] then [], x else LocalRawDef (na,b) :: bl, c
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
          Constrextern.check_same_type ty1 ty2;
          ty2 in
  LocalRawAssum ([na],ty)
            
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

(* Extrac lambdas when a type constraint occurs *)
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

let pr_recursive_decl pr id b t c =
  pr_id id ++ b ++ pr_opt_type_spc pr t ++ str " :=" ++
  brk(1,2) ++ pr ltop c

let name_of_binder = function
  | LocalRawAssum (nal,_) -> nal
  | LocalRawDef (_,_) -> []

let pr_fixdecl pr (id,n,t0,c0) =
  let (bl,t,c) = extract_def_binders t0 c0 in
  let (bl,t,c) =
    if List.length bl <= n then split_fix (n+1) t0 c0 else (bl,t,c) in
  let annot =
    let ids = List.flatten (List.map name_of_binder bl) in
    if List.length ids > 1 then 
      spc() ++ str "{struct " ++ pr_name (snd (list_last ids)) ++ str"}"
    else mt() in
  pr_recursive_decl pr id
    (str" " ++ hov 0 (pr_undelimited_binders (pr ltop) bl) ++ annot) t c

let pr_cofixdecl pr (id,t,c) =
  pr_recursive_decl pr id (mt ()) t c

let pr_recursive pr_decl id = function
  | [] -> anomaly "(co)fixpoint with no definition"
  | [d1] -> pr_decl d1
  | dl ->
      prlist_with_sep (fun () -> fnl() ++ str "with ") pr_decl dl ++
      fnl() ++ str "for " ++ pr_id id

let pr_arg pr x = spc () ++ pr x

let is_var id = function
  | CRef (Ident (_,id')) when id=id' -> true
  | _ -> false

let tm_clash = function
  | (CRef (Ident (_,id)), Some (_,_,nal)) when List.exists ((=) (Name id)) nal
      -> Some id
  | _ -> None

let pr_case_item pr (tm,(na,indnalopt)) =
  hov 0 (pr (lcast,E) tm ++
  (match na with
    | Name id when not (is_var id tm) -> spc () ++ str "as " ++  pr_id id
    | Anonymous when tm_clash (tm,indnalopt) <> None ->
	(* hide [tm] name to avoid conflicts *)
	spc () ++ str "as _" ++ pr_id (out_some (tm_clash (tm,indnalopt)))
    | _ -> mt ()) ++
  (match indnalopt with
    | None -> mt ()
    | Some (_,ind,nal) ->
        spc () ++ str "in " ++ 
        hov 0 (pr_reference ind ++ prlist (pr_arg pr_name) nal)))

let pr_case_type pr po =
  match po with
    | None | Some (CHole _) -> mt()
    | Some p -> spc() ++ str "return " ++ hov 0 (pr (lcast,E) p)

let pr_return_type pr po = pr_case_type pr po

let pr_simple_return_type pr na po =
  (match na with
    | Name id -> spc () ++ str "as " ++  pr_id id
    | _ -> mt ()) ++
  pr_case_type pr po

let pr_proj pr pr_app a f l =
  hov 0 (pr lsimple a ++ cut() ++ str ".(" ++ pr_app pr f l ++ str ")")

let pr_appexpl pr f l =
      hov 2 (
	str "@" ++ pr_reference f ++
	prlist (fun a -> spc () ++ pr (lapp,L) a) l)

let pr_app pr a l =
  hov 2 (
    pr (lapp,L) a  ++ 
    prlist (fun a -> spc () ++ pr_expl_args pr a) l)

let rec pr inherited a =
  let (strm,prec) = match a with
  | CRef r -> pr_reference r, latom
  | CFix (_,id,fix) ->
      let p = hov 0 (str"fix " ++ pr_recursive (pr_fixdecl pr) (snd id) fix) in
      (if List.length fix = 1 & prec_less (fst inherited) ltop
       then str"(" ++ p ++ str")" else p),
      lfix
  | CCoFix (_,id,cofix) ->
      hov 0 (str "cofix " ++ pr_recursive (pr_cofixdecl pr) (snd id) cofix),
      lfix
  | CArrow (_,a,b) ->
      hov 0 (pr (larrow,L) a ++ str " ->" ++ brk(1,0) ++ pr (-larrow,E) b),
      larrow
  | CProdN _ ->
      let (bl,a) = extract_prod_binders a in
      hov 2 (
	str"forall" ++ spc() ++ pr_delimited_binders (pr ltop) bl ++
        str "," ++ spc() ++ pr ltop a),
      lprod
  | CLambdaN _ ->
      let (bl,a) = extract_lam_binders a in
      hov 2 (
	str"fun" ++ spc() ++ pr_delimited_binders (pr ltop) bl ++
        str " =>" ++ spc() ++ pr ltop a),
      llambda
  | CLetIn (_,x,a,b) ->
      hv 0 (
        hov 2 (str "let " ++ pr_located pr_name x ++ str " :=" ++ spc() ++
               pr ltop a ++ str " in") ++
        spc () ++ pr ltop b),
      lletin
  | CAppExpl (_,(Some i,f),l) ->
      let l1,l2 = list_chop i l in
      let c,l1 = list_sep_last l1 in
      let p = pr_proj pr pr_appexpl c f l1 in
      if l2<>[] then
	p ++ prlist (fun a -> spc () ++ pr (lapp,L) a) l2, lapp
      else
	p, lproj
  | CAppExpl (_,(None,f),l) -> pr_appexpl pr f l, lapp
  | CApp (_,(Some i,f),l) ->
      let l1,l2 = list_chop i l in
      let c,l1 = list_sep_last l1 in
      assert (snd c = None);
      let p = pr_proj pr pr_app (fst c) f l1 in
      if l2<>[] then 
	p ++ prlist (fun a -> spc () ++ pr_expl_args pr a) l2, lapp
      else
	p, lproj
  | CApp (_,(None,a),l) -> pr_app pr a l, lapp
  | CCases (_,(po,rtntypopt),c,eqns) ->
      v 0
        (hov 4 (str "match " ++ 
	  hov 0 (
	    prlist_with_sep sep_v (pr_case_item pr) c
            ++ pr_case_type pr rtntypopt) ++
	str " with") ++
        prlist (pr_eqn pr) eqns ++ spc() ++ str "end"),
      latom
  | CLetTuple (_,nal,(na,po),c,b) ->
      hv 0 (
        str "let " ++
	hov 0 (str "(" ++
               prlist_with_sep sep_v pr_name nal ++
               str ")" ++
	       pr_simple_return_type pr na po ++ str " :=" ++
               spc() ++ pr ltop c ++ str " in") ++
        spc() ++ pr ltop b),
      lletin
  | CIf (_,c,(na,po),b1,b2) ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
	 parsing est lui plus tolérant) *)
      hv 0 (
	hov 1 (str "if " ++ pr ltop c ++ pr_simple_return_type pr na po) ++
	spc () ++
	hov 0 (str "then" ++ brk (1,1) ++ pr ltop b1) ++ spc () ++
	hov 0 (str "else" ++ brk (1,1) ++ pr ltop b2)),
      lif
     
  | COrderedCase (_,st,po,c,[b1;b2]) when st = IfStyle ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
	 parsing est lui plus tolérant) *)
      hv 0 (
	hov 1 (str "if " ++ pr ltop c ++ pr_return_type pr po) ++ spc () ++
	hov 0 (str "then" ++ brk (1,1) ++ pr ltop b1) ++ spc () ++
	hov 0 (str "else" ++ brk (1,1) ++ pr ltop b2)),
      lif
  | COrderedCase (_,st,po,c,[CLambdaN(_,[nal,_],b)]) when st = LetStyle ->
      hv 0 (
        str "let " ++
	hov 0 (str "(" ++
               prlist_with_sep sep_v (fun (_,n) -> pr_name n) nal ++
               str ")" ++
	       pr_return_type pr po ++ str " :=" ++
               spc() ++ pr ltop c ++ str " in") ++
        spc() ++ pr ltop b),
      lletin
  | COrderedCase (_,style,po,c,bl) ->
      hv 0 (
	str (if style=MatchStyle then "old_match " else "match ") ++ 
	pr ltop c ++
	pr_return_type pr po ++
	str " with" ++ brk (1,0) ++
	hov 0 (prlist
          (fun b -> str "| ??? =>" ++ spc() ++ pr ltop b ++ fnl ()) bl) ++
        str "end"),
      latom
  | CHole _ -> str "_", latom
(*
  | CEvar (_,n) -> str "?" ++ int n, latom
*)
  | CEvar (_,n) -> str (Evd.string_of_existential n), latom
  | CPatVar (_,(_,p)) -> str "?" ++ pr_patvar p, latom
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
	  [LocalRawAssum (nal1,t)], CLambdaN (loc,(nal2,t)::bll,c)
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

let transf istype env n iscast c =
  if Options.do_translate() then
    let r = 
      Constrintern.for_grammar
        (Constrintern.interp_rawconstr_gen istype Evd.empty env [] false 
	  ([],[]))
	c in
    begin try
      (* Try to infer old case and type annotations *)
      let _ = Pretyping.understand_gen_tcc Evd.empty env [] None r in 
      (*msgerrnl (str "Typage OK");*) ()
    with e -> (*msgerrnl (str "Warning: can't type")*) () end;
    let c =
      (if istype then Constrextern.extern_rawtype
      else Constrextern.extern_rawconstr)
      (Termops.vars_of_env env) r in
    strip_context n iscast c
  else [], c

let pr_constr_env env c = pr lsimple (snd (transf false env 0 false c))
let pr_lconstr_env env c = pr ltop (snd (transf false env 0 false c))
let pr_constr c = pr_constr_env (Global.env()) c
let pr_lconstr c = pr_lconstr_env (Global.env()) c

let pr_binders = pr_undelimited_binders (pr ltop)

let pr_lconstr_env_n env n b c =
  let bl, c = transf false env n b c in bl, pr ltop c
let pr_type_env_n env n c = pr ltop (snd (transf true env n false c))
let pr_type c = pr ltop (snd (transf true (Global.env()) 0 false c))

let transf_pattern env c =
  if Options.do_translate() then
    Constrextern.extern_rawconstr (Termops.vars_of_env env)
      (Constrintern.for_grammar
	(Constrintern.interp_rawconstr_gen false Evd.empty env [] true ([],[]))
	c)
  else c

let pr_pattern c = pr lsimple (transf_pattern (Global.env()) c)

let pr_rawconstr_env env c =
  pr_constr (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)
let pr_lrawconstr_env env c =
  pr_lconstr (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)

let pr_cases_pattern = pr_patt ltop

let pr_occurrences prc (nl,c) =
   prc c ++ prlist (fun n -> spc () ++ int n) nl

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
  | Simpl o -> str "simpl" ++ pr_opt (pr_occurrences pr_constr) o  
  | Cbv f ->
      if f = {rBeta=true;rIota=true;rZeta=true;rDelta=true;rConst=[]} then
	str "compute"
      else
	hov 1 (str "cbv" ++ pr_red_flag pr_ref f)
  | Lazy f -> 
      hov 1 (str "lazy" ++ pr_red_flag pr_ref f)
  | Unfold l ->
      hov 1 (str "unfold " ++
        prlist_with_sep pr_coma (fun (nl,qid) ->
	  pr_ref qid ++ prlist (pr_arg int) nl) l)
  | Fold l -> hov 1 (str "fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l ->
      hov 1 (str "pattern" ++
        pr_arg (prlist_with_sep pr_coma (pr_occurrences pr_constr)) l)
        
  | Red true -> error "Shouldn't be accessible from user"
  | ExtraRedExpr (s,c) ->
      hov 1 (str s ++ pr_arg pr_constr c)

let rec pr_may_eval prc prlc pr2 = function
  | ConstrEval (r,c) ->
      hov 0
        (str "eval" ++ brk (1,1) ++
         pr_red_expr (prc,prlc,pr2) r ++
	 str " in" ++ spc() ++ prc c)
  | ConstrContext ((_,id),c) ->
      hov 0
	(str "inst " ++ pr_id id ++ spc () ++
	 str "[" ++ prlc c ++ str "]")
  | ConstrTypeOf c -> hov 1 (str "check" ++ spc() ++ prc c)
  | ConstrTerm c -> prlc c

let pr_rawconstr_env_no_translate env c =
  pr lsimple (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)
let pr_lrawconstr_env_no_translate env c =
  pr ltop (Constrextern.extern_rawconstr (Termops.vars_of_env env) c)


let pr_pattern_env_no_translate env c =
  pr lsimple (Constrextern.extern_pattern env Termops.empty_names_context c)
