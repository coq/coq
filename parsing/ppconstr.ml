(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Errors
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
open Glob_term
open Constrextern
open Termops
(*i*)

let sep_v = fun _ -> str"," ++ spc()
let pr_tight_coma () = str "," ++ cut ()

let latom = 0
let lprod = 200
let llambda = 200
let lif = 200
let lletin = 200
let lletpattern = 200
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

open Notation

let print_hunks n pr pr_binders (terms,termlists,binders) unp =
  let env = ref terms and envlist = ref termlists and bll = ref binders in
  let pop r = let a = List.hd !r in r := List.tl !r; a in
  let rec aux = function
  | [] -> mt ()
  | UnpMetaVar (_,prec) :: l ->
      let c = pop env in pr (n,prec) c ++ aux l
  | UnpListMetaVar (_,prec,sl) :: l ->
      let cl = pop envlist in
      let pp1 = prlist_with_sep (fun () -> aux sl) (pr (n,prec)) cl in
      let pp2 = aux l in
      pp1 ++ pp2
  | UnpBinderListMetaVar (_,isopen,sl) :: l ->
      let cl = pop bll in pr_binders (fun () -> aux sl) isopen cl ++ aux l
  | UnpTerminal s :: l -> str s ++ aux l
  | UnpBox (b,sub) :: l ->
      (* Keep order: side-effects *)
      let pp1 = ppcmd_of_box b (aux sub) in
      let pp2 = aux l in
      pp1 ++ pp2
  | UnpCut cut :: l -> ppcmd_of_cut cut ++ aux l in
  aux unp

let pr_notation pr pr_binders s env =
  let unpl, level = find_notation_printing_rule s in
  print_hunks level pr pr_binders env unpl, level

let pr_delimiters key strm =
  strm ++ str ("%"^key)

let pr_generalization bk ak c =
  let hd, tl =
    match bk with
    | Implicit -> "{", "}"
    | Explicit -> "(", ")"
  in (* TODO: syntax Abstraction Kind *)
    str "`" ++ str hd ++ c ++ str tl

let pr_com_at n =
  if Flags.do_beautify() && n <> 0 then comment n
  else mt()

let pr_with_comments loc pp = pr_located (fun x -> x) (loc,pp)

let pr_sep_com sep f c = pr_with_comments (constr_loc c) (sep() ++ f c)

let pr_in_comment pr x = str "(* " ++ pr x ++ str " *)"

let pr_universe = Univ.pr_uni

let pr_glob_sort = function
  | GProp Term.Null -> str "Prop"
  | GProp Term.Pos -> str "Set"
  | GType u -> hov 0 (str "Type" ++ pr_opt (pr_in_comment pr_universe) u)

let pr_id = pr_id
let pr_name = pr_name
let pr_qualid = pr_qualid
let pr_patvar = pr_id

let pr_expl_args pr (a,expl) =
  match expl with
  | None -> pr (lapp,L) a
  | Some (_,ExplByPos (n,_id)) ->
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

let pr_evar pr n l =
  hov 0 (str (Evd.string_of_existential n) ++
  (match l with
   | Some l ->
       spc () ++ pr_in_comment
         (fun l ->
	   str"[" ++ hov 0 (prlist_with_sep pr_comma (pr ltop) l) ++ str"]")
         (List.rev l)
   | None -> mt()))

let las = lapp
let lpator = 100
let lpatrec = 0

let rec pr_patt sep inh p =
  let (strm,prec) = match p with
  | CPatRecord (_, l) ->
      let pp (c, p) =
	pr_reference c ++ spc() ++ str ":=" ++ pr_patt spc (lpatrec, Any) p in
      str "{| " ++ prlist_with_sep pr_semicolon pp l ++ str " |}", lpatrec
  | CPatAlias (_,p,id) ->
      pr_patt mt (las,E) p ++ str " as " ++ pr_id id, las
  | CPatCstr (_,c,[]) -> pr_reference c, latom
  | CPatCstr (_,c,args) ->
      pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp
  | CPatCstrExpl (_,c,args) ->
      str "@" ++ pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp
  | CPatAtom (_,None) -> str "_", latom
  | CPatAtom (_,Some r) -> pr_reference r, latom
  | CPatOr (_,pl) ->
      hov 0 (prlist_with_sep pr_bar (pr_patt spc (lpator,L)) pl), lpator
  | CPatNotation (_,"( _ )",([p],[])) ->
      pr_patt (fun()->str"(") (max_int,E) p ++ str")", latom
  | CPatNotation (_,s,(l,ll)) ->
      pr_notation (pr_patt mt) (fun _ _ _ -> mt()) s (l,ll,[])
  | CPatPrim (_,p) -> pr_prim_token p, latom
  | CPatDelimiters (_,k,p) -> pr_delimiters k (pr_patt mt lsimple p), 1
  in
  let loc = cases_pattern_expr_loc p in
  pr_with_comments loc
    (sep() ++ if prec_less prec inh then strm else surround strm)

let pr_patt = pr_patt mt

let pr_eqn pr (loc,pl,rhs) =
  let pl = List.map snd pl in
  spc() ++ hov 4
    (pr_with_comments loc
      (str "| " ++
      hov 0 (prlist_with_sep pr_bar (prlist_with_sep sep_v (pr_patt ltop)) pl
             ++ str " =>") ++
      pr_sep_com spc (pr ltop) rhs))

let begin_of_binder = function
    LocalRawDef((loc,_),_) -> fst (unloc loc)
  | LocalRawAssum((loc,_)::_,_,_) -> fst (unloc loc)
  | _ -> assert false

let begin_of_binders = function
  | b::_ -> begin_of_binder b
  | _ -> 0

let surround_impl k p =
  match k with
  | Explicit -> str"(" ++ p ++ str")"
  | Implicit -> str"{" ++ p ++ str"}"

let surround_implicit k p =
  match k with
  | Explicit -> p
  | Implicit -> (str"{" ++ p ++ str"}")

let pr_binder many pr (nal,k,t) =
  match k with
    | Generalized (b, b', t') ->
      assert (b=Implicit);
      begin match nal with
	|[loc,Anonymous] ->
	  hov 1 (str"`" ++ (surround_impl b'
			      ((if t' then str "!" else mt ()) ++ pr t)))
	|[loc,Name id] ->
	  hov 1 (str "`" ++ (surround_impl b'
			       (pr_lident (loc,id) ++ str " : " ++
				  (if t' then str "!" else mt()) ++ pr t)))
	|_ -> anomaly "List of generalized binders have alwais one element."
      end
    | Default b ->
      match t with
	| CHole _ ->
	  let s = prlist_with_sep spc pr_lname nal in
	  hov 1 (surround_implicit b s)
	| _ ->
	  let s = prlist_with_sep spc pr_lname nal ++ str " : " ++ pr t in
	  hov 1 (if many then surround_impl b s else surround_implicit b s)

let pr_binder_among_many pr_c = function
  | LocalRawAssum (nal,k,t) ->
      pr_binder true pr_c (nal,k,t)
  | LocalRawDef (na,c) ->
      let c,topt = match c with
        | CCast(_,c, CastConv (_,t)) -> c, t
        | _ -> c, CHole (dummy_loc, None) in
      surround (pr_lname na ++ pr_opt_type pr_c topt ++
         str":=" ++ cut() ++ pr_c c)

let pr_undelimited_binders sep pr_c =
  prlist_with_sep sep (pr_binder_among_many pr_c)

let pr_delimited_binders kw sep pr_c bl =
  let n = begin_of_binders bl in
  match bl with
  | [LocalRawAssum (nal,k,t)] ->
      pr_com_at n ++ kw() ++ pr_binder false pr_c (nal,k,t)
  | LocalRawAssum _ :: _ as bdl ->
      pr_com_at n ++ kw() ++ pr_undelimited_binders sep pr_c bdl
  | _ -> assert false

let pr_binders_gen pr_c sep is_open =
  if is_open then pr_delimited_binders mt sep pr_c
  else pr_undelimited_binders sep pr_c

let rec extract_prod_binders = function
(*  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_prod_binders c in
      if bl = [] then [], x else LocalRawDef (na,b) :: bl, c*)
  | CProdN (loc,[],c) ->
      extract_prod_binders c
  | CProdN (loc,(nal,bk,t)::bl,c) ->
      let bl,c = extract_prod_binders (CProdN(loc,bl,c)) in
      LocalRawAssum (nal,bk,t) :: bl, c
  | c -> [], c

let rec extract_lam_binders = function
(*  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_lam_binders c in
      if bl = [] then [], x else LocalRawDef (na,b) :: bl, c*)
  | CLambdaN (loc,[],c) ->
      extract_lam_binders c
  | CLambdaN (loc,(nal,bk,t)::bl,c) ->
      let bl,c = extract_lam_binders (CLambdaN(loc,bl,c)) in
      LocalRawAssum (nal,bk,t) :: bl, c
  | c -> [], c

let split_lambda = function
  | CLambdaN (loc,[[na],bk,t],c) -> (na,t,c)
  | CLambdaN (loc,([na],bk,t)::bl,c) -> (na,t,CLambdaN(loc,bl,c))
  | CLambdaN (loc,(na::nal,bk,t)::bl,c) -> (na,t,CLambdaN(loc,(nal,bk,t)::bl,c))
  | _ -> anomaly "ill-formed fixpoint body"

let rename na na' t c =
  match (na,na') with
    | (_,Name id), (_,Name id') -> (na',t,replace_vars_constr_expr [id,id'] c)
    | (_,Name id), (_,Anonymous) -> (na,t,c)
    | _ -> (na',t,c)

let split_product na' = function
  | CProdN (loc,[[na],bk,t],c) -> rename na na' t c
  | CProdN (loc,([na],bk,t)::bl,c) -> rename na na' t (CProdN(loc,bl,c))
  | CProdN (loc,(na::nal,bk,t)::bl,c) ->
      rename na na' t (CProdN(loc,(nal,bk,t)::bl,c))
  | _ -> anomaly "ill-formed fixpoint body"

let rec split_fix n typ def =
  if n = 0 then ([],typ,def)
  else
    let (na,_,def) = split_lambda def in
    let (na,t,typ) = split_product na typ in
    let (bl,typ,def) = split_fix (n-1) typ def in
    (LocalRawAssum ([na],default_binder_kind,t)::bl,typ,def)

let pr_recursive_decl pr pr_dangling dangling_with_for id bl annot t c =
  let pr_body =
    if dangling_with_for then pr_dangling else pr in
  pr_id id ++ str" " ++
  hov 0 (pr_undelimited_binders spc (pr ltop) bl ++ annot) ++
  pr_opt_type_spc pr t ++ str " :=" ++
  pr_sep_com (fun () -> brk(1,2)) (pr_body ltop) c

let pr_guard_annot pr_aux bl (n,ro) =
  match n with
    | None -> mt ()
    | Some (loc, id) ->
      match (ro : Topconstr.recursion_order_expr) with
	| CStructRec ->
	  let names_of_binder = function
	    | LocalRawAssum (nal,_,_) -> nal
	    | LocalRawDef (_,_) -> []
	  in let ids = List.flatten (List.map names_of_binder bl) in
	     if List.length ids > 1 then
	       spc() ++ str "{struct " ++ pr_id id ++ str"}"
	     else mt()
	| CWfRec c ->
	  spc() ++ str "{wf " ++ pr_aux c ++ spc() ++ pr_id id ++ str"}"
	| CMeasureRec (m,r) ->
	  spc() ++ str "{measure " ++ pr_aux m ++ spc() ++ pr_id id++
	    (match r with None -> mt() | Some r -> str" on " ++ pr_aux r) ++ str"}"

let pr_fixdecl pr prd dangling_with_for ((_,id),ro,bl,t,c) =
  let annot = pr_guard_annot (pr lsimple) bl ro in
    pr_recursive_decl pr prd dangling_with_for id bl annot t c

let pr_cofixdecl pr prd dangling_with_for ((_,id),bl,t,c) =
  pr_recursive_decl pr prd dangling_with_for id bl (mt()) t c

let pr_recursive pr_decl id = function
  | [] -> anomaly "(co)fixpoint with no definition"
  | [d1] -> pr_decl false d1
  | dl ->
      prlist_with_sep (fun () -> fnl() ++ str "with ")
        (pr_decl true) dl ++
      fnl() ++ str "for " ++ pr_id id

let pr_asin pr (na,indnalopt) =
  (match na with (* Decision of printing "_" or not moved to constrextern.ml *)
    | Some na -> spc () ++ str "as " ++  pr_lname na
    | None -> mt ()) ++
  (match indnalopt with
    | None -> mt ()
    | Some t -> spc () ++ str "in " ++ pr_patt lsimple t)

let pr_case_item pr (tm,asin) =
  hov 0 (pr (lcast,E) tm ++ pr_asin pr asin)

let pr_case_type pr po =
  match po with
    | None | Some (CHole _) -> mt()
    | Some p ->
        spc() ++ hov 2 (str "return" ++ pr_sep_com spc (pr lsimple) p)

let pr_simple_return_type pr na po =
  (match na with
    | Some (_,Name id) ->
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

let pr_forall () = str"forall" ++ spc ()

let pr_fun () = str"fun" ++ spc ()

let pr_fun_sep = str " =>"


let pr_dangling_with_for sep pr inherited a =
  match a with
  | (CFix (_,_,[_])|CCoFix(_,_,[_])) -> pr sep (latom,E) a
  | _ -> pr sep inherited a

let pr pr sep inherited a =
  let (strm,prec) = match a with
  | CRef r -> pr_reference r, latom
  | CFix (_,id,fix) ->
      hov 0 (str"fix " ++
             pr_recursive
               (pr_fixdecl (pr mt) (pr_dangling_with_for mt pr)) (snd id) fix),
      lfix
  | CCoFix (_,id,cofix) ->
      hov 0 (str "cofix " ++
             pr_recursive
              (pr_cofixdecl (pr mt) (pr_dangling_with_for mt pr)) (snd id) cofix),
      lfix
  | CProdN _ ->
      let (bl,a) = extract_prod_binders a in
      hov 0 (
	hov 2 (pr_delimited_binders pr_forall spc
                 (pr mt ltop) bl) ++
        str "," ++ pr spc ltop a),
      lprod
  | CLambdaN _ ->
      let (bl,a) = extract_lam_binders a in
      hov 0 (
        hov 2 (pr_delimited_binders pr_fun spc
                (pr mt ltop) bl) ++
	       pr_fun_sep ++ pr spc ltop a),
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
  | CRecord (_,w,l) ->
      let beg =
	match w with
	| None -> spc ()
	| Some t -> spc () ++ pr spc ltop t ++ spc () ++ str"with" ++ spc ()
      in
	hv 0 (str"{|" ++ beg ++
	      prlist_with_sep pr_semicolon
		(fun (id, c) -> h 1 (pr_reference id ++ spc () ++ str":=" ++ pr spc ltop c)) l
	      ++ str" |}"), latom

  | CCases (_,LetPatternStyle,rtntypopt,[c,asin],[(_,[(loc,[p])],b)]) ->
      hv 0 (
	str "let '" ++
	  hov 0 (pr_patt ltop p ++
		 pr_asin (pr_dangling_with_for mt pr) asin ++
		 str " :=" ++ pr spc ltop c ++
		 pr_case_type (pr_dangling_with_for mt pr) rtntypopt ++
		 str " in" ++ pr spc ltop b)),
	lletpattern
  | CCases(_,_,rtntypopt,c,eqns) ->
      v 0
        (hv 0 (str "match" ++ brk (1,2) ++
		  hov 0 (
		    prlist_with_sep sep_v
		      (pr_case_item (pr_dangling_with_for mt pr)) c
		    ++ pr_case_type (pr_dangling_with_for mt pr) rtntypopt) ++
		  spc () ++ str "with") ++
		  prlist (pr_eqn (pr mt)) eqns ++ spc() ++ str "end"),
      latom
  | CLetTuple (_,nal,(na,po),c,b) ->
      hv 0 (
        str "let " ++
	hov 0 (str "(" ++
               prlist_with_sep sep_v pr_lname nal ++
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
  | CEvar (_,n,l) -> pr_evar (pr mt) n l, latom
  | CPatVar (_,(_,p)) -> str "?" ++ pr_patvar p, latom
  | CSort (_,s) -> pr_glob_sort s, latom
  | CCast (_,a,CastConv (k,b)) ->
      let s = match k with VMcast -> "<:" | DEFAULTcast | REVERTcast -> ":" in
      hv 0 (pr mt (lcast,L) a ++ cut () ++ str s ++ pr mt (-lcast,E) b),
      lcast
  | CCast (_,a,CastCoerce) ->
      hv 0 (pr mt (lcast,L) a ++ cut () ++ str ":>"),
      lcast
  | CNotation (_,"( _ )",([t],[],[])) ->
      pr (fun()->str"(") (max_int,L) t ++ str")", latom
  | CNotation (_,s,env) ->
      pr_notation (pr mt) (pr_binders_gen (pr mt ltop)) s env
  | CGeneralization (_,bk,ak,c) -> pr_generalization bk ak (pr mt lsimple c), latom
  | CPrim (_,p) -> pr_prim_token p, prec_of_prim_token p
  | CDelimiters (_,sc,a) -> pr_delimiters sc (pr mt lsimple a), 1
  in
  let loc = constr_loc a in
  pr_with_comments loc
    (sep() ++ if prec_less prec inherited then strm else surround strm)

type term_pr = {
  pr_constr_expr   : constr_expr -> std_ppcmds;
  pr_lconstr_expr  : constr_expr -> std_ppcmds;
  pr_constr_pattern_expr  : constr_pattern_expr -> std_ppcmds;
  pr_lconstr_pattern_expr : constr_pattern_expr -> std_ppcmds
}

type precedence =  Ppextend.precedence * Ppextend.parenRelation
let modular_constr_pr = pr
let rec fix rf x =rf (fix rf) x
let pr = fix modular_constr_pr mt

let default_term_pr = {
  pr_constr_expr   = pr lsimple;
  pr_lconstr_expr  = pr ltop;
  pr_constr_pattern_expr  = pr lsimple;
  pr_lconstr_pattern_expr = pr ltop
}

let term_pr = ref default_term_pr

let set_term_pr = (:=) term_pr

let pr_constr_expr c   = !term_pr.pr_constr_expr   c
let pr_lconstr_expr c  = !term_pr.pr_lconstr_expr  c
let pr_constr_pattern_expr c  = !term_pr.pr_constr_pattern_expr  c
let pr_lconstr_pattern_expr c = !term_pr.pr_lconstr_pattern_expr c

let pr_cases_pattern_expr = pr_patt ltop

let pr_binders = pr_undelimited_binders spc (pr ltop)

let pr_with_occurrences pr occs =
  match occs with
    ((false,[]),c) -> pr c
  | ((nowhere_except_in,nl),c) ->
      hov 1 (pr c ++ spc() ++ str"at " ++
        (if nowhere_except_in then mt() else str "- ") ++
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

let pr_red_expr (pr_constr,pr_lconstr,pr_ref,pr_pattern) = function
  | Red false -> str "red"
  | Hnf -> str "hnf"
  | Simpl o -> str "simpl" ++ pr_opt (pr_with_occurrences pr_pattern) o
  | Cbv f ->
      if f = {rBeta=true;rIota=true;rZeta=true;rDelta=true;rConst=[]} then
	str "compute"
      else
	hov 1 (str "cbv" ++ pr_red_flag pr_ref f)
  | Lazy f ->
      hov 1 (str "lazy" ++ pr_red_flag pr_ref f)
  | Unfold l ->
      hov 1 (str "unfold" ++ spc() ++
             prlist_with_sep pr_comma (pr_with_occurrences pr_ref) l)
  | Fold l -> hov 1 (str "fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l ->
      hov 1 (str "pattern" ++
        pr_arg (prlist_with_sep pr_comma (pr_with_occurrences pr_constr)) l)

  | Red true -> error "Shouldn't be accessible from user."
  | ExtraRedExpr s -> str s
  | CbvVm o -> str "vm_compute" ++ pr_opt (pr_with_occurrences pr_pattern) o

let rec pr_may_eval test prc prlc pr2 pr3 = function
  | ConstrEval (r,c) ->
      hov 0
        (str "eval" ++ brk (1,1) ++
         pr_red_expr (prc,prlc,pr2,pr3) r ++
	 str " in" ++ spc() ++ prc c)
  | ConstrContext ((_,id),c) ->
      hov 0
	(str "context " ++ pr_id id ++ spc () ++
	 str "[" ++ prlc c ++ str "]")
  | ConstrTypeOf c -> hov 1 (str "type of" ++ spc() ++ prc c)
  | ConstrTerm c when test c -> h 0 (str "(" ++ prc c ++ str ")")
  | ConstrTerm c -> prc c

let pr_may_eval a = pr_may_eval (fun _ -> false) a
