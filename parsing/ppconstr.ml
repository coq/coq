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

let latom = 0
let lannot = 1
let lprod = 8 (* not 1 because the scope extends to 8 on the right *)
let llambda = 8 (* not 1 *)
let lif = 8 (* not 1 *)
let lletin = 8 (* not 1 *)
let lcases = 1
let larrow = 8
let lcast = 9
let lapp = 10
let ltop = (8,E)

let prec_less child (parent,assoc) = match assoc with
  | E -> child <= parent
  | L -> child < parent
  | Prec n -> child <= n
  | Any -> true

let env_assoc_value v env =
  try List.nth env (v-1)
  with Not_found -> anomaly "Inconsistent environment for pretty-print rule"

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
  let left = "'"^key^":" and right = "'" in
  let lspace =
    if is_letter (left.[String.length left -1]) then str " " else mt () in
  let rspace =
    let c = right.[0] in
    if is_letter c or is_digit c or c = '\'' then str " " else mt () in
  str left ++ lspace ++ strm ++ rspace ++ str right

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
  | Some (_,ExplByPos n) -> int n ++ str "!"
  | Some (_,ExplByName n) -> anomaly "Argument made explicit by name"

let pr_expl_args pr (a,expl) =
  pr_explicitation expl ++ pr (lapp,L) a

let pr_opt_type pr = function
  | CHole _ -> mt ()
  | t -> str ":" ++ pr ltop t

let pr_tight_coma () = str "," ++ cut ()

let pr_name = function
  | Anonymous -> str "_"
  | Name id -> pr_id id

let pr_located pr (loc,x) = pr x

let pr_let_binder pr x a =
  hov 0 (hov 0 (pr_name x ++ brk(0,1) ++ str ":=") ++ brk(0,1) ++ pr ltop a)

let pr_binder pr (nal,t) =
  hov 0 (
    prlist_with_sep pr_tight_coma (pr_located pr_name) nal ++
    pr_opt_type pr t)

let pr_binders pr bl =
  hv 0 (prlist_with_sep pr_semicolon (pr_binder pr) bl)

let pr_local_binder pr = function
    LocalRawAssum(nal,t) -> pr_binder pr (nal,t)
  | LocalRawDef((_,na),t) -> pr_let_binder pr na t

let pr_local_binders pr bl =
  hv 0 (prlist_with_sep pr_semicolon (pr_local_binder pr) bl)

let pr_global vars ref = pr_global_env vars ref

let rec pr_lambda_tail pr bll = function
  | CLambdaN (_,bl,a) ->
      pr_lambda_tail pr (bll ++ pr_semicolon() ++ pr_binders pr bl) a
  | CLetIn (_,x,a,b) ->
      pr_lambda_tail pr (bll ++ pr_semicolon() ++ pr_let_binder pr (snd x) a) b
  | a ->
      bll, pr ltop a

let rec pr_prod_tail pr bll = function
  | CProdN (_,bl,a) ->
      pr_prod_tail pr (bll ++ pr_semicolon () ++ pr_binders pr bl) a
  | a -> bll, pr ltop a

let pr_recursive_decl pr id binders t c =
  pr_id id ++ binders ++
  brk (1,2) ++ str ": " ++ pr ltop t ++ str " :=" ++
  brk (1,2) ++ pr ltop c

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

let concat_binder na t = function
  | [] -> [[na],t]
  | (nal,u)::bl' as bl -> if t=u then (na::nal,t)::bl' else ([na],t)::bl

let rec split_fix n typ def =
  if n = 0 then ([],typ,def)
  else
    let (na,_,def) = split_lambda def in
    let (_,t,typ) = split_product typ in
    let (bl,typ,def) = split_fix (n-1) typ def in
    (concat_binder na t bl,typ,def)

let pr_fixdecl pr (id,n,bl,t,c) =
  pr_recursive_decl pr id 
    (brk (1,2) ++ str "[" ++ pr_local_binders pr bl ++ str "]") t c

let pr_cofixdecl pr (id,bl,t,c) =
  let  b =
    if bl=[] then mt() else
      brk(1,2) ++ str"[" ++ pr_local_binders pr bl ++ str "]" in
  pr_recursive_decl pr id b t c

let pr_recursive fix pr_decl id = function
  | [] -> anomaly "(co)fixpoint with no definition"
  | d1::dl ->
      hov 0 (
	str fix ++ spc () ++ pr_id id ++ brk (1,2) ++ str "{" ++
	(v 0 (
	  (hov 0 (pr_decl d1)) ++
	  (prlist (fun fix -> fnl () ++ hov 0 (str "with" ++ pr_decl fix))
	    dl))) ++
	str "}")

let pr_fix pr = pr_recursive "Fix" (pr_fixdecl pr)
let pr_cofix pr = pr_recursive "CoFix" (pr_cofixdecl pr)

let rec pr_arrow pr = function
  | CArrow (_,a,b) -> pr (larrow,L) a ++ cut () ++ str "->" ++ pr_arrow pr b
  | a -> pr (larrow,E) a

let pr_annotation pr = function
  | None -> mt ()
  | Some t -> str "<" ++ pr ltop t ++ str ">" ++ brk (0,2)

let rec pr_cases_pattern _inh = function
  | CPatAlias (_,p,x) ->
      pr_cases_pattern _inh p ++ spc () ++ str "as" ++ spc () ++ pr_id x
  | CPatCstr (_,c,[]) -> pr_reference c
  | CPatCstr (_,c,pl) ->
      hov 0 (
	str "(" ++ pr_reference c ++ spc () ++ 
	prlist_with_sep spc (pr_cases_pattern _inh) pl ++ str ")")
  | CPatAtom (_,Some c) -> pr_reference c
  | CPatAtom (_,None) -> str "_"
  | CPatNotation (_,"( _ )",[p]) ->
      str"("++ pr_cases_pattern _inh p ++ str")"
  | CPatNotation (_,s,env) -> fst (pr_patnotation pr_cases_pattern s env)
  | CPatNumeral (_,n) -> Bignat.pr_bigint n
  | CPatDelimiters (_,key,p) -> pr_delimiters key (pr_cases_pattern _inh p)

let pr_cases_pattern = pr_cases_pattern (0,E) (* level unused *)

let pr_eqn pr (_,patl,rhs) =
  hov 0 (
    prlist_with_sep spc pr_cases_pattern patl ++ spc () ++
    str "=>" ++
    brk (1,1) ++ pr ltop rhs) ++ spc ()

let pr_cases pr (po,_) tml eqns =
  hov 0 (
    pr_annotation pr po ++
    hv 0 (
      hv 0 (
	str "Cases" ++ brk (1,2) ++
	prlist_with_sep spc (fun (tm,_) -> pr ltop tm) tml ++ spc() ++ str "of") ++ brk(1,2) ++
      prlist_with_sep (fun () -> str "| ") (pr_eqn pr) eqns ++
      str "end"))

let pr_proj pr pr_app a f l =
  hov 0 (pr (latom,E) a ++ cut() ++ str ".(" ++ pr_app pr f l ++ str ")")

let pr_explapp pr f l =
  hov 0 (
    str "!" ++ pr_reference f ++ 
    prlist (fun a -> brk (1,1) ++ pr (lapp,L) a) l)

let pr_app pr a l =
  hov 0 (
    pr (lapp,L) a ++ 
    prlist (fun a -> brk (1,1) ++ pr_expl_args pr a) l)

let rec pr inherited a =
  let (strm,prec) = match a with
  | CRef r -> pr_reference r, latom
  | CFix (_,id,fix) -> pr_fix pr (snd id) fix, latom
  | CCoFix (_,id,cofix) -> pr_cofix pr (snd id) cofix, latom
  | CArrow _ -> hv 0 (pr_arrow pr a), larrow
  | CProdN (_,bl,a) ->
      let bll, a = pr_prod_tail pr (mt()) a in
      hv 1 (
	hv 1 (str "(" ++ pr_binders pr bl ++ bll ++ str ")") ++
	brk (0,1) ++ a), lprod
  | CLambdaN (_,bl,a) ->
      let bll, a = pr_lambda_tail pr (mt()) a in
      hv 1 (
	hv 1 (str "[" ++ pr_binders pr bl ++ bll ++ str "]") ++
      brk (0,1) ++ a), llambda
  | CLetIn (_,x,a,b) ->
      let bll, b = pr_lambda_tail pr (mt()) b in
      hv 1 (
	hv 1 (str "[" ++ pr_let_binder pr (snd x) a ++ bll ++ str "]") ++
	brk (0,1) ++ b), lletin
  | CAppExpl (_,((* V7 don't know about projections *)_,f),l) ->
      pr_explapp pr f l, lapp
  | CApp (_,(_,a),l) ->
      pr_app pr a l, lapp
  | CCases (_,po,tml,eqns) ->
      pr_cases pr po tml eqns, lcases
  | COrderedCase (_,IfStyle,po,c,[b1;b2]) ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
	 parsing est lui plus tolérant) *)
      hov 0 (
	pr_annotation pr po ++
	hv 0 (
	  str "if " ++ pr ltop c ++ spc () ++
	  hov 0 (str "then" ++ brk (1,1) ++ pr ltop b1) ++ spc () ++
	  hov 0 (str "else" ++ brk (1,1) ++ pr ltop b2))), lif
  | CLetTuple _ | CIf _ ->
      error "Let tuple not supported in v7"

  | COrderedCase (_,(MatchStyle|RegularStyle as style),po,c,bl) ->
      hov 0 (
	hov 0 (
	pr_annotation pr po ++
	  hov 0 (
	    str (if style=RegularStyle then "Case" else "Match") ++ 
	    brk (1,1) ++ pr ltop c ++ spc () ++
	    str (if style=RegularStyle then "of" else "with") ++
	    brk (1,3) ++
	    fnl () ++ hov 0 (prlist (fun b -> pr ltop b ++ fnl ()) bl) ++
	    str "end"))), lcases
  | COrderedCase (_,_,_,_,_) -> 
      anomaly "malformed if or destructuring let"
  | CHole _ -> str "?", latom
(*
  | CEvar (_,n) -> str "?" ++ int n, latom
*)
  | CEvar (_,n) -> str (Evd.string_of_existential n), latom
  | CPatVar (_,(_,p)) -> str "?" ++ pr_patvar p, latom
  | CSort (_,s) -> pr_sort s, latom
  | CCast (_,a,b) ->
      hv 0 (pr (lcast,L) a ++ cut () ++ str "::" ++ pr (lcast,E) b), lcast
  | CNotation (_,"( _ )",[t]) ->
      str"("++ pr (max_int,E) t ++ str")", latom
  | CNotation (_,s,env) -> pr_notation pr s env
  | CNumeral (_,p) -> Bignat.pr_bigint p, latom
  | CDelimiters (_,sc,a) -> pr_delimiters sc (pr ltop a), latom
  | CDynamic _ -> str "<dynamic>", latom
  in
  if prec_less prec inherited then strm
  else str"(" ++ strm ++ str")"
  
let pr_constr = pr ltop

let pr_pattern = pr_constr

let pr_qualid qid = str (string_of_qualid qid)

open Rawterm

let pr_arg pr x = spc () ++ pr x

let pr_red_flag pr r =
  (if r.rBeta then pr_arg str "Beta" else mt ()) ++
  (if r.rIota then pr_arg str "Iota" else mt ()) ++
  (if r.rZeta then pr_arg str "Zeta" else mt ()) ++
  (if r.rConst = [] then
     if r.rDelta then pr_arg str "Delta"
     else mt ()
   else
     pr_arg str "Delta" ++ (if r.rDelta then str "-" else mt ()) ++
     hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]"))

open Genarg

let pr_occurrences prc (nl,c) = prlist (fun n -> int n ++ spc ()) nl ++ prc c

let pr_red_expr (pr_constr,pr_ref) = function
  | Red false -> str "Red"
  | Hnf -> str "Hnf"
  | Simpl o -> str "Simpl" ++ pr_opt (pr_occurrences pr_constr) o
  | Cbv f ->
      if f = {rBeta=true;rIota=true;rZeta=true;rDelta=true;rConst=[]} then
	str "Compute"
      else
	hov 1 (str "Cbv" ++ spc () ++ pr_red_flag pr_ref f)
  | Lazy f -> 
      hov 1 (str "Lazy" ++ spc () ++ pr_red_flag pr_ref f)
  | Unfold l ->
      hov 1 (str "Unfold" ++
        prlist (fun (nl,qid) ->
	  prlist (pr_arg int) nl ++ spc () ++ pr_ref qid) l)
  | Fold l -> hov 1 (str "Fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l -> hov 1 (str "Pattern " ++ prlist (pr_occurrences pr_constr) l)
  | Red true -> error "Shouldn't be accessible from user"
  | ExtraRedExpr (s,c) ->
      hov 1 (str s ++ pr_arg pr_constr c)

let rec pr_may_eval pr pr2 = function
  | ConstrEval (r,c) ->
      hov 0
        (str "Eval" ++ brk (1,1) ++ pr_red_expr (pr,pr2) r ++
	 spc () ++ str "in" ++ brk (1,1) ++ pr c)
  | ConstrContext ((_,id),c) ->
      hov 0
	(str "Inst " ++ brk (1,1) ++ pr_id id ++ spc () ++
	 str "[" ++ pr c ++ str "]")
  | ConstrTypeOf c -> hov 0 (str "Check " ++ brk (1,1) ++ pr c)
  | ConstrTerm c -> pr c

let pr_rawconstr c = pr_constr (Constrextern.extern_rawconstr Idset.empty c)
