(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Libnames
open Q_util

let is_meta s = String.length s > 0 && s.[0] == '$'

let purge_str s =
  if String.length s == 0 || s.[0] <> '$' then s
  else String.sub s 1 (String.length s - 1)

let anti loc x =
  let e =
    let loc = unloc loc in
    let loc = make_loc (1, snd loc - fst loc) in <:expr< $lid:purge_str x$ >>
  in
  <:expr< $anti:e$ >>

(* [mlexpr_of_ast] contributes to translate g_*.ml4 files into g_*.ppo *)
(* This is where $id's (and macros) in ast are translated in ML variables *)
(* which will bind their actual ast value *)

let rec mlexpr_of_ast = function
  | Coqast.Nmeta (loc, id) -> anti loc id
  | Coqast.Id (loc, id) when is_meta id -> <:expr< Coqast.Id loc $anti loc id$ >>
  | Coqast.Node (_, "$VAR", [Coqast.Nmeta (loc, x)]) ->
      <:expr< let s = $anti loc x$ in
      if String.length s > 0 && String.sub s 0 1 = "$" then
	failwith "Wrong ast: $VAR should not be bound to a meta variable"
      else
	Coqast.Nvar loc (Names.id_of_string s) >>
  | Coqast.Node (_, "$PATH", [Coqast.Nmeta (loc, x)]) ->
      <:expr< Coqast.Path loc $anti loc x$ >>
  | Coqast.Node (_, "$ID", [Coqast.Nmeta (loc, x)]) ->
      <:expr< Coqast.Id loc $anti loc x$ >>
  | Coqast.Node (_, "$STR", [Coqast.Nmeta (loc, x)]) ->
      <:expr< Coqast.Str loc $anti loc x$ >>
(* Obsolète
  | Coqast.Node _ "$SLAM" [Coqast.Nmeta loc idl; y] ->
      <:expr<
      List.fold_right (Pcoq.slam_ast loc) $anti loc idl$ $mlexpr_of_ast y$ >>
*)
  | Coqast.Node (loc, "$ABSTRACT", [Coqast.Str (_, s); x; y]) ->
      let x = mlexpr_of_ast x in
      let y = mlexpr_of_ast y in
      <:expr< Ast.abstract_binders_ast loc $str:s$ $x$ $y$ >>
  | Coqast.Node (loc, nn, al) ->
      let e = expr_list_of_ast_list al in
      <:expr< Coqast.Node loc $str:nn$ $e$ >>
  | Coqast.Nvar (loc, id) ->
      <:expr< Coqast.Nvar loc (Names.id_of_string $str:Names.string_of_id id$) >>
  | Coqast.Slam (loc, None, a) ->
      <:expr< Coqast.Slam loc None $mlexpr_of_ast a$ >>
  | Coqast.Smetalam (loc, s, a) ->
      <:expr< 
      match $anti loc s$ with
	[ Coqast.Nvar _ id -> Coqast.Slam loc (Some id) $mlexpr_of_ast a$
	| Coqast.Nmeta _ s -> Coqast.Smetalam loc s $mlexpr_of_ast a$
	| _ -> failwith "Slam expects a var or a metavar" ] >>
  | Coqast.Slam (loc, Some s, a) ->
      let se = <:expr< Names.id_of_string $str:Names.string_of_id s$ >> in
      <:expr< Coqast.Slam loc (Some $se$) $mlexpr_of_ast a$ >>
  | Coqast.Num (loc, i) -> <:expr< Coqast.Num loc $int:string_of_int i$ >>
  | Coqast.Id (loc, id) -> <:expr< Coqast.Id loc $str:id$ >>
  | Coqast.Str (loc, str) -> <:expr< Coqast.Str loc $str:str$ >>
  | Coqast.Path (loc, kn) ->
      let l,a = Libnames.decode_kn kn in
      let mlexpr_of_modid id =
	<:expr< Names.id_of_string $str:string_of_id id$ >> in
      let e = List.map mlexpr_of_modid (repr_dirpath l) in
      let e = expr_list_of_var_list e in
      <:expr< Coqast.Path loc (Libnames.encode_kn (Names.make_dirpath $e$)
                (Names.id_of_string $str:Names.string_of_id a$)) >> 
  | Coqast.Dynamic (_, _) ->
      failwith "Q_Coqast: dynamic: not implemented"

and expr_list_of_ast_list al =
  List.fold_right
    (fun a e2 -> match a with
       | (Coqast.Node (_, "$LIST", [Coqast.Nmeta (locv, pv)])) ->
           let e1 = anti locv pv in
           let loc = (fst(MLast.loc_of_expr e1), snd(MLast.loc_of_expr e2)) in
	     if e2 = (let loc = dummy_loc in <:expr< [] >>)
	     then <:expr< $e1$ >>
	     else <:expr< ( $lid:"@"$ $e1$ $e2$) >>
       | _ ->
           let e1 = mlexpr_of_ast a in
           let loc = (fst(MLast.loc_of_expr e1), snd(MLast.loc_of_expr e2)) in
	   <:expr< [$e1$ :: $e2$] >> )
    al (let loc = dummy_loc in <:expr< [] >>)

and expr_list_of_var_list sl =
  let loc = dummy_loc in
  List.fold_right
    (fun e1 e2 ->
       let loc = (fst (MLast.loc_of_expr e1), snd (MLast.loc_of_expr e2)) in
       <:expr< [$e1$ :: $e2$] >>)
    sl <:expr< [] >>

(* We don't give location for tactic quotation! *)
let loc = dummy_loc

let dloc = <:expr< Util.dummy_loc >>

let mlexpr_of_ident id =
  <:expr< Names.id_of_string $str:Names.string_of_id id$ >>

let mlexpr_of_name = function
  | Names.Anonymous -> <:expr< Names.Anonymous >>
  | Names.Name id -> 
      <:expr< Names.Name (Names.id_of_string $str:Names.string_of_id id$) >>

let mlexpr_of_dirpath dir =
  let l = Names.repr_dirpath dir in
  <:expr< Names.make_dirpath $mlexpr_of_list mlexpr_of_ident l$ >>

let mlexpr_of_qualid qid =
  let (dir, id) = repr_qualid qid in
  <:expr< make_qualid $mlexpr_of_dirpath dir$ $mlexpr_of_ident id$ >>

let mlexpr_of_reference = function
  | Libnames.Qualid (loc,qid) -> <:expr< Libnames.Qualid $dloc$ $mlexpr_of_qualid qid$ >>
  | Libnames.Ident (loc,id) -> <:expr< Libnames.Ident $dloc$ $mlexpr_of_ident id$ >>

let mlexpr_of_intro_pattern = function
  | Genarg.IntroOrAndPattern _ -> failwith "mlexpr_of_intro_pattern: TODO"
  | Genarg.IntroWildcard -> <:expr< Genarg.IntroWildcard >>
  | Genarg.IntroIdentifier id ->
      <:expr< Genarg.IntroIdentifier (mlexpr_of_ident $dloc$ id) >>

let mlexpr_of_ident_option = mlexpr_of_option (mlexpr_of_ident)

let mlexpr_of_or_metaid f = function
  | Tacexpr.AI a -> <:expr< Tacexpr.AI $f a$ >>
  | Tacexpr.MetaId (_,id) -> <:expr< Tacexpr.AI $anti loc id$ >>

let mlexpr_of_quantified_hypothesis = function
  | Rawterm.AnonHyp n -> <:expr< Rawterm.AnonHyp $mlexpr_of_int n$ >>
  | Rawterm.NamedHyp id ->  <:expr< Rawterm.NamedHyp $mlexpr_of_ident id$ >>

let mlexpr_of_located f (loc,x) = <:expr< ($dloc$, $f x$) >>

let mlexpr_of_loc loc = <:expr< $dloc$ >>

let mlexpr_of_or_var f = function
  | Genarg.ArgArg x -> <:expr< Genarg.ArgArg $f x$ >>
  | Genarg.ArgVar id -> <:expr< Genarg.ArgVar $mlexpr_of_located mlexpr_of_ident id$ >>

let mlexpr_of_hyp = mlexpr_of_or_metaid (mlexpr_of_located mlexpr_of_ident)

let mlexpr_of_occs = mlexpr_of_list mlexpr_of_int

let mlexpr_of_hyp_location = function
  | id, occs, (Tacexpr.InHyp,_) ->
      <:expr< ($mlexpr_of_hyp id$, $mlexpr_of_occs occs$, (Tacexpr.InHyp, ref None)) >>
  | id, occs, (Tacexpr.InHypTypeOnly,_) ->
      <:expr< ($mlexpr_of_hyp id$, $mlexpr_of_occs occs$, (Tacexpr.InHypTypeOnly, ref None)) >>
  | id, occs, (Tacexpr.InHypValueOnly,_) ->
      <:expr< ($mlexpr_of_hyp id$, $mlexpr_of_occs occs$, (Tacexpr.InHypValueOnly,ref None)) >>

let mlexpr_of_clause cl =
  <:expr< {Tacexpr.onhyps=
             $mlexpr_of_option (mlexpr_of_list mlexpr_of_hyp_location)
               cl.Tacexpr.onhyps$;
           Tacexpr.onconcl= $mlexpr_of_bool cl.Tacexpr.onconcl$;
           Tacexpr.concl_occs= $mlexpr_of_occs cl.Tacexpr.concl_occs$} >>

(*
let mlexpr_of_red_mode = function
  | Closure.UNIFORM -> <:expr< Closure.UNIFORM >>
  | Closure.SIMPL -> <:expr< Closure.SIMPL >>
  | Closure.WITHBACK -> <:expr< Closure.WITHBACK >>
*)

let mlexpr_of_red_flags {
  Rawterm.rBeta = bb;
  Rawterm.rIota = bi;
  Rawterm.rZeta = bz;
  Rawterm.rDelta = bd;
  Rawterm.rConst = l
} = <:expr< {
  Rawterm.rBeta = $mlexpr_of_bool bb$;
  Rawterm.rIota = $mlexpr_of_bool bi$;
  Rawterm.rZeta = $mlexpr_of_bool bz$;
  Rawterm.rDelta = $mlexpr_of_bool bd$;
  Rawterm.rConst = $mlexpr_of_list mlexpr_of_reference l$
} >>

let mlexpr_of_explicitation = function
  | Topconstr.ExplByName id -> <:expr< Topconstr.ExplByName $mlexpr_of_ident id$ >>
  | Topconstr.ExplByPos n -> <:expr< Topconstr.ExplByPos $mlexpr_of_int n$ >>
 
let rec mlexpr_of_constr = function
  | Topconstr.CRef (Libnames.Ident (loc,id)) when is_meta (string_of_id id) ->
      anti loc (string_of_id id)
  | Topconstr.CRef r -> <:expr< Topconstr.CRef $mlexpr_of_reference r$ >>
  | Topconstr.CFix (loc,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Topconstr.CCoFix (loc,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Topconstr.CArrow (loc,a,b) ->
  <:expr< Topconstr.CArrow $dloc$ $mlexpr_of_constr a$ $mlexpr_of_constr b$ >>
  | Topconstr.CProdN (loc,l,a) -> <:expr< Topconstr.CProdN $dloc$ $mlexpr_of_list (mlexpr_of_pair (mlexpr_of_list (mlexpr_of_pair (fun _ -> dloc) mlexpr_of_name)) mlexpr_of_constr) l$ $mlexpr_of_constr a$ >>
  | Topconstr.CLambdaN (loc,l,a) -> <:expr< Topconstr.CLambdaN $dloc$ $mlexpr_of_list (mlexpr_of_pair (mlexpr_of_list (mlexpr_of_pair (fun _ -> dloc) mlexpr_of_name)) mlexpr_of_constr) l$ $mlexpr_of_constr a$ >>
  | Topconstr.CLetIn (loc,_,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Topconstr.CAppExpl (loc,a,l) -> <:expr< Topconstr.CAppExpl $dloc$ $mlexpr_of_pair (mlexpr_of_option mlexpr_of_int) mlexpr_of_reference a$ $mlexpr_of_list mlexpr_of_constr l$ >>
  | Topconstr.CApp (loc,a,l) -> <:expr< Topconstr.CApp $dloc$ $mlexpr_of_pair (mlexpr_of_option mlexpr_of_int) mlexpr_of_constr a$ $mlexpr_of_list (mlexpr_of_pair mlexpr_of_constr (mlexpr_of_option (mlexpr_of_located mlexpr_of_explicitation))) l$ >>
  | Topconstr.CCases (loc,_,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Topconstr.COrderedCase (loc,_,_,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Topconstr.CHole loc -> <:expr< Topconstr.CHole $dloc$ >>
  | Topconstr.CNotation(_,ntn,l) ->
      <:expr< Topconstr.CNotation $dloc$ $mlexpr_of_string ntn$
                $mlexpr_of_list mlexpr_of_constr l$ >>
  | Topconstr.CPatVar (loc,n) -> 
      <:expr< Topconstr.CPatVar $dloc$ $mlexpr_of_pair mlexpr_of_bool mlexpr_of_ident n$ >>
  | _ -> failwith "mlexpr_of_constr: TODO"

let mlexpr_of_occ_constr =
  mlexpr_of_pair (mlexpr_of_list mlexpr_of_int) mlexpr_of_constr

let mlexpr_of_red_expr = function
  | Rawterm.Red b -> <:expr< Rawterm.Red $mlexpr_of_bool b$ >>
  | Rawterm.Hnf -> <:expr< Rawterm.Hnf >>
  | Rawterm.Simpl o -> <:expr< Rawterm.Simpl $mlexpr_of_option mlexpr_of_occ_constr o$ >>
  | Rawterm.Cbv f ->
      <:expr< Rawterm.Cbv $mlexpr_of_red_flags f$ >>
  | Rawterm.Lazy f ->
      <:expr< Rawterm.Lazy $mlexpr_of_red_flags f$ >>
  | Rawterm.Unfold l ->
      let f1 = mlexpr_of_list mlexpr_of_int in
      let f2 = mlexpr_of_reference in
      let f = mlexpr_of_list (mlexpr_of_pair f1 f2) in
      <:expr< Rawterm.Unfold $f l$ >>
  | Rawterm.Fold l ->
      <:expr< Rawterm.Fold $mlexpr_of_list mlexpr_of_constr l$ >>
  | Rawterm.Pattern l ->
      let f = mlexpr_of_list mlexpr_of_occ_constr in
      <:expr< Rawterm.Pattern $f l$ >>
  | Rawterm.ExtraRedExpr (s,c) ->
      let l = mlexpr_of_constr c in
      <:expr< Rawterm.ExtraRedExpr $mlexpr_of_string s$ $l$ >>

let rec mlexpr_of_argtype loc = function
  | Genarg.BoolArgType -> <:expr< Genarg.BoolArgType >>
  | Genarg.IntArgType -> <:expr< Genarg.IntArgType >>
  | Genarg.IntOrVarArgType -> <:expr< Genarg.IntOrVarArgType >>
  | Genarg.RefArgType -> <:expr< Genarg.RefArgType >>
  | Genarg.PreIdentArgType -> <:expr< Genarg.PreIdentArgType >>
  | Genarg.IntroPatternArgType -> <:expr< Genarg.IntroPatternArgType >>
  | Genarg.IdentArgType -> <:expr< Genarg.IdentArgType >>
  | Genarg.HypArgType -> <:expr< Genarg.HypArgType >>
  | Genarg.StringArgType -> <:expr< Genarg.StringArgType >>
  | Genarg.QuantHypArgType -> <:expr< Genarg.QuantHypArgType >>
  | Genarg.CastedOpenConstrArgType -> <:expr< Genarg.CastedOpenConstrArgType >>
  | Genarg.ConstrWithBindingsArgType -> <:expr< Genarg.ConstrWithBindingsArgType >>
  | Genarg.BindingsArgType -> <:expr< Genarg.BindingsArgType >>
  | Genarg.RedExprArgType -> <:expr< Genarg.RedExprArgType >>
  | Genarg.TacticArgType -> <:expr< Genarg.TacticArgType >>
  | Genarg.SortArgType -> <:expr< Genarg.SortArgType >>
  | Genarg.ConstrArgType -> <:expr< Genarg.ConstrArgType >>
  | Genarg.ConstrMayEvalArgType -> <:expr< Genarg.ConstrMayEvalArgType >>
  | Genarg.List0ArgType t -> <:expr< Genarg.List0ArgType $mlexpr_of_argtype loc t$ >>
  | Genarg.List1ArgType t -> <:expr< Genarg.List1ArgType $mlexpr_of_argtype loc t$ >>
  | Genarg.OptArgType t -> <:expr< Genarg.OptArgType $mlexpr_of_argtype loc t$ >>
  | Genarg.PairArgType (t1,t2) -> 
      let t1 = mlexpr_of_argtype loc t1 in
      let t2 = mlexpr_of_argtype loc t2 in
      <:expr< Genarg.PairArgType $t1$ $t2$ >>
  | Genarg.ExtraArgType s -> <:expr< Genarg.ExtraArgType $str:s$ >>

let rec mlexpr_of_may_eval f = function
  | Rawterm.ConstrEval (r,c) ->
      <:expr< Rawterm.ConstrEval $mlexpr_of_red_expr r$ $f c$ >>
  | Rawterm.ConstrContext ((loc,id),c) ->
      let id = mlexpr_of_ident id in
      <:expr< Rawterm.ConstrContext (loc,$id$) $f c$ >>
  | Rawterm.ConstrTypeOf c ->
      <:expr< Rawterm.ConstrTypeOf $mlexpr_of_constr c$ >>
  | Rawterm.ConstrTerm c ->
      <:expr< Rawterm.ConstrTerm $mlexpr_of_constr c$ >>

let mlexpr_of_binding_kind = function
  | Rawterm.ExplicitBindings l ->
      let l = mlexpr_of_list (mlexpr_of_triple mlexpr_of_loc mlexpr_of_quantified_hypothesis mlexpr_of_constr) l in
      <:expr< Rawterm.ExplicitBindings $l$ >>
  | Rawterm.ImplicitBindings l -> 
      let l = mlexpr_of_list mlexpr_of_constr l in
      <:expr< Rawterm.ImplicitBindings $l$ >>
  | Rawterm.NoBindings -> 
       <:expr< Rawterm.NoBindings >>

let mlexpr_of_induction_arg = function
  | Tacexpr.ElimOnConstr c ->
      <:expr< Tacexpr.ElimOnConstr $mlexpr_of_constr c$ >>
  | Tacexpr.ElimOnIdent (_,id) -> 
      <:expr< Tacexpr.ElimOnIdent $dloc$ $mlexpr_of_ident id$ >>
  | Tacexpr.ElimOnAnonHyp n ->
      <:expr< Tacexpr.ElimOnAnonHyp $mlexpr_of_int n$ >>

let mlexpr_of_binding = mlexpr_of_pair mlexpr_of_binding_kind mlexpr_of_constr

let mlexpr_of_constr_with_binding =
  mlexpr_of_pair mlexpr_of_constr mlexpr_of_binding_kind

let mlexpr_of_clause_pattern _ = failwith "mlexpr_of_clause_pattern: TODO"

let mlexpr_of_pattern_ast = mlexpr_of_constr

let mlexpr_of_entry_type = function
    _ -> failwith "mlexpr_of_entry_type: TODO"

let mlexpr_of_match_pattern = function
  | Tacexpr.Term t -> <:expr< Tacexpr.Term $mlexpr_of_pattern_ast t$ >>
  | Tacexpr.Subterm (ido,t) ->
      <:expr< Tacexpr.Subterm $mlexpr_of_option mlexpr_of_ident ido$ $mlexpr_of_pattern_ast t$ >>

let mlexpr_of_match_context_hyps = function
  | Tacexpr.Hyp (id,l) ->
      let f = mlexpr_of_located mlexpr_of_name in
      <:expr< Tacexpr.Hyp $f id$ $mlexpr_of_match_pattern l$ >>

let mlexpr_of_match_rule f = function
  | Tacexpr.Pat (l,mp,t) -> <:expr< Tacexpr.Pat $mlexpr_of_list mlexpr_of_match_context_hyps l$ $mlexpr_of_match_pattern mp$ $f t$ >>
  | Tacexpr.All t -> <:expr< Tacexpr.All $f t$ >>

let rec mlexpr_of_atomic_tactic = function
  (* Basic tactics *)
  | Tacexpr.TacIntroPattern pl ->
      let pl = mlexpr_of_list mlexpr_of_intro_pattern pl in
      <:expr< Tacexpr.TacIntroPattern $pl$ >>
  | Tacexpr.TacIntrosUntil h ->
      <:expr< Tacexpr.TacIntrosUntil $mlexpr_of_quantified_hypothesis h$ >>
  | Tacexpr.TacIntroMove (idopt,idopt') ->
      let idopt = mlexpr_of_ident_option idopt in
      let idopt'=mlexpr_of_option (mlexpr_of_located mlexpr_of_ident) idopt' in
      <:expr< Tacexpr.TacIntroMove $idopt$ $idopt'$ >>
  | Tacexpr.TacAssumption ->
      <:expr< Tacexpr.TacAssumption >>
  | Tacexpr.TacExact c ->
      <:expr< Tacexpr.TacExact $mlexpr_of_constr c$ >>
  | Tacexpr.TacApply cb ->
      <:expr< Tacexpr.TacApply $mlexpr_of_constr_with_binding cb$ >>
  | Tacexpr.TacElim (cb,cbo) ->
      let cb = mlexpr_of_constr_with_binding cb in
      let cbo = mlexpr_of_option mlexpr_of_constr_with_binding cbo in
      <:expr< Tacexpr.TacElim $cb$ $cbo$ >>
  | Tacexpr.TacElimType c ->
      <:expr< Tacexpr.TacElimType $mlexpr_of_constr c$ >>
  | Tacexpr.TacCase cb ->
      let cb = mlexpr_of_constr_with_binding cb in
      <:expr< Tacexpr.TacCase $cb$ >>
  | Tacexpr.TacCaseType c ->
      <:expr< Tacexpr.TacCaseType $mlexpr_of_constr c$ >>
  | Tacexpr.TacFix (ido,n) ->
      let ido = mlexpr_of_ident_option ido in
      let n = mlexpr_of_int n in
      <:expr< Tacexpr.TacFix $ido$ $n$ >>
  | Tacexpr.TacMutualFix (id,n,l) ->
      let id = mlexpr_of_ident id in
      let n = mlexpr_of_int n in
      let f =mlexpr_of_triple mlexpr_of_ident mlexpr_of_int mlexpr_of_constr in
      let l = mlexpr_of_list f l in
      <:expr< Tacexpr.TacMutualFix $id$ $n$ $l$ >>
  | Tacexpr.TacCofix ido ->
      let ido = mlexpr_of_ident_option ido in
      <:expr< Tacexpr.TacCofix $ido$ >>
  | Tacexpr.TacMutualCofix (id,l) ->
      let id = mlexpr_of_ident id in
      let f = mlexpr_of_pair mlexpr_of_ident mlexpr_of_constr in
      let l = mlexpr_of_list f l in
      <:expr< Tacexpr.TacMutualCofix $id$ $l$ >>

  | Tacexpr.TacCut c ->
      <:expr< Tacexpr.TacCut $mlexpr_of_constr c$ >>
  | Tacexpr.TacTrueCut (na,c) ->
      let na = mlexpr_of_name na in
      <:expr< Tacexpr.TacTrueCut $na$ $mlexpr_of_constr c$ >>
  | Tacexpr.TacForward (b,na,c) ->
      <:expr< Tacexpr.TacForward $mlexpr_of_bool b$ $mlexpr_of_name na$ $mlexpr_of_constr c$ >>
  | Tacexpr.TacGeneralize cl ->
      <:expr< Tacexpr.TacGeneralize $mlexpr_of_list mlexpr_of_constr cl$ >>
  | Tacexpr.TacGeneralizeDep c ->
      <:expr< Tacexpr.TacGeneralizeDep $mlexpr_of_constr c$ >>
  | Tacexpr.TacLetTac (na,c,cl) ->
      let na = mlexpr_of_name na in
      let cl = mlexpr_of_clause_pattern cl in
      <:expr< Tacexpr.TacLetTac $na$ $mlexpr_of_constr c$ $cl$ >>

  (* Derived basic tactics *)
  | Tacexpr.TacSimpleInduction (h,_) ->
      <:expr< Tacexpr.TacSimpleInduction ($mlexpr_of_quantified_hypothesis h$,ref []) >>
  | Tacexpr.TacNewInduction (c,cbo,ids) ->
      let cbo = mlexpr_of_option mlexpr_of_constr_with_binding cbo in
      let ids = mlexpr_of_option mlexpr_of_intro_pattern (fst ids) in
      <:expr< Tacexpr.TacNewInduction $mlexpr_of_induction_arg c$ $cbo$ ($ids$,ref [])>>
  | Tacexpr.TacSimpleDestruct h ->
      <:expr< Tacexpr.TacSimpleDestruct $mlexpr_of_quantified_hypothesis h$ >>
  | Tacexpr.TacNewDestruct (c,cbo,ids) ->
      let cbo = mlexpr_of_option mlexpr_of_constr_with_binding cbo in
      let ids = mlexpr_of_option mlexpr_of_intro_pattern (fst ids) in
      <:expr< Tacexpr.TacNewDestruct $mlexpr_of_induction_arg c$ $cbo$ ($ids$,ref []) >>

  (* Context management *)
  | Tacexpr.TacClear l ->
      let l = mlexpr_of_list (mlexpr_of_hyp) l in
      <:expr< Tacexpr.TacClear $l$ >>
  | Tacexpr.TacClearBody l ->
      let l = mlexpr_of_list (mlexpr_of_hyp) l in
      <:expr< Tacexpr.TacClearBody $l$ >>
  | Tacexpr.TacMove (dep,id1,id2) ->
      <:expr< Tacexpr.TacMove $mlexpr_of_bool dep$
              $mlexpr_of_hyp id1$
              $mlexpr_of_hyp id2$ >>

  (* Constructors *)
  | Tacexpr.TacLeft l ->
      <:expr< Tacexpr.TacLeft $mlexpr_of_binding_kind l$>>
  | Tacexpr.TacRight l ->
      <:expr< Tacexpr.TacRight $mlexpr_of_binding_kind l$>>
  | Tacexpr.TacSplit (b,l) ->
      <:expr< Tacexpr.TacSplit
        ($mlexpr_of_bool b$,$mlexpr_of_binding_kind l$)>>
  | Tacexpr.TacAnyConstructor t ->
      <:expr< Tacexpr.TacAnyConstructor $mlexpr_of_option mlexpr_of_tactic t$>>
  | Tacexpr.TacConstructor (n,l) ->
      let n = mlexpr_of_or_metaid mlexpr_of_int n in
      <:expr< Tacexpr.TacConstructor $n$ $mlexpr_of_binding_kind l$>>

  (* Conversion *)
  | Tacexpr.TacReduce (r,cl) ->
      let l = mlexpr_of_clause cl in
      <:expr< Tacexpr.TacReduce $mlexpr_of_red_expr r$ $l$ >>
  | Tacexpr.TacChange (occl,c,cl) ->
      let l = mlexpr_of_clause cl in
      let g = mlexpr_of_option mlexpr_of_occ_constr in
      <:expr< Tacexpr.TacChange $g occl$ $mlexpr_of_constr c$ $l$ >>

  (* Equivalence relations *)
  | Tacexpr.TacReflexivity -> <:expr< Tacexpr.TacReflexivity >>
  | Tacexpr.TacSymmetry ido -> <:expr< Tacexpr.TacSymmetry $mlexpr_of_clause ido$ >>
  | Tacexpr.TacTransitivity c -> <:expr< Tacexpr.TacTransitivity $mlexpr_of_constr c$ >>

  (* Automation tactics *)
  | Tacexpr.TacAuto (n,l) ->
      let n = mlexpr_of_option mlexpr_of_int n in
      let l = mlexpr_of_option (mlexpr_of_list mlexpr_of_string) l in
      <:expr< Tacexpr.TacAuto $n$ $l$ >>
(*
  | Tacexpr.TacTrivial l ->
      let l = mlexpr_of_option (mlexpr_of_list mlexpr_of_string) l in
      <:expr< Tacexpr.TacTrivial $l$ >>
*)

(*
  | Tacexpr.TacExtend (s,l) ->
      let l = mlexpr_of_list mlexpr_of_tactic_arg l in
      let $dloc$ = MLast.loc_of_expr l in
      <:expr< Tacexpr.TacExtend $mlexpr_of_string s$ $l$ >>
*)
  | _ -> failwith "Quotation of atomic tactic expressions: TODO"

and mlexpr_of_tactic : (Tacexpr.raw_tactic_expr -> MLast.expr) = function
  | Tacexpr.TacAtom (loc,t) ->
      <:expr< Tacexpr.TacAtom $dloc$ $mlexpr_of_atomic_tactic t$ >>
  | Tacexpr.TacThen (t1,t2) -> 
      <:expr< Tacexpr.TacThen $mlexpr_of_tactic t1$ $mlexpr_of_tactic t2$ >>
  | Tacexpr.TacThens (t,tl) ->
      <:expr< Tacexpr.TacThens $mlexpr_of_tactic t$ $mlexpr_of_list mlexpr_of_tactic tl$>>
  | Tacexpr.TacFirst tl ->
      <:expr< Tacexpr.TacFirst $mlexpr_of_list mlexpr_of_tactic tl$ >>
  | Tacexpr.TacSolve tl ->
      <:expr< Tacexpr.TacSolve $mlexpr_of_list mlexpr_of_tactic tl$ >>
  | Tacexpr.TacTry t ->
      <:expr< Tacexpr.TacTry $mlexpr_of_tactic t$ >>
  | Tacexpr.TacOrelse (t1,t2) ->
      <:expr< Tacexpr.TacOrelse $mlexpr_of_tactic t1$ $mlexpr_of_tactic t2$ >>
  | Tacexpr.TacDo (n,t) ->
      <:expr< Tacexpr.TacDo $mlexpr_of_or_var mlexpr_of_int n$ $mlexpr_of_tactic t$ >>
  | Tacexpr.TacRepeat t ->
      <:expr< Tacexpr.TacRepeat $mlexpr_of_tactic t$ >>
  | Tacexpr.TacProgress t ->
      <:expr< Tacexpr.TacProgress $mlexpr_of_tactic t$ >>
  | Tacexpr.TacId s -> <:expr< Tacexpr.TacId $str:s$ >>
  | Tacexpr.TacFail (n,s) -> <:expr< Tacexpr.TacFail $mlexpr_of_or_var mlexpr_of_int n$ $str:s$ >>
(*
  | Tacexpr.TacInfo t -> TacInfo (loc,f t)

  | Tacexpr.TacRec (id,(idl,t)) -> TacRec (loc,(id,(idl,f t)))
  | Tacexpr.TacRecIn (l,t) -> TacRecIn(loc,List.map (fun (id,t) -> (id,f t)) l,f t)
*)
  | Tacexpr.TacLetIn (l,t) ->
      let f =
	mlexpr_of_triple
	  (mlexpr_of_pair (fun _ -> dloc) mlexpr_of_ident)
	  (mlexpr_of_option mlexpr_of_tactic)
	  mlexpr_of_tactic_arg in
      <:expr< Tacexpr.TacLetIn $mlexpr_of_list f l$ $mlexpr_of_tactic t$ >>
  | Tacexpr.TacMatch (t,l) ->
      <:expr< Tacexpr.TacMatch
        $mlexpr_of_tactic t$
        $mlexpr_of_list (mlexpr_of_match_rule mlexpr_of_tactic) l$>>
  | Tacexpr.TacMatchContext (lr,l) ->
      <:expr< Tacexpr.TacMatchContext 
        $mlexpr_of_bool lr$
        $mlexpr_of_list (mlexpr_of_match_rule mlexpr_of_tactic) l$>>
(*
  | Tacexpr.TacFun of $dloc$ * tactic_fun_ast
  | Tacexpr.TacFunRec of $dloc$ * identifier * tactic_fun_ast
*)
(*
  | Tacexpr.TacArg (Tacexpr.AstTacArg (Coqast.Nmeta $dloc$ id)) -> anti loc id
*)
  | Tacexpr.TacArg (Tacexpr.MetaIdArg (_,id)) -> anti loc id
  | Tacexpr.TacArg t ->
      <:expr< Tacexpr.TacArg $mlexpr_of_tactic_arg t$ >>
  | _ -> failwith "Quotation of tactic expressions: TODO"

and mlexpr_of_tactic_arg = function
  | Tacexpr.MetaIdArg (loc,id) -> anti loc id
  | Tacexpr.TacCall (loc,t,tl) ->
      <:expr< Tacexpr.TacCall $dloc$ $mlexpr_of_reference t$ $mlexpr_of_list mlexpr_of_tactic_arg tl$>>
  | Tacexpr.Tacexp t ->
      <:expr< Tacexpr.Tacexp $mlexpr_of_tactic t$ >>
  | Tacexpr.ConstrMayEval c ->
      <:expr< Tacexpr.ConstrMayEval $mlexpr_of_may_eval mlexpr_of_constr c$ >>
  | Tacexpr.Reference r ->
      <:expr< Tacexpr.Reference $mlexpr_of_reference r$ >>
  | _ -> failwith "mlexpr_of_tactic_arg: TODO"

let f e =
  let ee s =
    mlexpr_of_ast (Pcoq.Gram.Entry.parse e
                     (Pcoq.Gram.parsable (Stream.of_string s)))
  in
  let ep s = patt_of_expr (ee s) in
  Quotation.ExAst (ee, ep)

let fconstr e =
  let ee s =
    mlexpr_of_constr (Pcoq.Gram.Entry.parse e
                     (Pcoq.Gram.parsable (Stream.of_string s)))
  in
  let ep s = patt_of_expr (ee s) in
  Quotation.ExAst (ee, ep)

let ftac e =
  let ee s =
    mlexpr_of_tactic (Pcoq.Gram.Entry.parse e
                     (Pcoq.Gram.parsable (Stream.of_string s)))
  in
  let ep s = patt_of_expr (ee s) in
  Quotation.ExAst (ee, ep)

let _ = 
  Quotation.add "constr" (fconstr Pcoq.Constr.constr_eoi);
  Quotation.add "tactic" (ftac Pcoq.Tactic.tactic_eoi);
(*  Quotation.add "vernac" (f Pcoq.Vernac_.vernac_eoi);*)
(*  Quotation.add "ast" (f Pcoq.Prim.ast_eoi);*)
  Quotation.default := "constr"
