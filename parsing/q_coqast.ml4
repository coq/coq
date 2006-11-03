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
    let loc =
      ifdef OCAML_308 then
        loc
      else
        (1, snd loc - fst loc)
    in <:expr< $lid:purge_str x$ >>
  in
  <:expr< $anti:e$ >>

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
  | Genarg.IntroAnonymous -> <:expr< Genarg.IntroAnonymous >>
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
  | Rawterm.ArgArg x -> <:expr< Rawterm.ArgArg $f x$ >>
  | Rawterm.ArgVar id -> <:expr< Rawterm.ArgVar $mlexpr_of_located mlexpr_of_ident id$ >>

let mlexpr_of_hyp = mlexpr_of_or_metaid (mlexpr_of_located mlexpr_of_ident)

let mlexpr_of_occs = mlexpr_of_list (mlexpr_of_or_var mlexpr_of_int)

let mlexpr_of_occurrences f = mlexpr_of_pair mlexpr_of_occs f

let mlexpr_of_hyp_location = function
  | occs, Tacexpr.InHyp ->
      <:expr< ($mlexpr_of_occurrences mlexpr_of_hyp occs$, Tacexpr.InHyp) >>
  | occs, Tacexpr.InHypTypeOnly ->
      <:expr< ($mlexpr_of_occurrences mlexpr_of_hyp occs$, Tacexpr.InHypTypeOnly) >>
  | occs, Tacexpr.InHypValueOnly ->
      <:expr< ($mlexpr_of_occurrences mlexpr_of_hyp occs$, Tacexpr.InHypValueOnly) >>

let mlexpr_of_clause cl =
  <:expr< {Tacexpr.onhyps=
             $mlexpr_of_option (mlexpr_of_list mlexpr_of_hyp_location)
               cl.Tacexpr.onhyps$;
           Tacexpr.onconcl= $mlexpr_of_bool cl.Tacexpr.onconcl$;
           Tacexpr.concl_occs= $mlexpr_of_occs cl.Tacexpr.concl_occs$} >>

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
  | Topconstr.CHole loc -> <:expr< Topconstr.CHole $dloc$ >>
  | Topconstr.CNotation(_,ntn,l) ->
      <:expr< Topconstr.CNotation $dloc$ $mlexpr_of_string ntn$
                $mlexpr_of_list mlexpr_of_constr l$ >>
  | Topconstr.CPatVar (loc,n) -> 
      <:expr< Topconstr.CPatVar $dloc$ $mlexpr_of_pair mlexpr_of_bool mlexpr_of_ident n$ >>
  | _ -> failwith "mlexpr_of_constr: TODO"

let mlexpr_of_occ_constr =
  mlexpr_of_pair (mlexpr_of_list (mlexpr_of_or_var mlexpr_of_int))
    mlexpr_of_constr

let mlexpr_of_red_expr = function
  | Rawterm.Red b -> <:expr< Rawterm.Red $mlexpr_of_bool b$ >>
  | Rawterm.Hnf -> <:expr< Rawterm.Hnf >>
  | Rawterm.Simpl o -> <:expr< Rawterm.Simpl $mlexpr_of_option mlexpr_of_occ_constr o$ >>
  | Rawterm.Cbv f ->
      <:expr< Rawterm.Cbv $mlexpr_of_red_flags f$ >>
  | Rawterm.Lazy f ->
      <:expr< Rawterm.Lazy $mlexpr_of_red_flags f$ >>
  | Rawterm.Unfold l ->
      let f1 = mlexpr_of_list (mlexpr_of_or_var mlexpr_of_int) in
      let f2 = mlexpr_of_reference in
      let f = mlexpr_of_list (mlexpr_of_pair f1 f2) in
      <:expr< Rawterm.Unfold $f l$ >>
  | Rawterm.Fold l ->
      <:expr< Rawterm.Fold $mlexpr_of_list mlexpr_of_constr l$ >>
  | Rawterm.Pattern l ->
      let f = mlexpr_of_list mlexpr_of_occ_constr in
      <:expr< Rawterm.Pattern $f l$ >>
  | Rawterm.CbvVm -> <:expr< Rawterm.CbvVm >>
  | Rawterm.ExtraRedExpr s ->
      <:expr< Rawterm.ExtraRedExpr $mlexpr_of_string s$ >>

let rec mlexpr_of_argtype loc = function
  | Genarg.BoolArgType -> <:expr< Genarg.BoolArgType >>
  | Genarg.IntArgType -> <:expr< Genarg.IntArgType >>
  | Genarg.IntOrVarArgType -> <:expr< Genarg.IntOrVarArgType >>
  | Genarg.RefArgType -> <:expr< Genarg.RefArgType >>
  | Genarg.PreIdentArgType -> <:expr< Genarg.PreIdentArgType >>
  | Genarg.IntroPatternArgType -> <:expr< Genarg.IntroPatternArgType >>
  | Genarg.IdentArgType -> <:expr< Genarg.IdentArgType >>
  | Genarg.VarArgType -> <:expr< Genarg.VarArgType >>
  | Genarg.StringArgType -> <:expr< Genarg.StringArgType >>
  | Genarg.QuantHypArgType -> <:expr< Genarg.QuantHypArgType >>
  | Genarg.OpenConstrArgType b -> <:expr< Genarg.OpenConstrArgType $mlexpr_of_bool b$ >>
  | Genarg.ConstrWithBindingsArgType -> <:expr< Genarg.ConstrWithBindingsArgType >>
  | Genarg.BindingsArgType -> <:expr< Genarg.BindingsArgType >>
  | Genarg.RedExprArgType -> <:expr< Genarg.RedExprArgType >>
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

let mlexpr_of_message_token = function
  | Tacexpr.MsgString s -> <:expr< Tacexpr.MsgString $str:s$ >>
  | Tacexpr.MsgInt n -> <:expr< Tacexpr.MsgInt $mlexpr_of_int n$ >>
  | Tacexpr.MsgIdent id -> <:expr< Tacexpr.MsgIdent $mlexpr_of_hyp id$ >>

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
  | Tacexpr.TacExactNoCheck c ->
      <:expr< Tacexpr.TacExactNoCheck $mlexpr_of_constr c$ >>
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
  | Tacexpr.TacAssert (t,ipat,c) ->
      let ipat = mlexpr_of_intro_pattern ipat in
      <:expr< Tacexpr.TacAssert $mlexpr_of_option mlexpr_of_tactic t$ $ipat$ 
	      $mlexpr_of_constr c$ >>
  | Tacexpr.TacGeneralize cl ->
      <:expr< Tacexpr.TacGeneralize $mlexpr_of_list mlexpr_of_constr cl$ >>
  | Tacexpr.TacGeneralizeDep c ->
      <:expr< Tacexpr.TacGeneralizeDep $mlexpr_of_constr c$ >>
  | Tacexpr.TacLetTac (na,c,cl) ->
      let na = mlexpr_of_name na in
      let cl = mlexpr_of_clause_pattern cl in
      <:expr< Tacexpr.TacLetTac $na$ $mlexpr_of_constr c$ $cl$ >>

  (* Derived basic tactics *)
  | Tacexpr.TacSimpleInduction h ->
      <:expr< Tacexpr.TacSimpleInduction ($mlexpr_of_quantified_hypothesis h$) >>
  | Tacexpr.TacNewInduction (cl,cbo,ids) ->
      let cbo = mlexpr_of_option mlexpr_of_constr_with_binding cbo in
      let ids = mlexpr_of_intro_pattern ids in
(*       let ids = mlexpr_of_option mlexpr_of_intro_pattern ids in *)
(*       <:expr< Tacexpr.TacNewInduction $mlexpr_of_induction_arg c$ $cbo$ $ids$>> *)
      <:expr< Tacexpr.TacNewInduction $mlexpr_of_list mlexpr_of_induction_arg cl$ $cbo$ $ids$>>
  | Tacexpr.TacSimpleDestruct h ->
      <:expr< Tacexpr.TacSimpleDestruct $mlexpr_of_quantified_hypothesis h$ >>
  | Tacexpr.TacNewDestruct (c,cbo,ids) ->
      let cbo = mlexpr_of_option mlexpr_of_constr_with_binding cbo in
      let ids = mlexpr_of_intro_pattern ids in
      <:expr< Tacexpr.TacNewDestruct $mlexpr_of_list mlexpr_of_induction_arg c$ $cbo$ $ids$ >>

  (* Context management *)
  | Tacexpr.TacClear (b,l) ->
      let l = mlexpr_of_list (mlexpr_of_hyp) l in
      <:expr< Tacexpr.TacClear $mlexpr_of_bool b$ $l$ >>
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
  | Tacexpr.TacAuto (n,lems,l) ->
      let n = mlexpr_of_option (mlexpr_of_or_var mlexpr_of_int) n in
      let lems = mlexpr_of_list mlexpr_of_constr lems in
      let l = mlexpr_of_option (mlexpr_of_list mlexpr_of_string) l in
      <:expr< Tacexpr.TacAuto $n$ $lems$ $l$ >>
  | Tacexpr.TacTrivial (lems,l) ->
      let l = mlexpr_of_option (mlexpr_of_list mlexpr_of_string) l in
      let lems = mlexpr_of_list mlexpr_of_constr lems in
      <:expr< Tacexpr.TacTrivial $lems$ $l$ >>

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
  | Tacexpr.TacId l -> 
      <:expr< Tacexpr.TacId $mlexpr_of_list mlexpr_of_message_token l$ >>
  | Tacexpr.TacFail (n,l) ->
      <:expr< Tacexpr.TacFail $mlexpr_of_or_var mlexpr_of_int n$ $mlexpr_of_list mlexpr_of_message_token l$ >>
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
  | Tacexpr.TacMatch (lz,t,l) ->
      <:expr< Tacexpr.TacMatch
        $mlexpr_of_bool lz$
        $mlexpr_of_tactic t$
        $mlexpr_of_list (mlexpr_of_match_rule mlexpr_of_tactic) l$>>
  | Tacexpr.TacMatchContext (lz,lr,l) ->
      <:expr< Tacexpr.TacMatchContext 
        $mlexpr_of_bool lz$
        $mlexpr_of_bool lr$
        $mlexpr_of_list (mlexpr_of_match_rule mlexpr_of_tactic) l$>>

  | Tacexpr.TacFun (idol,body) ->
      <:expr< Tacexpr.TacFun
        ($mlexpr_of_list mlexpr_of_ident_option idol$,
         $mlexpr_of_tactic body$) >>
(*
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
  Quotation.default := "constr"
