(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Q_util
open Compat

let is_meta s = String.length s > 0 && s.[0] == '$'

let purge_str s =
  if String.length s == 0 || s.[0] <> '$' then s
  else String.sub s 1 (String.length s - 1)

let anti loc x =
  expl_anti loc <:expr< $lid:purge_str x$ >>

(* We don't give location for tactic quotation! *)
let loc = CompatLoc.ghost

let dloc = <:expr< Loc.ghost >>

let mlexpr_of_ident id =
  <:expr< Names.Id.of_string $str:Names.Id.to_string id$ >>

let mlexpr_of_name = function
  | Names.Anonymous -> <:expr< Names.Anonymous >>
  | Names.Name id ->
      <:expr< Names.Name (Names.Id.of_string $str:Names.Id.to_string id$) >>

let mlexpr_of_dirpath dir =
  let l = Names.DirPath.repr dir in
  <:expr< Names.DirPath.make $mlexpr_of_list mlexpr_of_ident l$ >>

let mlexpr_of_qualid qid =
  let (dir, id) = Libnames.repr_qualid qid in
  <:expr< Libnames.make_qualid $mlexpr_of_dirpath dir$ $mlexpr_of_ident id$ >>

let mlexpr_of_reference = function
  | Libnames.Qualid (loc,qid) ->
    let loc = of_coqloc loc in <:expr< Libnames.Qualid $dloc$ $mlexpr_of_qualid qid$ >>
  | Libnames.Ident (loc,id) ->
    let loc = of_coqloc loc in <:expr< Libnames.Ident $dloc$ $mlexpr_of_ident id$ >>

let mlexpr_of_union f g = function
  | Util.Inl a -> <:expr< Util.Inl $f a$ >>
  | Util.Inr b -> <:expr< Util.Inr $g b$ >>

let mlexpr_of_located f (loc,x) =
  let loc = of_coqloc loc in
  <:expr< ($dloc$, $f x$) >>

let mlexpr_of_loc loc = <:expr< $dloc$ >>

let mlexpr_of_by_notation f = function
  | Misctypes.AN x -> <:expr< Misctypes.AN $f x$ >>
  | Misctypes.ByNotation (loc,s,sco) ->
      let loc = of_coqloc loc in
      <:expr< Misctypes.ByNotation $dloc$ $str:s$ $mlexpr_of_option mlexpr_of_string sco$ >>

let mlexpr_of_global_flag = function
  | Tacexpr.TacGlobal -> <:expr<Tacexpr.TacGlobal>>
  | Tacexpr.TacLocal  -> <:expr<Tacexpr.TacLocal>>

let mlexpr_of_intro_pattern_disjunctive = function
  _ -> failwith "mlexpr_of_intro_pattern_disjunctive: TODO"

let mlexpr_of_intro_pattern_naming = function
  | Misctypes.IntroAnonymous -> <:expr< Misctypes.IntroAnonymous >>
  | Misctypes.IntroFresh id -> <:expr< Misctypes.IntroFresh (mlexpr_of_ident $dloc$ id) >>
  | Misctypes.IntroIdentifier id ->
      <:expr< Misctypes.IntroIdentifier (mlexpr_of_ident $dloc$ id) >>

let mlexpr_of_intro_pattern = function
  | Misctypes.IntroForthcoming b -> <:expr< Misctypes.IntroForthcoming (mlexpr_of_bool $dloc$ b) >>
  | Misctypes.IntroNaming pat ->
      <:expr< Misctypes.IntroNaming $mlexpr_of_intro_pattern_naming pat$ >>
  | Misctypes.IntroAction _ ->
      failwith "mlexpr_of_intro_pattern: TODO"

let mlexpr_of_ident_option = mlexpr_of_option (mlexpr_of_ident)

let mlexpr_of_quantified_hypothesis = function
  | Misctypes.AnonHyp n -> <:expr< Glob_term.AnonHyp $mlexpr_of_int n$ >>
  | Misctypes.NamedHyp id ->  <:expr< Glob_term.NamedHyp $mlexpr_of_ident id$ >>

let mlexpr_of_or_var f = function
  | Misctypes.ArgArg x -> <:expr< Misctypes.ArgArg $f x$ >>
  | Misctypes.ArgVar id -> <:expr< Misctypes.ArgVar $mlexpr_of_located mlexpr_of_ident id$ >>

let mlexpr_of_hyp = (mlexpr_of_located mlexpr_of_ident)

let mlexpr_of_occs = function
  | Locus.AllOccurrences -> <:expr< Locus.AllOccurrences >>
  | Locus.AllOccurrencesBut l ->
    <:expr< Locus.AllOccurrencesBut
      $mlexpr_of_list (mlexpr_of_or_var mlexpr_of_int) l$ >>
  | Locus.NoOccurrences -> <:expr< Locus.NoOccurrences >>
  | Locus.OnlyOccurrences l ->
    <:expr< Locus.OnlyOccurrences
      $mlexpr_of_list (mlexpr_of_or_var mlexpr_of_int) l$ >>

let mlexpr_of_occurrences f = mlexpr_of_pair mlexpr_of_occs f

let mlexpr_of_hyp_location = function
  | occs, Locus.InHyp ->
      <:expr< ($mlexpr_of_occurrences mlexpr_of_hyp occs$, Locus.InHyp) >>
  | occs, Locus.InHypTypeOnly ->
      <:expr< ($mlexpr_of_occurrences mlexpr_of_hyp occs$, Locus.InHypTypeOnly) >>
  | occs, Locus.InHypValueOnly ->
      <:expr< ($mlexpr_of_occurrences mlexpr_of_hyp occs$, Locus.InHypValueOnly) >>

let mlexpr_of_clause cl =
  <:expr< {Locus.onhyps=
             $mlexpr_of_option (mlexpr_of_list mlexpr_of_hyp_location)
               cl.Locus.onhyps$;
           Locus.concl_occs= $mlexpr_of_occs cl.Locus.concl_occs$} >>

let mlexpr_of_red_flags {
  Genredexpr.rBeta = bb;
  Genredexpr.rIota = bi;
  Genredexpr.rZeta = bz;
  Genredexpr.rDelta = bd;
  Genredexpr.rConst = l
} = <:expr< {
  Genredexpr.rBeta = $mlexpr_of_bool bb$;
  Genredexpr.rIota = $mlexpr_of_bool bi$;
  Genredexpr.rZeta = $mlexpr_of_bool bz$;
  Genredexpr.rDelta = $mlexpr_of_bool bd$;
  Genredexpr.rConst = $mlexpr_of_list (mlexpr_of_by_notation mlexpr_of_reference) l$
} >>

let mlexpr_of_instance c = <:expr< None >>

let mlexpr_of_explicitation = function
  | Constrexpr.ExplByName id -> <:expr< Constrexpr.ExplByName $mlexpr_of_ident id$ >>
  | Constrexpr.ExplByPos (n,_id) -> <:expr< Constrexpr.ExplByPos $mlexpr_of_int n$ >>

let mlexpr_of_binding_kind = function
  | Decl_kinds.Implicit -> <:expr< Decl_kinds.Implicit >>
  | Decl_kinds.Explicit -> <:expr< Decl_kinds.Explicit >>

let mlexpr_of_binder_kind = function
  | Constrexpr.Default b -> <:expr< Constrexpr.Default $mlexpr_of_binding_kind b$ >>
  | Constrexpr.Generalized (b,b',b'') ->
      <:expr< Constrexpr.TypeClass $mlexpr_of_binding_kind b$
	$mlexpr_of_binding_kind b'$ $mlexpr_of_bool b''$ >>

let rec mlexpr_of_constr = function
  | Constrexpr.CRef (Libnames.Ident (loc,id),_) when is_meta (Id.to_string id) ->
      let loc = of_coqloc loc in
      anti loc (Id.to_string id)
  | Constrexpr.CRef (r,n) -> <:expr< Constrexpr.CRef $mlexpr_of_reference r$ None >>
  | Constrexpr.CFix (loc,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Constrexpr.CCoFix (loc,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Constrexpr.CProdN (loc,l,a) ->
      let loc = of_coqloc loc in
      <:expr< Constrexpr.CProdN $dloc$ $mlexpr_of_list
      (mlexpr_of_triple (mlexpr_of_list (mlexpr_of_pair (fun _ -> dloc) mlexpr_of_name)) mlexpr_of_binder_kind mlexpr_of_constr) l$ $mlexpr_of_constr a$ >>
  | Constrexpr.CLambdaN (loc,l,a) ->
    let loc = of_coqloc loc in
    <:expr< Constrexpr.CLambdaN $dloc$ $mlexpr_of_list (mlexpr_of_triple (mlexpr_of_list (mlexpr_of_pair (fun _ -> dloc) mlexpr_of_name)) mlexpr_of_binder_kind mlexpr_of_constr) l$ $mlexpr_of_constr a$ >>
  | Constrexpr.CLetIn (loc,_,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Constrexpr.CAppExpl (loc,(p,r,us),l) ->
    let loc = of_coqloc loc in
    let a = (p,r,us) in
    <:expr< Constrexpr.CAppExpl $dloc$ $mlexpr_of_triple (mlexpr_of_option mlexpr_of_int) mlexpr_of_reference mlexpr_of_instance a$ $mlexpr_of_list mlexpr_of_constr l$ >>
  | Constrexpr.CApp (loc,a,l) ->
    let loc = of_coqloc loc in
    <:expr< Constrexpr.CApp $dloc$ $mlexpr_of_pair (mlexpr_of_option mlexpr_of_int) mlexpr_of_constr a$ $mlexpr_of_list (mlexpr_of_pair mlexpr_of_constr (mlexpr_of_option (mlexpr_of_located mlexpr_of_explicitation))) l$ >>
  | Constrexpr.CCases (loc,_,_,_,_) -> failwith "mlexpr_of_constr: TODO"
  | Constrexpr.CHole (loc, None, ipat, None) ->
    let loc = of_coqloc loc in
    <:expr< Constrexpr.CHole $dloc$ None $mlexpr_of_intro_pattern_naming ipat$ None >>
  | Constrexpr.CHole (loc,_,_,_) -> failwith "mlexpr_of_constr: TODO CHole (Some _)"
  | Constrexpr.CNotation(_,ntn,(subst,substl,[])) ->
      <:expr< Constrexpr.CNotation $dloc$ $mlexpr_of_string ntn$
              ($mlexpr_of_list mlexpr_of_constr subst$,
               $mlexpr_of_list (mlexpr_of_list mlexpr_of_constr) substl$,[]) >>
  | Constrexpr.CPatVar (loc,n) ->
      let loc = of_coqloc loc in
      <:expr< Constrexpr.CPatVar $dloc$ $mlexpr_of_ident n$ >>
  | Constrexpr.CEvar (loc,n,[]) ->
      let loc = of_coqloc loc in
      <:expr< Constrexpr.CEvar $dloc$ $mlexpr_of_ident n$ [] >>
  | _ -> failwith "mlexpr_of_constr: TODO"

let mlexpr_of_occ_constr =
  mlexpr_of_occurrences mlexpr_of_constr

let mlexpr_of_occ_ref_or_constr =
  mlexpr_of_occurrences
    (mlexpr_of_union
       (mlexpr_of_by_notation mlexpr_of_reference) mlexpr_of_constr)

let mlexpr_of_red_expr = function
  | Genredexpr.Red b -> <:expr< Genredexpr.Red $mlexpr_of_bool b$ >>
  | Genredexpr.Hnf -> <:expr< Genredexpr.Hnf >>
  | Genredexpr.Simpl (f,o) ->
      <:expr< Genredexpr.Simpl $mlexpr_of_red_flags f$ $mlexpr_of_option mlexpr_of_occ_ref_or_constr o$ >>
  | Genredexpr.Cbv f ->
      <:expr< Genredexpr.Cbv $mlexpr_of_red_flags f$ >>
  | Genredexpr.Cbn f ->
      <:expr< Genredexpr.Cbn $mlexpr_of_red_flags f$ >>
  | Genredexpr.Lazy f ->
      <:expr< Genredexpr.Lazy $mlexpr_of_red_flags f$ >>
  | Genredexpr.Unfold l ->
      let f1 = mlexpr_of_by_notation mlexpr_of_reference in
      let f = mlexpr_of_list (mlexpr_of_occurrences f1) in
      <:expr< Genredexpr.Unfold $f l$ >>
  | Genredexpr.Fold l ->
      <:expr< Genredexpr.Fold $mlexpr_of_list mlexpr_of_constr l$ >>
  | Genredexpr.Pattern l ->
      let f = mlexpr_of_list mlexpr_of_occ_constr in
      <:expr< Genredexpr.Pattern $f l$ >>
  | Genredexpr.CbvVm o -> <:expr< Genredexpr.CbvVm $mlexpr_of_option mlexpr_of_occ_ref_or_constr o$ >>
  | Genredexpr.CbvNative o -> <:expr< Genredexpr.CbvNative $mlexpr_of_option mlexpr_of_occ_ref_or_constr o$ >>
  | Genredexpr.ExtraRedExpr s ->
      <:expr< Genredexpr.ExtraRedExpr $mlexpr_of_string s$ >>

let rec mlexpr_of_argtype loc = function
  | Genarg.IntOrVarArgType -> <:expr< Genarg.IntOrVarArgType >>
  | Genarg.IdentArgType -> <:expr< Genarg.IdentArgType >>
  | Genarg.VarArgType -> <:expr< Genarg.VarArgType >>
  | Genarg.QuantHypArgType -> <:expr< Genarg.QuantHypArgType >>
  | Genarg.OpenConstrArgType -> <:expr< Genarg.OpenConstrArgType >>
  | Genarg.ConstrWithBindingsArgType -> <:expr< Genarg.ConstrWithBindingsArgType >>
  | Genarg.BindingsArgType -> <:expr< Genarg.BindingsArgType >>
  | Genarg.RedExprArgType -> <:expr< Genarg.RedExprArgType >>
  | Genarg.GenArgType -> <:expr< Genarg.GenArgType >>
  | Genarg.ConstrArgType -> <:expr< Genarg.ConstrArgType >>
  | Genarg.ConstrMayEvalArgType -> <:expr< Genarg.ConstrMayEvalArgType >>
  | Genarg.ListArgType t -> <:expr< Genarg.ListArgType $mlexpr_of_argtype loc t$ >>
  | Genarg.OptArgType t -> <:expr< Genarg.OptArgType $mlexpr_of_argtype loc t$ >>
  | Genarg.PairArgType (t1,t2) ->
      let t1 = mlexpr_of_argtype loc t1 in
      let t2 = mlexpr_of_argtype loc t2 in
      <:expr< Genarg.PairArgType $t1$ $t2$ >>
  | Genarg.ExtraArgType s -> <:expr< Genarg.ExtraArgType $str:s$ >>

let mlexpr_of_may_eval f = function
  | Genredexpr.ConstrEval (r,c) ->
      <:expr< Genredexpr.ConstrEval $mlexpr_of_red_expr r$ $f c$ >>
  | Genredexpr.ConstrContext ((loc,id),c) ->
      let loc = of_coqloc loc in
      let id = mlexpr_of_ident id in
      <:expr< Genredexpr.ConstrContext (loc,$id$) $f c$ >>
  | Genredexpr.ConstrTypeOf c ->
      <:expr< Genredexpr.ConstrTypeOf $mlexpr_of_constr c$ >>
  | Genredexpr.ConstrTerm c ->
      <:expr< Genredexpr.ConstrTerm $mlexpr_of_constr c$ >>

let mlexpr_of_binding_kind = function
  | Misctypes.ExplicitBindings l ->
      let l = mlexpr_of_list (mlexpr_of_triple mlexpr_of_loc mlexpr_of_quantified_hypothesis mlexpr_of_constr) l in
      <:expr< Misctypes.ExplicitBindings $l$ >>
  | Misctypes.ImplicitBindings l ->
      let l = mlexpr_of_list mlexpr_of_constr l in
      <:expr< Misctypes.ImplicitBindings $l$ >>
  | Misctypes.NoBindings ->
       <:expr< Misctypes.NoBindings >>

let mlexpr_of_binding = mlexpr_of_pair mlexpr_of_binding_kind mlexpr_of_constr

let mlexpr_of_constr_with_binding =
  mlexpr_of_pair mlexpr_of_constr mlexpr_of_binding_kind

let mlexpr_of_constr_with_binding_arg =
  mlexpr_of_pair (mlexpr_of_option mlexpr_of_bool) mlexpr_of_constr_with_binding

let mlexpr_of_move_location f = function
  | Misctypes.MoveAfter id -> <:expr< Misctypes.MoveAfter $f id$ >>
  | Misctypes.MoveBefore id -> <:expr< Misctypes.MoveBefore $f id$ >>
  | Misctypes.MoveFirst -> <:expr< Misctypes.MoveFirst >>
  | Misctypes.MoveLast -> <:expr< Misctypes.MoveLast >>

let mlexpr_of_induction_arg = function
  | Tacexpr.ElimOnConstr c ->
      <:expr< Tacexpr.ElimOnConstr $mlexpr_of_constr_with_binding c$ >>
  | Tacexpr.ElimOnIdent (_,id) ->
      <:expr< Tacexpr.ElimOnIdent $dloc$ $mlexpr_of_ident id$ >>
  | Tacexpr.ElimOnAnonHyp n ->
      <:expr< Tacexpr.ElimOnAnonHyp $mlexpr_of_int n$ >>

let mlexpr_of_clause_pattern _ = failwith "mlexpr_of_clause_pattern: TODO"

let mlexpr_of_pattern_ast = mlexpr_of_constr

let mlexpr_of_entry_type = function
    _ -> failwith "mlexpr_of_entry_type: TODO"

let mlexpr_of_match_lazy_flag = function
  | Tacexpr.General -> <:expr<Tacexpr.General>>
  | Tacexpr.Select    -> <:expr<Tacexpr.Select>>
  | Tacexpr.Once    -> <:expr<Tacexpr.Once>>

let mlexpr_of_match_pattern = function
  | Tacexpr.Term t -> <:expr< Tacexpr.Term $mlexpr_of_pattern_ast t$ >>
  | Tacexpr.Subterm (b,ido,t) ->
      <:expr< Tacexpr.Subterm $mlexpr_of_bool b$ $mlexpr_of_option mlexpr_of_ident ido$ $mlexpr_of_pattern_ast t$ >>

let mlexpr_of_match_context_hyps = function
  | Tacexpr.Hyp (id,l) ->
      let f = mlexpr_of_located mlexpr_of_name in
      <:expr< Tacexpr.Hyp $f id$ $mlexpr_of_match_pattern l$ >>
  | Tacexpr.Def (id,v,l) ->
      let f = mlexpr_of_located mlexpr_of_name in
      <:expr< Tacexpr.Def $f id$ $mlexpr_of_match_pattern v$ $mlexpr_of_match_pattern l$ >>

let mlexpr_of_match_rule f = function
  | Tacexpr.Pat (l,mp,t) -> <:expr< Tacexpr.Pat $mlexpr_of_list mlexpr_of_match_context_hyps l$ $mlexpr_of_match_pattern mp$ $f t$ >>
  | Tacexpr.All t -> <:expr< Tacexpr.All $f t$ >>

let mlexpr_of_message_token = function
  | Tacexpr.MsgString s -> <:expr< Tacexpr.MsgString $str:s$ >>
  | Tacexpr.MsgInt n -> <:expr< Tacexpr.MsgInt $mlexpr_of_int n$ >>
  | Tacexpr.MsgIdent id -> <:expr< Tacexpr.MsgIdent $mlexpr_of_hyp id$ >>

let mlexpr_of_debug = function
  | Tacexpr.Off -> <:expr< Tacexpr.Off >>
  | Tacexpr.Debug -> <:expr< Tacexpr.Debug >>
  | Tacexpr.Info -> <:expr< Tacexpr.Info >>

let rec mlexpr_of_atomic_tactic = function
  (* Basic tactics *)
  | Tacexpr.TacIntroPattern pl ->
      let pl = mlexpr_of_list (mlexpr_of_located mlexpr_of_intro_pattern) pl in
      <:expr< Tacexpr.TacIntroPattern $pl$ >>
  | Tacexpr.TacIntroMove (idopt,idopt') ->
      let idopt = mlexpr_of_ident_option idopt in
      let idopt'= mlexpr_of_move_location mlexpr_of_hyp idopt' in
      <:expr< Tacexpr.TacIntroMove $idopt$ $idopt'$ >>
  | Tacexpr.TacExact c ->
      <:expr< Tacexpr.TacExact $mlexpr_of_constr c$ >>
  | Tacexpr.TacApply (b,false,cb,None) ->
      <:expr< Tacexpr.TacApply $mlexpr_of_bool b$ False $mlexpr_of_list mlexpr_of_constr_with_binding_arg cb$ None >>
  | Tacexpr.TacElim (false,cb,cbo) ->
      let cb = mlexpr_of_constr_with_binding_arg cb in
      let cbo = mlexpr_of_option mlexpr_of_constr_with_binding cbo in
      <:expr< Tacexpr.TacElim False $cb$ $cbo$ >>
  | Tacexpr.TacCase (false,cb) ->
      let cb = mlexpr_of_constr_with_binding_arg cb in
      <:expr< Tacexpr.TacCase False $cb$ >>
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

  | Tacexpr.TacAssert (b,t,ipat,c) ->
      let ipat = mlexpr_of_option (mlexpr_of_located mlexpr_of_intro_pattern) ipat in
      <:expr< Tacexpr.TacAssert $mlexpr_of_bool b$
              $mlexpr_of_option mlexpr_of_tactic t$ $ipat$
	      $mlexpr_of_constr c$ >>
  | Tacexpr.TacGeneralize cl ->
      <:expr< Tacexpr.TacGeneralize
	      $mlexpr_of_list
                (mlexpr_of_pair mlexpr_of_occ_constr mlexpr_of_name) cl$ >>
  | Tacexpr.TacGeneralizeDep c ->
      <:expr< Tacexpr.TacGeneralizeDep $mlexpr_of_constr c$ >>
  | Tacexpr.TacLetTac (na,c,cl,b,e) ->
      let na = mlexpr_of_name na in
      let cl = mlexpr_of_clause_pattern cl in
      <:expr< Tacexpr.TacLetTac $na$ $mlexpr_of_constr c$ $cl$
	      $mlexpr_of_bool b$
	      (mlexpr_of_option (mlexpr_of_located mlexpr_of_intro_pattern) e)
      >>

  (* Derived basic tactics *)
  | Tacexpr.TacInductionDestruct (isrec,ev,l) ->
      <:expr< Tacexpr.TacInductionDestruct $mlexpr_of_bool isrec$ $mlexpr_of_bool ev$
	$mlexpr_of_pair
	(mlexpr_of_list
	   (mlexpr_of_triple
	      (mlexpr_of_pair
                 (mlexpr_of_option mlexpr_of_bool)
                 mlexpr_of_induction_arg)
	      (mlexpr_of_pair
		 (mlexpr_of_option (mlexpr_of_located mlexpr_of_intro_pattern_naming))
		 (mlexpr_of_option (mlexpr_of_intro_pattern_disjunctive)))
	      (mlexpr_of_option mlexpr_of_clause)))
	(mlexpr_of_option mlexpr_of_constr_with_binding)
 l$ >>

  (* Context management *)
  | Tacexpr.TacClear (b,l) ->
      let l = mlexpr_of_list (mlexpr_of_hyp) l in
      <:expr< Tacexpr.TacClear $mlexpr_of_bool b$ $l$ >>
  | Tacexpr.TacClearBody l ->
      let l = mlexpr_of_list (mlexpr_of_hyp) l in
      <:expr< Tacexpr.TacClearBody $l$ >>
  | Tacexpr.TacMove (id1,id2) ->
      <:expr< Tacexpr.TacMove
              $mlexpr_of_hyp id1$
              $mlexpr_of_move_location mlexpr_of_hyp id2$ >>

  (* Constructors *)
  | Tacexpr.TacSplit (ev,l) ->
      <:expr< Tacexpr.TacSplit
        ($mlexpr_of_bool ev$, $mlexpr_of_list mlexpr_of_binding_kind l$)>>
  (* Conversion *)
  | Tacexpr.TacReduce (r,cl) ->
      let l = mlexpr_of_clause cl in
      <:expr< Tacexpr.TacReduce $mlexpr_of_red_expr r$ $l$ >>
  | Tacexpr.TacChange (p,c,cl) ->
      let l = mlexpr_of_clause cl in
      let g = mlexpr_of_option mlexpr_of_constr in
      <:expr< Tacexpr.TacChange $g p$ $mlexpr_of_constr c$ $l$ >>

  (* Equivalence relations *)
  | Tacexpr.TacSymmetry ido -> <:expr< Tacexpr.TacSymmetry $mlexpr_of_clause ido$ >>

  (* Automation tactics *)
  | Tacexpr.TacAuto (debug,n,lems,l) ->
      let d = mlexpr_of_debug debug in
      let n = mlexpr_of_option (mlexpr_of_or_var mlexpr_of_int) n in
      let lems = mlexpr_of_list mlexpr_of_constr lems in
      let l = mlexpr_of_option (mlexpr_of_list mlexpr_of_string) l in
      <:expr< Tacexpr.TacAuto $d$ $n$ $lems$ $l$ >>
  | Tacexpr.TacTrivial (debug,lems,l) ->
      let d = mlexpr_of_debug debug in
      let l = mlexpr_of_option (mlexpr_of_list mlexpr_of_string) l in
      let lems = mlexpr_of_list mlexpr_of_constr lems in
      <:expr< Tacexpr.TacTrivial $d$ $lems$ $l$ >>

  | _ -> failwith "Quotation of atomic tactic expressions: TODO"

and mlexpr_of_tactic : (Tacexpr.raw_tactic_expr -> MLast.expr) = function
  | Tacexpr.TacAtom (loc,t) ->
      let loc = of_coqloc loc in
      <:expr< Tacexpr.TacAtom $dloc$ $mlexpr_of_atomic_tactic t$ >>
  | Tacexpr.TacThen (t1,t2) ->
      <:expr< Tacexpr.TacThen $mlexpr_of_tactic t1$ $mlexpr_of_tactic t2$>>
  | Tacexpr.TacThens (t,tl) ->
      <:expr< Tacexpr.TacThens $mlexpr_of_tactic t$ $mlexpr_of_list mlexpr_of_tactic tl$>>
  | Tacexpr.TacFirst tl ->
      <:expr< Tacexpr.TacFirst $mlexpr_of_list mlexpr_of_tactic tl$ >>
  | Tacexpr.TacSolve tl ->
      <:expr< Tacexpr.TacSolve $mlexpr_of_list mlexpr_of_tactic tl$ >>
  | Tacexpr.TacTry t ->
      <:expr< Tacexpr.TacTry $mlexpr_of_tactic t$ >>
  | Tacexpr.TacOr (t1,t2) ->
      <:expr< Tacexpr.TacOr $mlexpr_of_tactic t1$ $mlexpr_of_tactic t2$ >>
  | Tacexpr.TacOrelse (t1,t2) ->
      <:expr< Tacexpr.TacOrelse $mlexpr_of_tactic t1$ $mlexpr_of_tactic t2$ >>
  | Tacexpr.TacDo (n,t) ->
      <:expr< Tacexpr.TacDo $mlexpr_of_or_var mlexpr_of_int n$ $mlexpr_of_tactic t$ >>
  | Tacexpr.TacTimeout (n,t) ->
      <:expr< Tacexpr.TacTimeout $mlexpr_of_or_var mlexpr_of_int n$ $mlexpr_of_tactic t$ >>
  | Tacexpr.TacRepeat t ->
      <:expr< Tacexpr.TacRepeat $mlexpr_of_tactic t$ >>
  | Tacexpr.TacProgress t ->
      <:expr< Tacexpr.TacProgress $mlexpr_of_tactic t$ >>
  | Tacexpr.TacShowHyps t ->
      <:expr< Tacexpr.TacShowHyps $mlexpr_of_tactic t$ >>
  | Tacexpr.TacId l ->
      <:expr< Tacexpr.TacId $mlexpr_of_list mlexpr_of_message_token l$ >>
  | Tacexpr.TacFail (g,n,l) ->
      <:expr< Tacexpr.TacFail $mlexpr_of_global_flag g$ $mlexpr_of_or_var mlexpr_of_int n$ $mlexpr_of_list mlexpr_of_message_token l$ >>
(*
  | Tacexpr.TacInfo t -> TacInfo (loc,f t)

  | Tacexpr.TacRec (id,(idl,t)) -> TacRec (loc,(id,(idl,f t)))
  | Tacexpr.TacRecIn (l,t) -> TacRecIn(loc,List.map (fun (id,t) -> (id,f t)) l,f t)
*)
  | Tacexpr.TacLetIn (isrec,l,t) ->
      let f =
	mlexpr_of_pair
	  (mlexpr_of_pair (fun _ -> dloc) mlexpr_of_ident)
	  mlexpr_of_tactic_arg in
      <:expr< Tacexpr.TacLetIn $mlexpr_of_bool isrec$ $mlexpr_of_list f l$ $mlexpr_of_tactic t$ >>
  | Tacexpr.TacMatch (lz,t,l) ->
      <:expr< Tacexpr.TacMatch
        $mlexpr_of_match_lazy_flag lz$
        $mlexpr_of_tactic t$
        $mlexpr_of_list (mlexpr_of_match_rule mlexpr_of_tactic) l$>>
  | Tacexpr.TacMatchGoal (lz,lr,l) ->
      <:expr< Tacexpr.TacMatchGoal
        $mlexpr_of_match_lazy_flag lz$
        $mlexpr_of_bool lr$
        $mlexpr_of_list (mlexpr_of_match_rule mlexpr_of_tactic) l$>>

  | Tacexpr.TacFun (idol,body) ->
      <:expr< Tacexpr.TacFun
        ($mlexpr_of_list mlexpr_of_ident_option idol$,
         $mlexpr_of_tactic body$) >>
  | Tacexpr.TacArg (_,Tacexpr.MetaIdArg (_,true,id)) -> anti loc id
  | Tacexpr.TacArg (_,t) ->
      <:expr< Tacexpr.TacArg $dloc$ $mlexpr_of_tactic_arg t$ >>
  | Tacexpr.TacComplete t ->
      <:expr< Tacexpr.TacComplete $mlexpr_of_tactic t$ >>
  | _ -> failwith "Quotation of tactic expressions: TODO"

and mlexpr_of_tactic_arg = function
  | Tacexpr.MetaIdArg (loc,true,id) ->
    let loc = of_coqloc loc in
    anti loc id
  | Tacexpr.MetaIdArg (loc,false,id) ->
    let loc = of_coqloc loc in
    <:expr< Tacexpr.ConstrMayEval (Genredexpr.ConstrTerm $anti loc id$) >>
  | Tacexpr.TacCall (loc,t,tl) ->
    let loc = of_coqloc loc in
    <:expr< Tacexpr.TacCall $dloc$ $mlexpr_of_reference t$ $mlexpr_of_list mlexpr_of_tactic_arg tl$>>
  | Tacexpr.Tacexp t ->
      <:expr< Tacexpr.Tacexp $mlexpr_of_tactic t$ >>
  | Tacexpr.ConstrMayEval c ->
      <:expr< Tacexpr.ConstrMayEval $mlexpr_of_may_eval mlexpr_of_constr c$ >>
  | Tacexpr.Reference r ->
      <:expr< Tacexpr.Reference $mlexpr_of_reference r$ >>
  | _ -> failwith "mlexpr_of_tactic_arg: TODO"


IFDEF CAMLP5 THEN

let not_impl x =
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  failwith ("<Q_coqast.patt_of_expt, not impl: " ^ desc)

(* The following function is written without quotation
   in order to be parsable even by camlp4. The version with
   quotation can be found in revision <= 12972 of [q_util.ml4] *)

open MLast

let rec patt_of_expr e =
  let loc = loc_of_expr e in
  match e with
    | ExAcc (_, e1, e2) -> PaAcc (loc, patt_of_expr e1, patt_of_expr e2)
    | ExApp (_, e1, e2) -> PaApp (loc, patt_of_expr e1, patt_of_expr e2)
    | ExLid (_, x) when x = vala "loc" -> PaAny loc
    | ExLid (_, s) -> PaLid (loc, s)
    | ExUid (_, s) -> PaUid (loc, s)
    | ExStr (_, s) -> PaStr (loc, s)
    | ExAnt (_, e) -> PaAnt (loc, patt_of_expr e)
    | _ -> not_impl e

let fconstr e =
  let ee s =
    mlexpr_of_constr (Pcoq.Gram.entry_parse e
			(Pcoq.Gram.parsable (Stream.of_string s)))
  in
  let ep s = patt_of_expr (ee s) in
  Quotation.ExAst (ee, ep)

let ftac e =
  let ee s =
    mlexpr_of_tactic (Pcoq.Gram.entry_parse e
			(Pcoq.Gram.parsable (Stream.of_string s)))
  in
  let ep s = patt_of_expr (ee s) in
  Quotation.ExAst (ee, ep)

let _ =
  Quotation.add "constr" (fconstr Pcoq.Constr.constr_eoi);
  Quotation.add "tactic" (ftac Pcoq.Tactic.tactic_eoi);
  Quotation.default := "constr"

ELSE

open Pcaml

let expand_constr_quot_expr loc _loc_name_opt contents =
  mlexpr_of_constr
    (Pcoq.Gram.parse_string Pcoq.Constr.constr_eoi loc contents)

let expand_tactic_quot_expr loc _loc_name_opt contents =
  mlexpr_of_tactic
    (Pcoq.Gram.parse_string Pcoq.Tactic.tactic_eoi loc contents)

let _ =
  (* FIXME: for the moment, we add quotations in expressions only, not pattern *)
  Quotation.add "constr" Quotation.DynAst.expr_tag expand_constr_quot_expr;
  Quotation.add "tactic" Quotation.DynAst.expr_tag expand_tactic_quot_expr;
  Quotation.default := "constr"

END
