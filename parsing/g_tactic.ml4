(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Ast
open Pcoq
open Util
open Tacexpr
open Rawterm

(* open grammar entries, possibly in quotified form *)
ifdef Quotify then open Qast

open Constr
open Prim
open Tactic

(* Functions overloaded by quotifier *)

let induction_arg_of_constr c =
  try ElimOnIdent (Ast.loc c,coerce_to_id c) with _ -> ElimOnConstr c

let local_compute = [FBeta;FIota;FDeltaBut [];FZeta]

let error_oldelim _ = error "OldElim no longer supported"

ifdef Quotify then
  let induction_arg_of_constr = function
  | Qast.Node ("Nvar", [_;id]) -> Qast.Node ("ElimOnIdent", [id])
  | c -> Qast.Node ("ElimOnConstr", [c])

ifdef Quotify then
let make_red_flag s = Qast.Apply ("make_red_flag", [s])

ifdef Quotify then
let local_compute = 
  Qast.List [
    Qast.Node ("FBeta", []);
    Qast.Node ("FDeltaBut", [Qast.List []]);
    Qast.Node ("FIota", []);
    Qast.Node ("FZeta", [])]

(*
  let
    {rBeta = b; rIota = i; rZeta = z; rDelta = d; rConst = l} = make_red_flag s
  in
  let quotify_ident id =
    Qast.Apply ("Names.id_of_string", [Qast.Str (Names.string_of_id id)])
  in
  let quotify_path sp =
    let dir, id = Names.repr_path sp in
    let l = Names.repr_dirpath dir in
    Qast.Apply ("Names.make_path",
      [Qast.Apply ("Names.make_dirpath",
        [Qast.List (List.map quotify_ident l)]);
      quotify_ident id]) in
  Qast.Record 
    ["rBeta",Qast.Bool b; "rIota",Qast.Bool i;
     "rZeta",Qast.Bool z; "rDelta",Qast.Bool d;
     "rConst",Qast.List (List.map quotify_path l)]
*)
ifdef Quotify then open Q

(* Please leave several GEXTEND for modular compilation under PowerPC *)

(* Auxiliary grammar rules *)

GEXTEND Gram
  GLOBAL: simple_tactic constrarg constr_with_bindings quantified_hypothesis
    red_expr int_or_var castedopenconstr;

  int_or_var:
    [ [ n = integer  -> Genarg.ArgArg n
      | id = ident -> Genarg.ArgVar (loc,id) ] ]
  ;
  autoarg_depth:
  [ [ n = OPT natural -> n ] ]
  ;
  autoarg_adding:
  [ [ IDENT "Adding" ; "["; l = LIST1 qualid; "]" -> l | -> [] ] ]
  ;
  autoarg_destructing:
  [ [ IDENT "Destructing" -> true | -> false ] ]
  ;
  autoarg_usingTDB:
  [ [ "Using"; "TDB"  -> true | -> false ] ]
  ;
  autoargs:
  [ [ a0 = autoarg_depth; l = autoarg_adding; 
      a2 = autoarg_destructing; a3 = autoarg_usingTDB -> (a0,l,a2,a3) ] ]
  ;
  (* Either an hypothesis or a ltac ref (variable or pattern metavariable) *)
  id_or_ltac_ref:
    [ [ id = ident -> AN (loc,id)
      | "?"; n = natural -> MetaNum (loc,n) ] ]
  ;
  (* Either a global ref or a ltac ref (variable or pattern metavariable) *)
  qualid_or_ltac_ref:
    [ [ (loc,qid) = qualid -> AN (loc,qid)
      | "?"; n = natural -> MetaNum (loc,n) ] ]
  ;
  (* An identifier or a quotation meta-variable *)
  id_or_meta:
    [ [ id = rawident -> AI id 

      (* This is used in quotations *)
      | id = METAIDENT -> MetaId (loc,id) ] ]
  ;
  (* A number or a quotation meta-variable *)
  num_or_meta:
    [ [ n = integer -> AI n
      |	id = METAIDENT -> MetaId (loc,id)
      ] ]
  ;
  constrarg:
    [ [ IDENT "Inst"; id = rawident; "["; c = constr; "]" ->
        ConstrContext (id, c)
      | IDENT "Eval"; rtc = Tactic.red_expr; "in"; c = constr ->
        ConstrEval (rtc,c) 
      | IDENT "Check"; c = constr -> ConstrTypeOf c
      | c = constr -> ConstrTerm c ] ]
  ;
  castedopenconstr:
    [ [ c = constr -> c ] ]
  ;
  induction_arg:
    [ [ n = natural -> ElimOnAnonHyp n
      | c = constr -> induction_arg_of_constr c
    ] ]
  ;
  quantified_hypothesis:
    [ [ id = ident -> NamedHyp id
      | n = natural -> AnonHyp n ] ]
  ;
  pattern_occ:
    [ [ nl = LIST0 integer; c = constr -> (nl,c) ] ]
  ;
  pattern_occ_hyp_list:
    [ [ nl = LIST1 natural; IDENT "Goal" -> (Some nl,[])
      | nl = LIST1 natural; id = id_or_meta; (g,l) = pattern_occ_hyp_list ->
	  (g,(id,nl)::l)
      | IDENT "Goal" -> (Some [],[])
      | id = id_or_meta; (g,l) = pattern_occ_hyp_list -> (g,(id,[])::l) ] ]
  ;
  clause_pattern:
    [ [ "in"; p = pattern_occ_hyp_list -> p | -> None, [] ] ]
  ;
  intropatterns:
    [ [ l = LIST0 simple_intropattern -> l ]]
  ;
  simple_intropattern:
    [ [ "["; tc = LIST1 intropatterns SEP "|" ; "]" -> IntroOrAndPattern tc
      | "("; tc = LIST1 simple_intropattern SEP "," ; ")" -> IntroOrAndPattern [tc]
      | IDENT "_" -> IntroWildcard
      | id = ident -> IntroIdentifier id
      ] ]
  ;
  simple_binding:
    [ [ id = ident; ":="; c = constr -> (NamedHyp id, c)
      | n = natural; ":="; c = constr -> (AnonHyp n, c) ] ]
  ;
  binding_list:
    [ [ c1 = constr; ":="; c2 = constr; bl = LIST0 simple_binding ->
          ExplicitBindings ((NamedHyp (coerce_to_id c1), c2) :: bl)
      | n = natural; ":="; c = constr; bl = LIST0 simple_binding ->
	  ExplicitBindings ((AnonHyp n, c) :: bl)
      | c1 = constr; bl = LIST0 constr ->
	  ImplicitBindings (c1 :: bl) ] ]
  ;
  constr_with_bindings:
    [ [ c = constr; l = with_binding_list -> (c, l) ] ]
  ;
  with_binding_list:
    [ [ "with"; bl = binding_list -> bl | -> NoBindings ] ]
  ;
  unfold_occ:
    [ [ nl = LIST0 integer; c = qualid_or_ltac_ref -> (nl,c) ] ]
  ;
  red_flag:
    [ [ IDENT "Beta" -> FBeta
      | IDENT "Delta" -> FDeltaBut []
      | IDENT "Iota" -> FIota
      | IDENT "Zeta" -> FZeta
      | IDENT "Delta"; "["; idl = LIST1 qualid_or_ltac_ref; "]" -> FConst idl
      | IDENT "Delta"; "-"; "["; idl = LIST1 qualid_or_ltac_ref; "]" -> FDeltaBut idl
    ] ]
  ;
  red_tactic:
    [ [ IDENT "Red" -> Red false
      | IDENT "Hnf" -> Hnf
      | IDENT "Simpl" -> Simpl
      | IDENT "Cbv"; s = LIST1 red_flag -> Cbv (make_red_flag s)
      | IDENT "Lazy"; s = LIST1 red_flag -> Lazy (make_red_flag s)
      | IDENT "Compute" -> Cbv (make_red_flag [FBeta;FIota;FDeltaBut [];FZeta])
      | IDENT "Unfold"; ul = LIST1 unfold_occ -> Unfold ul
      | IDENT "Fold"; cl = LIST1 constr -> Fold cl
      | IDENT "Pattern"; pl = LIST1 pattern_occ -> Pattern pl ] ]
  ;
  (* This is [red_tactic] including possible extensions *)
  red_expr:
    [ [ IDENT "Red" -> Red false
      | IDENT "Hnf" -> Hnf
      | IDENT "Simpl" -> Simpl
      | IDENT "Cbv"; s = LIST1 red_flag -> Cbv (make_red_flag s)
      | IDENT "Lazy"; s = LIST1 red_flag -> Lazy (make_red_flag s)
      | IDENT "Compute" -> Cbv (make_red_flag [FBeta;FIota;FDeltaBut [];FZeta])
      | IDENT "Unfold"; ul = LIST1 unfold_occ -> Unfold ul
      | IDENT "Fold"; cl = LIST1 constr -> Fold cl
      | IDENT "Pattern"; pl = LIST1 pattern_occ -> Pattern pl
      | s = IDENT; c = constr -> ExtraRedExpr (s,c) ] ]
  ;
  hypident:
    [ [ id = id_or_meta -> InHyp id
      | "("; "Type"; "of"; id = id_or_meta; ")" -> InHypType id ] ]
  ;
  clause:
    [ [ "in"; idl = LIST1 hypident -> idl
      | -> [] ] ]
  ;
  fixdecl:
    [ [ id = ident; "/"; n = natural; ":"; c = constr -> (id,n,c) ] ]
  ;
  cofixdecl:
    [ [ id = ident; ":"; c = constr -> (id,c) ] ]
  ;
  hintbases:
    [ [ "with"; "*" -> None
      | "with"; l = LIST1 IDENT -> Some l
      | -> Some [] ] ]
  ;
  simple_tactic:
    [ [ 
      (* Basic tactics *)
        IDENT "Intros"; IDENT "until"; id = quantified_hypothesis -> 
	  TacIntrosUntil id
      | IDENT "Intros"; pl = intropatterns -> TacIntroPattern pl
      | IDENT "Intro"; id = ident; IDENT "after"; id2 = rawident ->
	  TacIntroMove (Some id, Some id2)
      | IDENT "Intro"; IDENT "after"; id2 = rawident ->
	  TacIntroMove (None, Some id2)
      | IDENT "Intro"; id = ident -> TacIntroMove (Some id, None)
      | IDENT "Intro" -> TacIntroMove (None, None)

      | IDENT "Assumption" -> TacAssumption
      | IDENT "Exact"; c = constr -> TacExact c

      | IDENT "Apply"; cl = constr_with_bindings -> TacApply cl
      | IDENT "Elim"; cl = constr_with_bindings; "using";
        el = constr_with_bindings -> TacElim (cl,Some el)
      | IDENT "Elim"; cl = constr_with_bindings -> TacElim (cl,None)
      | IDENT "OldElim"; c = constr ->
	  (* TacOldElim c *) error_oldelim ()
      | IDENT "ElimType"; c = constr -> TacElimType c
      | IDENT "Case"; cl = constr_with_bindings -> TacCase cl
      | IDENT "CaseType"; c = constr -> TacCaseType c
      | IDENT "Fix"; n = natural -> TacFix (None,n)
      | IDENT "Fix"; id = ident; n = natural -> TacFix (Some id,n)
      | IDENT "Fix"; id = ident; n = natural; "with"; fd = LIST0 fixdecl ->
	  TacMutualFix (id,n,fd)
      | IDENT "Cofix" -> TacCofix None
      | IDENT "Cofix"; id = ident -> TacCofix (Some id)
      | IDENT "Cofix"; id = ident; "with"; fd = LIST0 cofixdecl ->
	  TacMutualCofix (id,fd)

      | IDENT "Cut"; c = constr -> TacCut c
      | IDENT "Assert"; c = constr -> TacTrueCut (None,c)
      | IDENT "Assert"; c = constr; ":"; t = constr ->
          TacTrueCut (Some (coerce_to_id c),t)
      | IDENT "Assert"; c = constr; ":="; b = constr ->
          TacForward (false,Names.Name (coerce_to_id c),b)
      | IDENT "Pose"; c = constr; ":="; b = constr ->
	  TacForward (true,Names.Name (coerce_to_id c),b)
      | IDENT "Pose"; b = constr -> TacForward (true,Names.Anonymous,b)
      | IDENT "Generalize"; lc = LIST1 constr -> TacGeneralize lc
      | IDENT "Generalize"; IDENT "Dependent"; c = constr -> TacGeneralizeDep c
      | IDENT "LetTac"; id = ident; ":="; c = constr; p = clause_pattern
        -> TacLetTac (id,c,p)
      | IDENT "Instantiate"; n = natural; c = constr -> TacInstantiate (n,c)

      | IDENT "Specialize"; n = OPT natural; lcb = constr_with_bindings ->
	  TacSpecialize (n,lcb)
      | IDENT "LApply"; c = constr -> TacLApply c

      (* Derived basic tactics *)
      | IDENT "Induction"; h = quantified_hypothesis -> TacOldInduction h
      | IDENT "NewInduction"; c = induction_arg -> TacNewInduction c
      | IDENT "Double"; IDENT "Induction"; h1 = quantified_hypothesis;
	  h2 = quantified_hypothesis -> TacDoubleInduction (h1,h2)
      | IDENT "Destruct"; h = quantified_hypothesis -> TacOldDestruct h
      | IDENT "NewDestruct"; c = induction_arg -> TacNewDestruct c
      | IDENT "Decompose"; IDENT "Record" ; c = constr -> TacDecomposeAnd c
      | IDENT "Decompose"; IDENT "Sum"; c = constr -> TacDecomposeOr c
      | IDENT "Decompose"; "["; l = LIST1 qualid_or_ltac_ref; "]"; c = constr
        -> TacDecompose (l,c)

      (* Automation tactic *)
      | IDENT "Trivial"; db = hintbases -> TacTrivial db
      | IDENT "Auto"; n = OPT natural; db = hintbases -> TacAuto (n, db)

      | IDENT "AutoTDB"; n = OPT natural -> TacAutoTDB n
      | IDENT "CDHyp"; id = rawident -> TacDestructHyp (true,id)
      | IDENT "DHyp";  id = rawident -> TacDestructHyp (false,id)
      | IDENT "DConcl"  -> TacDestructConcl
      | IDENT "SuperAuto"; l = autoargs -> TacSuperAuto l
      | IDENT "Auto"; n = OPT natural; IDENT "Decomp"; p = OPT natural ->
	  TacDAuto (n, p)

      (* Context management *)
      | IDENT "Clear"; l = LIST1 id_or_ltac_ref -> TacClear l
      | IDENT "ClearBody"; l = LIST1 id_or_ltac_ref -> TacClearBody l
      | IDENT "Move"; id1 = rawident; IDENT "after"; id2 = rawident -> 
	  TacMove (true,id1,id2)
      | IDENT "Rename"; id1 = rawident; IDENT "into"; id2 = rawident -> 
	  TacRename (id1,id2)

      (* Constructors *)
      | IDENT "Left"; bl = with_binding_list -> TacLeft bl
      | IDENT "Right"; bl = with_binding_list -> TacRight bl
      | IDENT "Split"; bl = with_binding_list -> TacSplit bl
      | IDENT "Exists"; bl = binding_list -> TacSplit bl
      | IDENT "Exists" -> TacSplit NoBindings
      | IDENT "Constructor"; n = num_or_meta; l = with_binding_list ->
	  TacConstructor (n,l)
      | IDENT "Constructor"; t = OPT tactic -> TacAnyConstructor t

      (* Equivalence relations *)
      | IDENT "Reflexivity" -> TacReflexivity
      | IDENT "Symmetry" -> TacSymmetry
      | IDENT "Transitivity"; c = constr -> TacTransitivity c

      (* Conversion *)
      | r = red_tactic; cl = clause -> TacReduce (r, cl)
      (* Change ne doit pas s'appliquer dans un Definition t := Eval ... *)
      | IDENT "Change"; c = constr; cl = clause -> TacChange (c,cl)

(* Unused ??
      | IDENT "ML"; s = string -> ExtraTactic<:ast< (MLTACTIC $s) >>
*)

 (*   | [ id = identarg; l = constrarg_list ->
          match (isMeta (nvar_of_ast id), l) with
            | (true, []) -> id
            | (false, _) -> <:ast< (CALL $id ($LIST $l)) >>
            | _ -> Util.user_err_loc
                  (loc, "G_tactic.meta_tactic",
                   (str"Cannot apply arguments to a meta-tactic."))
      ] *)] ]
  ;
END;;
