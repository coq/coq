(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Ast
open Pcoq
open Util
open Tacexpr
open Rawterm
open Genarg
open Constr
open Prim
open Tactic

let tactic_kw =
  [ "using"; "Orelse"; "Proof"; "Qed"; "And"; "()"; "|-" ]
let _ =
  if !Options.v7 then
    List.iter (fun s -> Lexer.add_token ("",s)) tactic_kw

(* Functions overloaded by quotifier *)

let induction_arg_of_constr c =
  try ElimOnIdent (Topconstr.constr_loc c,snd (coerce_to_id c))
  with _ -> ElimOnConstr c

let local_compute = [FBeta;FIota;FDeltaBut [];FZeta]

let error_oldelim _ = error "OldElim no longer supported"

let join_to_constr loc c2 = (fst loc), snd (Topconstr.constr_loc c2)

(* Auxiliary grammar rules *)

if !Options.v7 then
GEXTEND Gram
  GLOBAL: simple_tactic constrarg bindings constr_with_bindings 
  quantified_hypothesis red_expr int_or_var castedopenconstr
  simple_intropattern;

  int_or_var:
    [ [ n = integer  -> Genarg.ArgArg n
      | id = identref -> Genarg.ArgVar id ] ]
  ;
  autoarg_depth:
  [ [ n = OPT natural -> n ] ]
  ;
  autoarg_adding:
  [ [ IDENT "Adding" ; "["; l = LIST1 global; "]" -> l | -> [] ] ]
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
  (* Either an hypothesis or a ltac ref (variable or pattern patvar) *)
  id_or_ltac_ref:
    [ [ id = base_ident -> AI (loc,id)
      | "?"; n = natural -> AI (loc,Pattern.patvar_of_int n) ] ]
  ;
  (* Either a global ref or a ltac ref (variable or pattern patvar) *)
  global_or_ltac_ref:
    [ [ qid = global -> qid
      | "?"; n = natural -> Libnames.Ident (loc,Pattern.patvar_of_int n) ] ]
  ;
  (* An identifier or a quotation meta-variable *)
  id_or_meta:
    [ [ id = identref -> AI id 

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
    [ [ IDENT "Inst"; id = identref; "["; c = constr; "]" ->
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
    [ [ id = base_ident -> NamedHyp id
      | n = natural -> AnonHyp n ] ]
  ;
  conversion:
    [ [ nl = LIST1 integer; c1 = constr; "with"; c2 = constr ->
         (Some (nl,c1), c2)
      |	c1 = constr; "with"; c2 = constr -> (Some ([],c1), c2)
      | c = constr -> (None, c) ] ]
  ;
  pattern_occ:
    [ [ nl = LIST0 integer; c = constr -> (nl,c) ] ]
  ;
  intropatterns:
    [ [ l = LIST0 simple_intropattern -> l ]]
  ;
  simple_intropattern:
    [ [ "["; tc = LIST1 intropatterns SEP "|" ; "]" -> IntroOrAndPattern tc
      | "("; tc = LIST1 simple_intropattern SEP "," ; ")" -> IntroOrAndPattern [tc]
      | IDENT "_" -> IntroWildcard
      | id = base_ident -> IntroIdentifier id
      ] ]
  ;
  simple_binding:
    [ [ id = base_ident; ":="; c = constr -> (loc, NamedHyp id, c)
      | n = natural; ":="; c = constr -> (loc, AnonHyp n, c) ] ]
  ;
  bindings:
    [ [ c1 = constr; ":="; c2 = constr; bl = LIST0 simple_binding ->
          ExplicitBindings
            ((join_to_constr loc c2,NamedHyp (snd(coerce_to_id c1)), c2) :: bl)
      | n = natural; ":="; c = constr; bl = LIST0 simple_binding ->
	  ExplicitBindings ((join_to_constr loc c,AnonHyp n, c) :: bl)
      | c1 = constr; bl = LIST0 constr ->
	  ImplicitBindings (c1 :: bl) ] ]
  ;
  constr_with_bindings:
    [ [ c = constr; l = with_bindings -> (c, l) ] ]
  ;
  with_bindings:
    [ [ "with"; bl = bindings -> bl | -> NoBindings ] ]
  ;
  unfold_occ:
    [ [ nl = LIST0 integer; c = global_or_ltac_ref -> (nl,c) ] ]
  ;
  red_flag:
    [ [ IDENT "Beta" -> FBeta
      | IDENT "Delta" -> FDeltaBut []
      | IDENT "Iota" -> FIota
      | IDENT "Zeta" -> FZeta
      | IDENT "Delta"; "["; idl = LIST1 global_or_ltac_ref; "]" -> FConst idl
      | IDENT "Delta"; "-"; "["; idl = LIST1 global_or_ltac_ref; "]" -> FDeltaBut idl
    ] ]
  ;
  red_tactic:
    [ [ IDENT "Red" -> Red false
      | IDENT "Hnf" -> Hnf
      | IDENT "Simpl"; po = OPT pattern_occ -> Simpl po
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
      | IDENT "Simpl"; po = OPT pattern_occ -> Simpl po
      | IDENT "Cbv"; s = LIST1 red_flag -> Cbv (make_red_flag s)
      | IDENT "Lazy"; s = LIST1 red_flag -> Lazy (make_red_flag s)
      | IDENT "Compute" -> Cbv (make_red_flag [FBeta;FIota;FDeltaBut [];FZeta])
      | IDENT "Unfold"; ul = LIST1 unfold_occ -> Unfold ul
      | IDENT "Fold"; cl = LIST1 constr -> Fold cl
      | IDENT "Pattern"; pl = LIST1 pattern_occ -> Pattern pl
      | s = IDENT -> ExtraRedExpr s ] ]
  ;
  hypident:
    [ [ id = id_or_meta -> id,[],(InHyp,ref None)
      | "("; "Type"; "of"; id = id_or_meta; ")" ->
          id,[],(InHypTypeOnly,ref None)
    ] ]
  ;
  clause:
    [ [ "in"; idl = LIST1 hypident ->
        {onhyps=Some idl;onconcl=false; concl_occs=[]}
      | -> {onhyps=Some[];onconcl=true;concl_occs=[]} ] ]
  ;
  simple_clause:
    [ [ "in"; idl = LIST1 id_or_meta -> idl
      | -> [] ] ]
  ;
  pattern_occ_hyp_tail_list:
    [ [ pl = pattern_occ_hyp_list -> pl
      | -> {onhyps=Some[];onconcl=false; concl_occs=[]} ] ]
  ;
  pattern_occ_hyp_list:
    [ [ nl = LIST1 natural; IDENT "Goal" ->
          {onhyps=Some[];onconcl=true;concl_occs=nl}
      | nl = LIST1 natural; id = id_or_meta; cls = pattern_occ_hyp_tail_list
        -> {cls with
            onhyps=option_app(fun l -> (id,nl,(InHyp,ref None))::l)
              cls.onhyps} 
      | IDENT "Goal" -> {onhyps=Some[];onconcl=true;concl_occs=[]}
      | id = id_or_meta; cls = pattern_occ_hyp_tail_list ->
         {cls with
          onhyps=option_app(fun l -> (id,[],(InHyp,ref None))::l)
            cls.onhyps} ] ]
  ;
  clause_pattern:
    [ [ "in"; p = pattern_occ_hyp_list -> p 
      | -> {onhyps=None; onconcl=true; concl_occs=[] } ] ]
  ;
  fixdecl:
    [ [ id = base_ident; "/"; n = natural; ":"; c = constr -> (id,n,c) ] ]
  ;
  cofixdecl:
    [ [ id = base_ident; ":"; c = constr -> (id,c) ] ]
  ;
  hintbases:
    [ [ "with"; "*" -> None
      | "with"; l = LIST1 IDENT -> Some l
      | -> Some [] ] ]
  ;
  eliminator:
    [ [ "using"; el = constr_with_bindings -> el ] ]
  ;
  with_names:
    [ [ "as"; ipat = simple_intropattern -> Some ipat | -> None ] ]
  ;
  simple_tactic:
    [ [ 
      (* Basic tactics *)
        IDENT "Intros"; IDENT "until"; id = quantified_hypothesis -> 
	  TacIntrosUntil id
      | IDENT "Intros"; pl = intropatterns -> TacIntroPattern pl
      | IDENT "Intro"; id = base_ident; IDENT "after"; id2 = identref ->
	  TacIntroMove (Some id, Some id2)
      | IDENT "Intro"; IDENT "after"; id2 = identref ->
	  TacIntroMove (None, Some id2)
      | IDENT "Intro"; id = base_ident -> TacIntroMove (Some id,None)
      | IDENT "Intro" -> TacIntroMove (None, None)

      | IDENT "Assumption" -> TacAssumption
      | IDENT "Exact"; c = constr -> TacExact c

      | IDENT "Apply"; cl = constr_with_bindings -> TacApply cl
      | IDENT "Elim"; cl = constr_with_bindings; el = OPT eliminator ->
          TacElim (cl,el)
      | IDENT "OldElim"; c = constr ->
	  (* TacOldElim c *) error_oldelim ()
      | IDENT "ElimType"; c = constr -> TacElimType c
      | IDENT "Case"; cl = constr_with_bindings -> TacCase cl
      | IDENT "CaseType"; c = constr -> TacCaseType c
      | IDENT "Fix"; n = natural -> TacFix (None,n)
      | IDENT "Fix"; id = base_ident; n = natural -> TacFix (Some id,n)
      | IDENT "Fix"; id = base_ident; n = natural; "with"; fd = LIST0 fixdecl ->
	  TacMutualFix (id,n,fd)
      | IDENT "Cofix" -> TacCofix None
      | IDENT "Cofix"; id = base_ident -> TacCofix (Some id)
      | IDENT "Cofix"; id = base_ident; "with"; fd = LIST0 cofixdecl ->
	  TacMutualCofix (id,fd)

      | IDENT "Cut"; c = constr -> TacCut c
      | IDENT "Assert"; c = constr -> TacTrueCut (Names.Anonymous,c)
      | IDENT "Assert"; c = constr; ":"; t = constr ->
          TacTrueCut (Names.Name (snd(coerce_to_id c)),t)
      | IDENT "Assert"; c = constr; ":="; b = constr ->
          TacForward (false,Names.Name (snd (coerce_to_id c)),b)
      | IDENT "Pose"; c = constr; ":="; b = constr ->
	  TacForward (true,Names.Name (snd(coerce_to_id c)),b)
      | IDENT "Pose"; b = constr -> TacForward (true,Names.Anonymous,b)
      | IDENT "Generalize"; lc = LIST1 constr -> TacGeneralize lc
      | IDENT "Generalize"; IDENT "Dependent"; c = constr -> TacGeneralizeDep c
      | IDENT "LetTac"; (_,na) = name; ":="; c = constr; p = clause_pattern
        -> TacLetTac (na,c,p)
      | IDENT "Instantiate"; n = natural; c = constr; cls = clause -> 
	    TacInstantiate (n,c,cls)
      | IDENT "Specialize"; n = OPT natural; lcb = constr_with_bindings ->
	  TacSpecialize (n,lcb)
      | IDENT "LApply"; c = constr -> TacLApply c

      (* Derived basic tactics *)
      | IDENT "Induction"; h = quantified_hypothesis -> TacSimpleInduction (h,ref [])
      | IDENT "NewInduction"; c = induction_arg; el = OPT eliminator;
          ids = with_names -> TacNewInduction (c,el,(ids,ref []))
      | IDENT "Double"; IDENT "Induction"; h1 = quantified_hypothesis;
	  h2 = quantified_hypothesis -> TacDoubleInduction (h1,h2)
      | IDENT "Destruct"; h = quantified_hypothesis -> TacSimpleDestruct h
      | IDENT "NewDestruct"; c = induction_arg; el = OPT eliminator; 
          ids = with_names -> TacNewDestruct (c,el,(ids,ref []))
      | IDENT "Decompose"; IDENT "Record" ; c = constr -> TacDecomposeAnd c
      | IDENT "Decompose"; IDENT "Sum"; c = constr -> TacDecomposeOr c
      | IDENT "Decompose"; "["; l = LIST1 global_or_ltac_ref; "]"; c = constr
        -> TacDecompose (l,c)

      (* Automation tactic *)
      | IDENT "Trivial"; db = hintbases -> TacTrivial db
      | IDENT "Auto"; n = OPT natural; db = hintbases -> TacAuto (n, db)

      | IDENT "AutoTDB"; n = OPT natural -> TacAutoTDB n
      | IDENT "CDHyp"; id = identref -> TacDestructHyp (true,id)
      | IDENT "DHyp";  id = identref -> TacDestructHyp (false,id)
      | IDENT "DConcl"  -> TacDestructConcl
      | IDENT "SuperAuto"; l = autoargs -> TacSuperAuto l
      | IDENT "Auto"; n = OPT natural; IDENT "Decomp"; p = OPT natural ->
	  TacDAuto (n, p)

      (* Context management *)
      | IDENT "Clear"; l = LIST1 id_or_ltac_ref -> TacClear l
      | IDENT "ClearBody"; l = LIST1 id_or_ltac_ref -> TacClearBody l
      | IDENT "Move"; id1 = id_or_ltac_ref; IDENT "after"; 
	  id2 = id_or_ltac_ref -> TacMove (true,id1,id2)
      | IDENT "Rename"; id1 = id_or_ltac_ref; IDENT "into"; 
	  id2 = id_or_ltac_ref -> TacRename (id1,id2)

      (* Constructors *)
      | IDENT "Left"; bl = with_bindings -> TacLeft bl
      | IDENT "Right"; bl = with_bindings -> TacRight bl
      | IDENT "Split"; bl = with_bindings -> TacSplit (false,bl)
      | IDENT "Exists"; bl = bindings -> TacSplit (true,bl)
      | IDENT "Exists" -> TacSplit (true,NoBindings)
      | IDENT "Constructor"; n = num_or_meta; l = with_bindings ->
	  TacConstructor (n,l)
      | IDENT "Constructor"; t = OPT tactic -> TacAnyConstructor t

      (* Equivalence relations *)
      | IDENT "Reflexivity" -> TacReflexivity
      | IDENT "Symmetry"; cls = clause -> TacSymmetry cls
      | IDENT "Transitivity"; c = constr -> TacTransitivity c

      (* Equality and inversion *)
      | IDENT "Dependent"; k =
	  [ IDENT "Simple"; IDENT "Inversion" -> SimpleInversion
	  | IDENT "Inversion" -> FullInversion
	  | IDENT "Inversion_clear" -> FullInversionClear ];
	  hyp = quantified_hypothesis; 
	  ids = with_names; co = OPT ["with"; c = constr -> c] ->
	    TacInversion (DepInversion (k,co,ids),hyp)
      | IDENT "Simple"; IDENT "Inversion";
	  hyp = quantified_hypothesis; ids = with_names; cl = simple_clause ->
	    TacInversion (NonDepInversion (SimpleInversion, cl, ids), hyp)
      | IDENT "Inversion"; 
	  hyp = quantified_hypothesis; ids = with_names; cl = simple_clause ->
	    TacInversion (NonDepInversion (FullInversion, cl, ids), hyp)
      | IDENT "Inversion_clear"; 
	  hyp = quantified_hypothesis; ids = with_names; cl = simple_clause ->
	    TacInversion (NonDepInversion (FullInversionClear, cl, ids), hyp)
      | IDENT "Inversion"; hyp = quantified_hypothesis; 
	  "using"; c = constr; cl = simple_clause ->
	    TacInversion (InversionUsing (c,cl), hyp)

      (* Conversion *)
      | r = red_tactic; cl = clause -> TacReduce (r, cl)
      (* Change ne doit pas s'appliquer dans un Definition t := Eval ... *)
      | IDENT "Change"; (oc,c) = conversion; cl = clause -> TacChange (oc,c,cl)

    ] ]
  ;
END;;
