(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Ast
open Pcoq
open Util
open Tacexpr
open Rawterm
open Genarg

let tactic_kw =
  [ "->"; "<-" ]
let _ = 
  if not !Options.v7 then
    List.iter (fun s -> Lexer.add_token("",s)) tactic_kw

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let lpar_id_coloneq =
  Gram.Entry.of_parser "lpar_id_coloneq"
    (fun strm ->
      match Stream.npeek 3 strm with
	| [("","("); ("IDENT",s); ("", ":=")] ->
            Stream.junk strm; Stream.junk strm; Stream.junk strm;
            Names.id_of_string s
	| _ -> raise Stream.Failure)

(* idem for (x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  Gram.Entry.of_parser "test_lpar_idnum_coloneq"
    (fun strm ->
      match Stream.npeek 3 strm with
        | [("","("); (("IDENT"|"INT"),_); ("", ":=")] -> ()
        | _ -> raise Stream.Failure)

(* idem for (x:t) *)
let lpar_id_colon =
  Gram.Entry.of_parser "test_lpar_id_colon"
    (fun strm ->
      match Stream.npeek 3 strm with
        | [("","("); ("IDENT",id); ("", ":")] ->
            Stream.junk strm; Stream.junk strm; Stream.junk strm;
            Names.id_of_string id
        | _ -> raise Stream.Failure)

(* open grammar entries, possibly in quotified form *)
ifdef Quotify then open Qast

open Constr
open Prim
open Tactic

let mk_fix_tac (loc,id,bl,ann,ty) =
  let n =
    match bl,ann with
        [([_],_)], None -> 0
      | _, Some x ->
          let ids = List.map snd (List.flatten (List.map fst bl)) in
          (try list_index (snd x) ids
          with Not_found -> error "no such fix variable")
      | _ -> error "cannot guess decreasing argument of fix" in
  (id,n,Topconstr.CProdN(loc,bl,ty))

let mk_cofix_tac (loc,id,bl,ann,ty) =
  let _ = option_app (fun (aloc,_) ->
    Util.user_err_loc
      (aloc,"Constr:mk_cofix_tac",
       Pp.str"Annotation forbidden in cofix expression")) ann in
  (id,Topconstr.CProdN(loc,bl,ty))

(* Functions overloaded by quotifier *)
let induction_arg_of_constr c =
  try ElimOnIdent (Topconstr.constr_loc c,coerce_to_id c)
  with _ -> ElimOnConstr c

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

ifdef Quotify then open Q

let join_to_constr loc c2 = (fst loc), snd (Topconstr.constr_loc c2)

(* Auxiliary grammar rules *)

if not !Options.v7 then
GEXTEND Gram
  GLOBAL: simple_tactic constrarg constr_with_bindings quantified_hypothesis
    red_expr int_or_var castedopenconstr;

  int_or_var:
    [ [ n = integer  -> Genarg.ArgArg n
      | id = identref -> Genarg.ArgVar id ] ]
  ;
  autoarg_depth:
  [ [ n = OPT natural -> n ] ]
  ;
  autoarg_adding:
  [ [ IDENT "adding" ; "["; l = LIST1 global; "]" -> l | -> [] ] ]
  ;
  autoarg_destructing:
  [ [ IDENT "destructing" -> true | -> false ] ]
  ;
  autoarg_usingTDB:
  [ [ "using"; "tdb"  -> true | -> false ] ]
  ;
  autoargs:
  [ [ a0 = autoarg_depth; l = autoarg_adding; 
      a2 = autoarg_destructing; a3 = autoarg_usingTDB -> (a0,l,a2,a3) ] ]
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
    [ [ IDENT "inst"; id = identref; "["; c = Constr.lconstr; "]" ->
        ConstrContext (id, c)
      | IDENT "eval"; rtc = Tactic.red_expr; "in"; c = Constr.constr ->
        ConstrEval (rtc,c) 
      | IDENT "check"; c = Constr.constr -> ConstrTypeOf c
      | c = Constr.lconstr -> ConstrTerm c ] ]
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
    [ [ c = constr -> (None, c)
      | c1 = constr; "with"; c2 = constr -> (Some ([],c1), c2)
      | c1 = constr; IDENT "at"; nl = LIST1 integer; "with"; c2 = constr ->
	  (Some (nl,c1), c2) ] ]
  ;
  pattern_occ:
    [ [ c = constr; nl = LIST0 integer -> (nl,c) ] ]
  ;
  pattern_occ_hyp_tail_list:
    [ [ pl = pattern_occ_hyp_list -> pl | -> (None,[]) ] ]
  ;
  pattern_occ_hyp_list:
    [ [ nl = LIST1 natural; IDENT "Goal" -> (Some nl,[])
      | nl = LIST1 natural; id = id_or_meta; (g,l) = pattern_occ_hyp_tail_list
	  -> (g,(id,nl)::l)
      | IDENT "Goal" -> (Some [],[])
      | id = id_or_meta; (g,l) = pattern_occ_hyp_tail_list -> (g,(id,[])::l)
    ] ]
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
      | "_" -> IntroWildcard
      | id = base_ident -> IntroIdentifier id
      ] ]
  ;
  simple_binding:
    [ [ "("; id = base_ident; ":="; c = lconstr; ")" -> (loc, NamedHyp id, c)
      | "("; n = natural; ":="; c = lconstr; ")" -> (loc, AnonHyp n, c) ] ]
  ;
  binding_list:
    [ [ test_lpar_idnum_coloneq; bl = LIST1 simple_binding ->
          ExplicitBindings bl
      | bl = LIST1 constr -> ImplicitBindings bl ] ]
  ;
  constr_with_bindings:
    [ [ c = constr; l = with_binding_list -> (c, l) ] ]
  ;
  with_binding_list:
    [ [ "with"; bl = binding_list -> bl | -> NoBindings ] ]
  ;
  unfold_occ:
    [ [ c = global; nl = LIST0 integer -> (nl,c) ] ]
  ;
  red_flag:
    [ [ IDENT "beta" -> FBeta
      | IDENT "delta" -> FDeltaBut []
      | IDENT "iota" -> FIota
      | IDENT "zeta" -> FZeta
      | IDENT "delta"; "["; idl = LIST1 global; "]" -> FConst idl
      | IDENT "delta"; "-"; "["; idl = LIST1 global; "]" -> FDeltaBut idl
    ] ]
  ;
  red_tactic:
    [ [ IDENT "red" -> Red false
      | IDENT "hnf" -> Hnf
      | IDENT "simpl"; po = OPT pattern_occ -> Simpl po
      | IDENT "cbv"; s = LIST1 red_flag -> Cbv (make_red_flag s)
      | IDENT "lazy"; s = LIST1 red_flag -> Lazy (make_red_flag s)
      | IDENT "compute" -> Cbv (make_red_flag [FBeta;FIota;FDeltaBut [];FZeta])
      | IDENT "unfold"; ul = LIST1 unfold_occ SEP "," -> Unfold ul
      | IDENT "fold"; cl = LIST1 constr -> Fold cl
      | IDENT "pattern"; pl = LIST1 pattern_occ SEP "," -> Pattern pl ] ]
  ;
  (* This is [red_tactic] including possible extensions *)
  red_expr:
    [ [ IDENT "red" -> Red false
      | IDENT "hnf" -> Hnf
      | IDENT "simpl"; po = OPT pattern_occ -> Simpl po
      | IDENT "cbv"; s = LIST1 red_flag -> Cbv (make_red_flag s)
      | IDENT "lazy"; s = LIST1 red_flag -> Lazy (make_red_flag s)
      | IDENT "compute" -> Cbv (make_red_flag [FBeta;FIota;FDeltaBut [];FZeta])
      | IDENT "unfold"; ul = LIST1 unfold_occ -> Unfold ul
      | IDENT "fold"; cl = LIST1 constr -> Fold cl
      | IDENT "pattern"; pl = LIST1 pattern_occ -> Pattern pl
      | s = IDENT; c = constr -> ExtraRedExpr (s,c) ] ]
  ;
  hypident:
    [ [ id = id_or_meta -> InHyp id
      | "("; IDENT "type"; "of"; id = id_or_meta; ")" -> InHypType id ] ]
  ;
  clause:
    [ [ "in"; idl = LIST1 hypident -> idl
      | -> [] ] ]
  ;
  simple_clause:
    [ [ "in"; idl = LIST1 id_or_meta -> idl
      | -> [] ] ]
  ;
  fixdecl:
    [ [ id = base_ident; bl=LIST0 Constr.binder; ann=fixannot;
        ":"; ty=lconstr -> (loc,id,bl,ann,ty) ] ]
  ;
  fixannot:
    [ [ "{"; IDENT "struct"; id=name; "}" -> Some id
      | -> None ] ]
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
    [ [ "as"; "["; ids = LIST1 (LIST0 simple_intropattern) SEP "|"; "]" -> ids
      | -> [] ] ]
  ;
  simple_tactic:
    [ [ 
      (* Basic tactics *)
        IDENT "intros"; IDENT "until"; id = quantified_hypothesis -> 
	  TacIntrosUntil id
      | IDENT "intros"; pl = intropatterns -> TacIntroPattern pl
      | IDENT "intro"; id = base_ident; IDENT "after"; id2 = identref ->
	  TacIntroMove (Some id, Some id2)
      | IDENT "intro"; IDENT "after"; id2 = identref ->
	  TacIntroMove (None, Some id2)
      | IDENT "intro"; id = base_ident -> TacIntroMove (Some id, None)
      | IDENT "intro" -> TacIntroMove (None, None)

      | IDENT "assumption" -> TacAssumption
      | IDENT "exact"; c = constr -> TacExact c

      | IDENT "apply"; cl = constr_with_bindings -> TacApply cl
      | IDENT "elim"; cl = constr_with_bindings; el = OPT eliminator ->
          TacElim (cl,el)
      | IDENT "elimtype"; c = constr -> TacElimType c
      | IDENT "case"; cl = constr_with_bindings -> TacCase cl
      | IDENT "casetype"; c = constr -> TacCaseType c
      | "fix"; n = natural -> TacFix (None,n)
      | "fix"; id = base_ident; n = natural -> TacFix (Some id,n)
      | "fix"; id = base_ident; n = natural; "with"; fd = LIST0 fixdecl ->
	  TacMutualFix (id,n,List.map mk_fix_tac fd)
      | "cofix" -> TacCofix None
      | "cofix"; id = base_ident -> TacCofix (Some id)
      | "cofix"; id = base_ident; "with"; fd = LIST0 fixdecl ->
	  TacMutualCofix (id,List.map mk_cofix_tac fd)

      | IDENT "cut"; c = constr -> TacCut c
      | IDENT "assert"; id = lpar_id_colon; t = lconstr; ")" ->
          TacTrueCut (Some id,t)
      | IDENT "assert"; id = lpar_id_coloneq; b = lconstr; ")" ->
          TacForward (false,Names.Name id,b)
      | IDENT "assert"; c = constr -> TacTrueCut (None,c)
      | IDENT "pose"; id = lpar_id_coloneq; b = lconstr; ")" ->
	  TacForward (true,Names.Name id,b)
      | IDENT "pose"; b = constr -> TacForward (true,Names.Anonymous,b)
      | IDENT "generalize"; lc = LIST1 constr -> TacGeneralize lc
      | IDENT "generalize"; IDENT "dependent"; c = constr ->
          TacGeneralizeDep c
      | IDENT "lettac"; "("; id = base_ident; ":="; c = lconstr; ")";
          p = clause_pattern -> TacLetTac (id,c,p)
      | IDENT "instantiate"; "("; n = natural; ":="; c = lconstr; ")" ->
          TacInstantiate (n,c)

      | IDENT "specialize"; n = OPT natural; lcb = constr_with_bindings ->
	  TacSpecialize (n,lcb)
      | IDENT "lapply"; c = constr -> TacLApply c

      (* Derived basic tactics *)
      | IDENT "simple_induction"; h = quantified_hypothesis ->
          TacSimpleInduction h
      | IDENT "induction"; c = induction_arg; el = OPT eliminator;
          ids = with_names -> TacNewInduction (c,el,ids)
      | IDENT "double"; IDENT "induction"; h1 = quantified_hypothesis;
	  h2 = quantified_hypothesis -> TacDoubleInduction (h1,h2)
      | IDENT "simple_destruct"; h = quantified_hypothesis ->
          TacSimpleDestruct h
      | IDENT "destruct"; c = induction_arg; el = OPT eliminator; 
          ids = with_names -> TacNewDestruct (c,el,ids)
      | IDENT "decompose"; IDENT "record" ; c = constr -> TacDecomposeAnd c
      | IDENT "decompose"; IDENT "sum"; c = constr -> TacDecomposeOr c
      | IDENT "decompose"; "["; l = LIST1 global; "]"; c = constr
        -> TacDecompose (l,c)

      (* Automation tactic *)
      | IDENT "trivial"; db = hintbases -> TacTrivial db
      | IDENT "auto"; n = OPT natural; db = hintbases -> TacAuto (n, db)

      | IDENT "autotdb"; n = OPT natural -> TacAutoTDB n
      | IDENT "cdhyp"; id = identref -> TacDestructHyp (true,id)
      | IDENT "dhyp";  id = identref -> TacDestructHyp (false,id)
      | IDENT "dconcl"  -> TacDestructConcl
      | IDENT "superauto"; l = autoargs -> TacSuperAuto l
      | IDENT "auto"; n = OPT natural; IDENT "decomp"; p = OPT natural ->
	  TacDAuto (n, p)

      (* Context management *)
      | IDENT "clear"; l = LIST1 id_or_meta -> TacClear l
      | IDENT "clearbody"; l = LIST1 id_or_meta -> TacClearBody l
      | IDENT "move"; id1 = id_or_meta; IDENT "after"; id2 = id_or_meta -> 
	  TacMove (true,id1,id2)
      | IDENT "rename"; id1 = id_or_meta; IDENT "into"; id2 = id_or_meta -> 
	  TacRename (id1,id2)

      (* Constructors *)
      | IDENT "left"; bl = with_binding_list -> TacLeft bl
      | IDENT "right"; bl = with_binding_list -> TacRight bl
      | IDENT "split"; bl = with_binding_list -> TacSplit (false,bl)
      | IDENT "exists"; bl = binding_list -> TacSplit (true,bl)
      | IDENT "exists" -> TacSplit (true,NoBindings)
      | IDENT "constructor"; n = num_or_meta; l = with_binding_list ->
	  TacConstructor (n,l)
      | IDENT "constructor"; t = OPT tactic -> TacAnyConstructor t

      (* Equivalence relations *)
      | IDENT "reflexivity" -> TacReflexivity
      | IDENT "symmetry"; ido = OPT [ "in"; id = id_or_meta -> id ] -> 
	  TacSymmetry ido
      | IDENT "transitivity"; c = constr -> TacTransitivity c

      (* Equality and inversion *)
      | IDENT "dependent"; k =
	  [ IDENT "simple"; IDENT "inversion" -> SimpleInversion
	  | IDENT "inversion" -> FullInversion
	  | IDENT "inversion_clear" -> FullInversionClear ];
	  hyp = quantified_hypothesis; 
	  ids = with_names; co = OPT ["with"; c = constr -> c] ->
	    TacInversion (DepInversion (k,co,ids),hyp)
      | IDENT "simple"; IDENT "inversion";
	  hyp = quantified_hypothesis; ids = with_names; cl = simple_clause ->
	    TacInversion (NonDepInversion (SimpleInversion, cl, ids), hyp)
      | IDENT "inversion"; 
	  hyp = quantified_hypothesis; ids = with_names; cl = simple_clause ->
	    TacInversion (NonDepInversion (FullInversion, cl, ids), hyp)
      | IDENT "inversion_clear"; 
	  hyp = quantified_hypothesis; ids = with_names; cl = simple_clause ->
	    TacInversion (NonDepInversion (FullInversionClear, cl, ids), hyp)
      | IDENT "inversion"; hyp = quantified_hypothesis; 
	  "using"; c = constr; cl = simple_clause ->
	    TacInversion (InversionUsing (c,cl), hyp)

      (* Conversion *)
      | r = red_tactic; cl = clause -> TacReduce (r, cl)
      (* Change ne doit pas s'appliquer dans un Definition t := Eval ... *)
      | IDENT "change"; (oc,c) = conversion; cl = clause -> TacChange (oc,c,cl)
    ] ]
  ;
END;;
