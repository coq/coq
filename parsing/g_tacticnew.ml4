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

let compute = Cbv all_flags

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
      match Stream.npeek 1 strm with
        | [("","(")] ->
            (match Stream.npeek 2 strm with
              | [_; ("IDENT",s)] ->
                  (match Stream.npeek 3 strm with
	            | [_; _; ("", ":=")] ->
                        Stream.junk strm; Stream.junk strm; Stream.junk strm;
                        Names.id_of_string s
	            | _ -> raise Stream.Failure)
	      | _ -> raise Stream.Failure)
	| _ -> raise Stream.Failure)

(* idem for (x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  Gram.Entry.of_parser "test_lpar_idnum_coloneq"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("","(")] ->
            (match Stream.npeek 2 strm with
              | [_; (("IDENT"|"INT"),_)] ->
                  (match Stream.npeek 3 strm with
                    | [_; _; ("", ":=")] -> ()
                    | _ -> raise Stream.Failure)
              | _ -> raise Stream.Failure)
        | _ -> raise Stream.Failure)

(* idem for (x:t) *)
let lpar_id_colon =
  Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("","(")] ->
            (match Stream.npeek 2 strm with
              | [_; ("IDENT",id)] ->
                  (match Stream.npeek 3 strm with
                    | [_; _; ("", ":")] ->
                        Stream.junk strm; Stream.junk strm; Stream.junk strm;
                        Names.id_of_string id
                    | _ -> raise Stream.Failure)
              | _ -> raise Stream.Failure)
        | _ -> raise Stream.Failure)

open Constr
open Prim
open Tactic

let mk_fix_tac (loc,id,bl,ann,ty) =
  let n =
    match bl,ann with
        [([_],_)], None -> 1
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
  try ElimOnIdent (Topconstr.constr_loc c,snd(coerce_to_id c))
  with _ -> ElimOnConstr c

let local_compute = [FBeta;FIota;FDeltaBut [];FZeta]

let error_oldelim _ = error "OldElim no longer supported"

let join_to_constr loc c2 = (fst loc), snd (Topconstr.constr_loc c2)

(* Auxiliary grammar rules *)

if not !Options.v7 then
GEXTEND Gram
  GLOBAL: simple_tactic constr_with_bindings quantified_hypothesis
  bindings red_expr int_or_var castedopenconstr simple_intropattern;

  int_or_var:
    [ [ n = integer  -> Genarg.ArgArg n
      | id = identref -> Genarg.ArgVar id ] ]
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
      | c1 = constr; "at"; nl = LIST1 integer; "with"; c2 = constr ->
	  (Some (nl,c1), c2) ] ]
  ;
  occurrences:
    [ [ "at"; nl = LIST1 integer -> nl
      | -> [] ] ]
  ;
  pattern_occ:
    [ [ c = constr; nl = occurrences -> (nl,c) ] ]
  ;
  unfold_occ:
    [ [ c = global; nl = occurrences -> (nl,c) ] ]
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
  bindings:
    [ [ test_lpar_idnum_coloneq; bl = LIST1 simple_binding ->
          ExplicitBindings bl
      | bl = LIST1 constr -> ImplicitBindings bl ] ]
  ;
  constr_with_bindings:
    [ [ c = constr; l = with_bindings -> (c, l) ] ]
  ;
  with_bindings:
    [ [ "with"; bl = bindings -> bl | -> NoBindings ] ]
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
      | IDENT "compute" -> compute
      | IDENT "unfold"; ul = LIST1 unfold_occ SEP "," -> Unfold ul
      | IDENT "fold"; cl = LIST1 constr -> Fold cl
      | IDENT "pattern"; pl = LIST1 pattern_occ SEP","-> Pattern pl ] ]
  ;
  (* This is [red_tactic] including possible extensions *)
  red_expr:
    [ [ IDENT "red" -> Red false
      | IDENT "hnf" -> Hnf
      | IDENT "simpl"; po = OPT pattern_occ -> Simpl po
      | IDENT "cbv"; s = LIST1 red_flag -> Cbv (make_red_flag s)
      | IDENT "lazy"; s = LIST1 red_flag -> Lazy (make_red_flag s)
      | IDENT "compute" -> compute
      | IDENT "unfold"; ul = LIST1 unfold_occ -> Unfold ul
      | IDENT "fold"; cl = LIST1 constr -> Fold cl
      | IDENT "pattern"; pl = LIST1 pattern_occ -> Pattern pl
      | s = IDENT; OPT [ (* compat V8.0pl1 *) constr ] -> ExtraRedExpr s ] ]
  ;
  hypident:
    [ [ id = id_or_meta -> id,(InHyp,ref None)
      | "("; IDENT "type"; IDENT "of"; id = id_or_meta; ")" ->
          id,(InHypTypeOnly,ref None)
      | "("; IDENT "value"; IDENT "of"; id = id_or_meta; ")" ->
          id,(InHypValueOnly,ref None)
    ] ]
  ;
  hypident_occ:
    [ [ (id,l)=hypident; occs=occurrences -> (id,occs,l) ] ]
  ;
  clause:
    [ [ "in"; "*"; occs=occurrences ->
        {onhyps=None;onconcl=true;concl_occs=occs}
      | "in"; "*"; "|-"; (b,occs)=concl_occ ->
          {onhyps=None; onconcl=b; concl_occs=occs}
      | "in"; hl=LIST0 hypident_occ SEP","; "|-"; (b,occs)=concl_occ ->
          {onhyps=Some hl; onconcl=b; concl_occs=occs}
      | "in"; hl=LIST0 hypident_occ SEP"," ->
          {onhyps=Some hl; onconcl=false; concl_occs=[]}
      | -> {onhyps=Some[];onconcl=true; concl_occs=[]} ] ]
  ;
  concl_occ:
    [ [ "*"; occs = occurrences -> (true,occs)
      | -> (false, []) ] ]
  ;
  simple_clause:
    [ [ "in"; idl = LIST1 id_or_meta -> idl
      | -> [] ] ]
  ;
  fixdecl:
    [ [ "("; id = base_ident; bl=LIST0 Constr.binder; ann=fixannot;
        ":"; ty=lconstr; ")" -> (loc,id,bl,ann,ty) ] ]
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
    [ [ "as"; ipat = simple_intropattern -> Some ipat | -> None ] ]
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
      | "fix"; id = base_ident; n = natural; "with"; fd = LIST1 fixdecl ->
	  TacMutualFix (id,n,List.map mk_fix_tac fd)
      | "cofix" -> TacCofix None
      | "cofix"; id = base_ident -> TacCofix (Some id)
      | "cofix"; id = base_ident; "with"; fd = LIST1 fixdecl ->
	  TacMutualCofix (id,List.map mk_cofix_tac fd)

      | IDENT "cut"; c = constr -> TacCut c
      | IDENT "assert"; id = lpar_id_colon; t = lconstr; ")" ->
          TacTrueCut (Names.Name id,t)
      | IDENT "assert"; id = lpar_id_coloneq; b = lconstr; ")" ->
          TacForward (false,Names.Name id,b)
      | IDENT "assert"; c = constr -> TacTrueCut (Names.Anonymous,c)
      | IDENT "pose"; id = lpar_id_coloneq; b = lconstr; ")" ->
	  TacForward (true,Names.Name id,b)
      | IDENT "pose"; b = constr -> TacForward (true,Names.Anonymous,b)
      | IDENT "generalize"; lc = LIST1 constr -> TacGeneralize lc
      | IDENT "generalize"; IDENT "dependent"; c = constr ->
          TacGeneralizeDep c
      | IDENT "set"; id = lpar_id_coloneq; c = lconstr; ")";
          p = clause -> TacLetTac (Names.Name id,c,p)
      | IDENT "set"; c = constr; p = clause ->
          TacLetTac (Names.Anonymous,c,p)
      | IDENT "instantiate"; "("; n = natural; ":="; c = lconstr; ")";
	  cls = clause ->
            TacInstantiate (n,c,cls)
	    
      | IDENT "specialize"; n = OPT natural; lcb = constr_with_bindings ->
	  TacSpecialize (n,lcb)
      | IDENT "lapply"; c = constr -> TacLApply c

      (* Derived basic tactics *)
      | IDENT "simple"; IDENT"induction"; h = quantified_hypothesis ->
          TacSimpleInduction (h,ref [])
      | IDENT "induction"; c = induction_arg; ids = with_names; 
	  el = OPT eliminator -> TacNewInduction (c,el,(ids,ref []))
      | IDENT "double"; IDENT "induction"; h1 = quantified_hypothesis;
	  h2 = quantified_hypothesis -> TacDoubleInduction (h1,h2)
      | IDENT "simple"; IDENT"destruct"; h = quantified_hypothesis ->
          TacSimpleDestruct h
      | IDENT "destruct"; c = induction_arg; ids = with_names; 
	  el = OPT eliminator -> TacNewDestruct (c,el,(ids,ref []))
      | IDENT "decompose"; IDENT "record" ; c = constr -> TacDecomposeAnd c
      | IDENT "decompose"; IDENT "sum"; c = constr -> TacDecomposeOr c
      | IDENT "decompose"; "["; l = LIST1 global; "]"; c = constr
        -> TacDecompose (l,c)

      (* Automation tactic *)
      | IDENT "trivial"; db = hintbases -> TacTrivial db
      | IDENT "auto"; n = OPT natural; db = hintbases -> TacAuto (n, db)

(* Obsolete since V8.0
      | IDENT "autotdb"; n = OPT natural -> TacAutoTDB n
      | IDENT "cdhyp"; id = identref -> TacDestructHyp (true,id)
      | IDENT "dhyp";  id = identref -> TacDestructHyp (false,id)
      | IDENT "dconcl"  -> TacDestructConcl
      | IDENT "superauto"; l = autoargs -> TacSuperAuto l
*)
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
      | IDENT "left"; bl = with_bindings -> TacLeft bl
      | IDENT "right"; bl = with_bindings -> TacRight bl
      | IDENT "split"; bl = with_bindings -> TacSplit (false,bl)
      | "exists"; bl = bindings -> TacSplit (true,bl)
      | "exists" -> TacSplit (true,NoBindings)
      | IDENT "constructor"; n = num_or_meta; l = with_bindings ->
	  TacConstructor (n,l)
      | IDENT "constructor"; t = OPT tactic -> TacAnyConstructor t

      (* Equivalence relations *)
      | IDENT "reflexivity" -> TacReflexivity
      | IDENT "symmetry"; cls = clause -> TacSymmetry cls
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
