
(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pcoq
open Pp
open Tactic
open Util
open Vernac

(* Proof commands *)
GEXTEND Gram
  GLOBAL: command ne_constrarg_list;

  destruct_location :
  [ [ IDENT "Conclusion"  -> <:ast< (CONCL)>>
    | IDENT "Discardable"; "Hypothesis"  -> <:ast< (DiscardableHYP)>>
    | "Hypothesis"   -> <:ast< (PreciousHYP)>> ]]
  ;
  ne_constrarg_list:
  [ [ l = LIST1 constrarg -> l ] ]
  ;
  opt_identarg_list:
  [ [ -> []
    | ":"; l = LIST1 identarg -> l ] ]
  ;
  deftok:
    [ [ IDENT "Meta"
      | IDENT "Tactic" ] ]
  ;
  vrec_clause:
    [ [ name=identarg; it=LIST1 input_fun; ":="; body=tactic_expr ->
          <:ast<(RECCLAUSE $name (FUNVAR ($LIST $it)) $body)>> ] ]
  ;
  command:
    [ [ IDENT "Goal"; c = constrarg; "." -> <:ast< (GOAL $c) >>
      | IDENT "Goal"; "." -> <:ast< (GOAL) >>
      | "Proof"; "." -> <:ast< (GOAL) >>
      |	IDENT "Begin"; "." -> <:ast< (GOAL) >>
      | IDENT "Abort"; "." -> <:ast< (ABORT) >>
      | "Qed"; "." -> <:ast< (SaveNamed) >>
      | IDENT "Save"; "." -> <:ast< (SaveNamed) >>
      | IDENT "Defined"; "." -> <:ast< (DefinedNamed) >>
      |	IDENT "Defined"; id = identarg; "." -> <:ast< (DefinedAnonymous $id) >>
      | IDENT "Save"; IDENT "Remark"; id = identarg; "." ->
          <:ast< (SaveAnonymousRmk $id) >>
      | IDENT "Save"; IDENT "Theorem"; id = identarg; "." ->
          <:ast< (SaveAnonymousThm $id) >>
      | IDENT "Save"; id = identarg; "." -> <:ast< (SaveAnonymous $id) >>
      | IDENT "Suspend"; "." -> <:ast< (SUSPEND) >>
      | IDENT "Resume"; "." -> <:ast< (RESUME) >>
      | IDENT "Resume"; id = identarg; "." -> <:ast< (RESUME $id) >>
      | IDENT "Abort"; IDENT "All"; "." -> <:ast< (ABORTALL) >>
      | IDENT "Abort"; id = identarg; "." -> <:ast< (ABORT $id) >>
      | IDENT "Restart"; "." -> <:ast< (RESTART) >>
      | "Proof"; c = constrarg; "." -> <:ast< (PROOF $c) >>
      | IDENT "Undo"; "." -> <:ast< (UNDO 1) >>
      | IDENT "Undo"; n = numarg; "." -> <:ast< (UNDO $n) >>
      | IDENT "Show"; n = numarg; "." -> <:ast< (SHOW $n) >>
      | IDENT "Show"; IDENT "Implicits"; n = numarg; "." ->
          <:ast< (SHOWIMPL $n) >>
      | IDENT "Focus"; "." -> <:ast< (FOCUS) >>
      | IDENT "Focus"; n = numarg; "." -> <:ast< (FOCUS $n) >>
      | IDENT "Unfocus"; "." -> <:ast< (UNFOCUS) >>
      | IDENT "Show"; "." -> <:ast< (SHOW) >>
      | IDENT "Show"; IDENT "Implicits"; "." -> <:ast< (SHOWIMPL) >>
      | IDENT "Show"; IDENT "Node"; "." -> <:ast< (ShowNode) >>
      | IDENT "Show"; IDENT "Script"; "." -> <:ast< (ShowScript) >>
      | IDENT "Show"; IDENT "Existentials"; "." -> <:ast< (ShowEx) >>
      | IDENT "Existential"; n = numarg; ":="; c = constrarg; "." ->
          <:ast< (EXISTENTIAL $n $c) >>
      | IDENT "Existential"; n = numarg; ":="; c1 = Constr.constr; ":";
        c2 = Constr.constr; "." ->
          <:ast< (EXISTENTIAL $n (CONSTR (CAST $c1 $c2))) >>
      | IDENT "Existential"; n = numarg; ":"; c2 = Constr.constr; ":=";
        c1 = Constr.constr; "." ->
          <:ast< (EXISTENTIAL $n (CONSTR (CAST $c1 $c2))) >>
      | IDENT "Explain"; "Proof"; l = numarg_list; "." ->
          <:ast< (ExplainProof ($LIST $l)) >>
      | IDENT "Explain"; "Proof"; IDENT "Tree"; l = numarg_list; "." ->
          <:ast< (ExplainProofTree ($LIST $l)) >>
      | IDENT "Go"; n = numarg; "." -> <:ast< (Go $n) >>
      | IDENT "Go"; IDENT "top"; "." -> <:ast< (Go "top") >>
      | IDENT "Go"; IDENT "prev"; "." -> <:ast< (Go "prev") >>
      | IDENT "Go"; IDENT "next"; "." -> <:ast< (Go "next") >>
      | IDENT "Show"; "Proof"; "." -> <:ast< (ShowProof) >>
      | IDENT "Guarded"; "." -> <:ast< (CheckGuard) >>
      | IDENT "Show"; IDENT "Tree"; "." -> <:ast< (ShowTree) >>
      | IDENT "Show"; IDENT "Conjectures"; "." -> <:ast< (ShowProofs) >>

(* Definitions for tactics *)

      | deftok; "Definition"; name=identarg; ":="; body=Tactic.tactic;
        "." -> <:ast<(TACDEF $name (AST $body))>>
      | deftok; "Definition"; name=identarg; largs=LIST1 input_fun;
        ":="; body=Tactic.tactic; "." ->
        <:ast<(TACDEF $name (AST (FUN (FUNVAR ($LIST $largs)) $body)))>>
      | IDENT "Recursive"; deftok; "Definition"; vc=vrec_clause ; "." ->
        (match vc with
            Coqast.Node(_,"RECCLAUSE",nme::tl) ->
              <:ast<(TACDEF $nme (AST (REC $vc)))>>
           |_ ->
             anomalylabstrm "Gram.vernac" [<'sTR "Not a correct RECCLAUSE">])
      |IDENT "Recursive"; deftok; "Definition"; vc=vrec_clause;
        IDENT "And"; vcl=LIST1 vrec_clause SEP IDENT "And"; "." ->
        let nvcl=
          List.fold_right
            (fun e b -> match e with
                Coqast.Node(_,"RECCLAUSE",nme::_) ->
                  nme::<:ast<(AST (REC $e))>>::b
               |_ ->
                 anomalylabstrm "Gram.vernac" [<'sTR
                   "Not a correct RECCLAUSE">]) (vc::vcl) []
        in
          <:ast<(TACDEF ($LIST $nvcl))>>

(* Hints for Auto and EAuto *)

      | IDENT "Hint"; hintname = identarg; dbname = opt_identarg_list; ":=";
	IDENT "Resolve"; c = constrarg; "." ->
	  <:ast<(HintResolve $hintname (VERNACARGLIST ($LIST $dbname)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Immediate"; c = constrarg; "." ->
	  <:ast<(HintImmediate $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Unfold"; c = identarg; "." ->
	  <:ast<(HintUnfold $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Constructors"; c = identarg;  "." ->
	  <:ast<(HintConstructors $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Extern"; n = numarg; c = constrarg ; tac = tacarg; "." ->
	  <:ast<(HintExtern $hintname (VERNACARGLIST ($LIST $dbnames)) 
		   $n $c (TACTIC $tac))>>
	  
      | IDENT "Hints"; IDENT "Resolve"; l = ne_identarg_list; 
	dbnames = opt_identarg_list; "." ->
          <:ast< (HintsResolve (VERNACARGLIST ($LIST $dbnames)) ($LIST $l)) >>
	  
      | IDENT "Hints"; IDENT "Immediate"; l = ne_identarg_list; 
	dbnames = opt_identarg_list; "." ->
          <:ast< (HintsImmediate (VERNACARGLIST ($LIST $dbnames)) ($LIST $l)) >>
	  
      | IDENT "Hints"; IDENT "Unfold"; l = ne_identarg_list;
	dbnames = opt_identarg_list; "." ->
          <:ast< (HintsUnfold (VERNACARGLIST ($LIST $dbnames)) ($LIST $l)) >>
	  
      | IDENT "HintDestruct"; 
                dloc = destruct_location;
                na  = identarg;
                hyptyp = constrarg;
                pri = numarg;
                tac = Prim.astact; "." -> 
          <:ast< (HintDestruct $na (AST $dloc) $hyptyp $pri (AST $tac))>>

      | n = numarg; ":"; tac = tacarg; "." ->
          <:ast< (SOLVE $n (TACTIC $tac)) >> 

(*This entry is not commented, only for debug*)
      | IDENT "PrintConstr"; com = constrarg; "." ->
          <:ast< (PrintConstr $com)>>
      ] ];
  END
