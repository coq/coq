
(* $Id$ *)

open Pcoq

open Tactic

GEXTEND Gram
  simple_tactic:
    [ [ IDENT "ML"; s = Prim.string -> <:ast< (MLTACTIC $s) >> ] ]
  ;
END

open Vernac

GEXTEND Gram
  vernac: LAST
    [ [ tac = tacarg; "." -> <:ast< (SOLVE 1 (TACTIC $tac)) >> ] ]
  ;
END

GEXTEND Gram
  tacarg:
    [ [ tcl = Tactic.tactic_com_list -> tcl ] ]
  ;
  theorem_body_line:
    [ [ n = numarg; ":"; tac = tacarg; "." ->
          <:ast< (VERNACCALL {SOLVE} $n (TACTIC $tac)) >>
      | tac = tacarg; "." -> <:ast< (VERNACCALL {SOLVE} 1 (TACTIC $tac)) >>
      ] ]
  ;
  theorem_body_line_list:
    [ [ t = theorem_body_line -> [t]
      | t = theorem_body_line; l = theorem_body_line_list -> t :: l ] ]
  ;
  theorem_body:
    [ [ l = theorem_body_line_list ->
          <:ast< (VERNACARGLIST ($LIST $l)) >> ] ]
  ;
  destruct_location :
  [ [ IDENT "Conclusion"  -> <:ast< (CONCL)>>
    | IDENT "Discardable"; "Hypothesis"  -> <:ast< (DiscardableHYP)>>
    | "Hypothesis"   -> <:ast< (PreciousHYP)>> ]]
  ;
  ne_comarg_list:
  [ [ l = LIST1 comarg -> l ] ]
  ;

  opt_identarg_list:
  [ [ -> []
    | ":"; l = LIST1 identarg -> l ] ]
  ;

  finite_tok:
    [ [ "Inductive" -> <:ast< "Inductive" >>
      | "CoInductive" -> <:ast< "CoInductive" >> ] ]
  ;
  block_old_style:
    [ [ ind = oneind_old_style; "with"; indl = block_old_style -> ind :: indl
      | ind = oneind_old_style -> [ind] ] ]
  ;
  oneind_old_style:
    [ [ id = identarg; ":"; c = comarg; ":="; lidcom = lidcom ->
          <:ast< (VERNACARGLIST $id $c $lidcom) >> ] ]
  ;
  block:
    [ [ ind = oneind; "with"; indl = block -> ind :: indl
      | ind = oneind -> [ind] ] ]
  ;
  oneind:
    [ [ id = identarg; indpar = indpar; ":"; c = comarg; ":="; lidcom = lidcom
      -> <:ast< (VERNACARGLIST $id $c $indpar $lidcom) >> ] ]
  ;
  onerec:
    [ [ id = identarg; "["; idl = ne_binder_semi_list; "]"; ":"; c = comarg;
        ":="; def = comarg ->
          <:ast< (VERNACARGLIST $id (BINDERLIST ($LIST $idl)) $c $def) >> ] ]
  ;
  specifrec:
    [ [ rec_ = onerec; "with"; recl = specifrec -> rec_ :: recl
      | rec_ = onerec -> [rec_] ] ]
  ;
  onecorec:
    [ [ id = identarg; ":"; c = comarg; ":="; def = comarg ->
          <:ast< (VERNACARGLIST $id $c $def) >> ] ]
  ;
  specifcorec:
    [ [ corec = onecorec; "with"; corecl = specifcorec -> corec :: corecl
      | corec = onecorec -> [corec] ] ]
  ;
  rec_constr:
    [ [ c = Vernac.identarg -> <:ast< (VERNACARGLIST $c) >>
      |  -> <:ast< (VERNACARGLIST) >> ] ]
  ;
  record_tok:
    [ [ IDENT "Record" -> <:ast< "Record" >>
      | IDENT "Structure" -> <:ast< "Structure" >> ] ]
  ;
  field:
    [ [ id = identarg; ":"; c = Command.command ->
          <:ast< (VERNACARGLIST "" $id (COMMAND $c)) >>
      | id = identarg; ":>"; c = Command.command ->
          <:ast< (VERNACARGLIST "COERCION" $id (COMMAND $c)) >> ] ]
  ;
  nefields:
    [ [ idc = field; ";"; fs = nefields -> idc :: fs
      | idc = field -> [idc] ] ]
  ;
  fields:
    [ [ fs = nefields -> <:ast< (VERNACARGLIST ($LIST $fs)) >>
      |  -> <:ast< (VERNACARGLIST) >> ] ]
  ;
  onescheme:
    [ [ id = identarg; ":="; dep = dep; c = comarg; IDENT "Sort";
        s = sortdef ->
          <:ast< (VERNACARGLIST $id $dep $c (COMMAND $s)) >> ] ]
  ;
  specifscheme:
    [ [ rec_ = onescheme; "with"; recl = specifscheme -> rec_ :: recl
      | rec_ = onescheme -> [rec_] ] ]
  ;
  dep:
    [ [ IDENT "Induction"; IDENT "for" -> <:ast< "DEP" >>
      | IDENT "Minimality"; IDENT "for" -> <:ast< "NODEP" >> ] ]
  ;
  ne_binder_semi_list:
    [ [ id = binder; ";"; idl = ne_binder_semi_list -> id :: idl
      | id = binder -> [id] ] ]
  ;
  indpar:
    [ [ "["; bl = ne_binder_semi_list; "]" ->
          <:ast< (BINDERLIST ($LIST $bl)) >>
      |  -> <:ast< (BINDERLIST) >> ] ]
  ;
  sortdef:
    [ [ "Set" -> <:ast< (PROP {Pos}) >>
      | "Prop" -> <:ast< (PROP {Null}) >>
      | "Type" -> <:ast< (TYPE) >> ] ]
  ;
  thm_tok:
    [ [ "Theorem" -> <:ast< "THEOREM" >>
      | IDENT "Lemma" -> <:ast< "LEMMA" >>
      | IDENT "Fact" -> <:ast< "FACT" >>
      | IDENT "Remark" -> <:ast< "REMARK" >> ] ]
  ;

  def_tok:
    [ [ "Definition" -> <:ast< "DEFINITION" >>
      | IDENT "Local" -> <:ast< "LOCAL" >> 
      | "@"; "Definition"  -> <:ast< "OBJECT" >>
      | "@"; IDENT "Local"  -> <:ast< "LOBJECT" >>
      | "@"; IDENT "Coercion"  -> <:ast< "OBJCOERCION" >>
      | "@"; IDENT "Local"; IDENT "Coercion"  -> <:ast< "LOBJCOERCION" >>
      | IDENT "SubClass"  -> <:ast< "SUBCLASS" >>
      | IDENT "Local"; IDENT "SubClass"  -> <:ast< "LSUBCLASS" >> ] ]  
  ;
  import_tok:
    [ [ IDENT "Import" -> <:ast< "IMPORT" >>
      | IDENT "Export" -> <:ast< "EXPORT" >>
      |  -> <:ast< "IMPORT" >> ] ]
  ;
  specif_tok:
    [ [ IDENT "Implementation" -> <:ast< "IMPLEMENTATION" >>
      | IDENT "Specification" -> <:ast< "SPECIFICATION" >>
      |  -> <:ast< "UNSPECIFIED" >> ] ]
  ;
  hyp_tok:
    [ [ "Hypothesis" -> <:ast< "HYPOTHESIS" >>
      | "Variable" -> <:ast< "VARIABLE" >> ] ]
  ;
  hyps_tok:
    [ [ IDENT "Hypotheses" -> <:ast< "HYPOTHESES" >>
      | IDENT "Variables" -> <:ast< "VARIABLES" >> ] ]
  ;
  param_tok:
    [ [ "Axiom" -> <:ast< "AXIOM" >>
      | "Parameter" -> <:ast< "PARAMETER" >> ] ]
  ;
  params_tok:
    [ [ IDENT "Parameters" -> <:ast< "PARAMETERS" >> ] ]
  ;
  binder:
    [ [ idl = ne_identarg_comma_list; ":"; c = Command.command ->
          <:ast< (BINDER $c ($LIST $idl)) >> ] ]
  ;
  idcom:
    [ [ id = IDENT; ":"; c = Command.command ->
          <:ast< (BINDER $c ($VAR $id)) >> ] ]
  ;
  ne_lidcom:
    [ [ idc = idcom; "|"; l = ne_lidcom -> idc :: l
      | idc = idcom -> [idc] ] ]
  ;
  lidcom:
    [ [ l = ne_lidcom -> <:ast< (BINDERLIST ($LIST $l)) >>
      | "|"; l = ne_lidcom -> <:ast< (BINDERLIST ($LIST $l)) >>
      |  -> <:ast< (BINDERLIST) >> ] ]
  ;
  END

GEXTEND Gram
  vernac:
      (* Definition, Goal *)
    [ [ thm = thm_tok; id = identarg; ":"; c = comarg; "." ->
          <:ast< (StartProof $thm $id $c) >>
      | thm = thm_tok; id = identarg; ":"; c = comarg; ":="; "Proof";
        tb = theorem_body; "Qed"; "." ->
          <:ast< (TheoremProof $thm $id $c $tb) >>

      | def = def_tok; s = identarg; ":"; c1 = Command.command; "." ->
          <:ast< (StartProof $def $s (COMMAND $c1)) >>
      | def = def_tok; s = identarg; ":="; c1 = Command.command; "." ->
          <:ast< (DEFINITION $def $s (COMMAND $c1)) >>
      | def = def_tok; s = identarg; ":="; c1 = Command.command; ":";
        c2 = Command.command; "." ->
          <:ast< (DEFINITION $def $s (COMMAND (CAST $c1 $c2))) >>
      | def = def_tok; s = identarg; ":"; c1 = Command.command; ":=";
        c2 = Command.command; "." ->
          <:ast< (DEFINITION $def $s (COMMAND (CAST $c2 $c1))) >>

(* CP / Juillet 99 
   Ajout de la possibilite d'appliquer une regle de reduction au 
   corps d'une definition 
   Definition t := Eval red in term
*)

      | def = def_tok; s = identarg; ":="; 
      IDENT "Eval"; r = Tactic.red_tactic; "in"; c1 = Command.command; "." ->
          <:ast< (DEFINITION $def $s (COMMAND $c1) (TACTIC_ARG (REDEXP $r))) >>
      | def = def_tok; s = identarg; ":="; 
      IDENT "Eval"; r = Tactic.red_tactic; "in"; c1 = Command.command; ":";
        c2 = Command.command; "." ->
          <:ast< (DEFINITION $def $s 
                 (COMMAND (CAST $c1 $c2)) (TACTIC_ARG (REDEXP $r))) >>
      | def = def_tok; s = identarg; ":"; c1 = Command.command; ":=";
        IDENT "Eval"; r = Tactic.red_tactic; "in"; 
	c2 = Command.command; "." ->
          <:ast< (DEFINITION $def $s (COMMAND (CAST $c2 $c1)) 
		    (TACTIC_ARG (REDEXP $r))) >>

(* Papageno / Février 99
   Ajout du racourci "Definition x [c:nat] := t" pour 
                     "Definition x := [c:nat]t" *)

      | def = def_tok; s = identarg; "["; id1 = IDENT; ":"; 
	c = Command.command; t = definition_tail;  "." -> 
	  <:ast< (DEFINITION $def $s (COMMAND (LAMBDA $c [$id1]$t))) >>

      | def = def_tok; s = identarg; "["; id1 = IDENT; ",";
	idl = Command.ne_ident_comma_list; ":"; c = Command.command; 
	t = definition_tail; "." -> 
	  <:ast< (DEFINITION $def $s (COMMAND 
			(LAMBDALIST $c [$id1]($SLAM $idl $t)))) >>


      | hyp = hyp_tok; bl = ne_binder_semi_list; "." ->
          <:ast< (VARIABLE $hyp  (BINDERLIST ($LIST $bl))) >>
      | hyp = hyps_tok; bl = ne_binder_semi_list; "." ->
          <:ast< (VARIABLE $hyp  (BINDERLIST ($LIST $bl))) >>
      | hyp = param_tok; bl = ne_binder_semi_list; "." ->
          <:ast< (PARAMETER $hyp (BINDERLIST ($LIST $bl))) >>
      | hyp = params_tok; bl = ne_binder_semi_list; "." ->
          <:ast< (PARAMETER $hyp (BINDERLIST ($LIST $bl))) >>
      | IDENT "Abstraction"; id = identarg; "["; l = ne_numarg_list; "]";
        ":="; c = comarg; "." ->
          <:ast< (ABSTRACTION $id $c ($LIST $l)) >>
      | f = finite_tok; "Set"; id = identarg; indpar = indpar; ":=";
        lidcom = lidcom; "." ->
          <:ast< (ONEINDUCTIVE $f $id (COMMAND (PROP {Pos})) $indpar
                   $lidcom) >>
      | f = finite_tok; "Type"; id = identarg; indpar = indpar; ":=";
        lidcom = lidcom; "." ->
          <:ast< (ONEINDUCTIVE $f $id (COMMAND (TYPE)) $indpar $lidcom) >>
      | f = finite_tok; "Prop"; id = identarg; indpar = indpar; ":=";
        lidcom = lidcom; "." ->
          <:ast< (ONEINDUCTIVE $f $id (COMMAND (PROP {Null})) $indpar
                   $lidcom) >>
      | f = finite_tok; indl = block; "." ->
          <:ast< (MUTUALINDUCTIVE $f (VERNACARGLIST ($LIST $indl))) >>

      | record_tok; name = identarg; ps = indpar; ":"; s = sortdef; ":=";
        c = rec_constr; "{"; fs = fields; "}"; "." ->
          <:ast< (RECORD "" $name $ps (COMMAND $s) $c $fs) >>
      | record_tok; ">"; name = identarg; ps = indpar; ":"; s = sortdef; ":=";
        c = rec_constr; "{"; fs = fields; "}"; "." ->
          <:ast< (RECORD "COERCION" $name $ps (COMMAND $s) $c $fs) >>

      | IDENT "Mutual"; "["; bl = ne_binder_semi_list; "]" ; f = finite_tok;
        indl = block_old_style; "." ->
          <:ast< (OLDMUTUALINDUCTIVE (BINDERLIST ($LIST $bl)) $f
                                     (VERNACARGLIST ($LIST $indl))) >>
      | IDENT "Mutual"; f = finite_tok; indl = block; "." ->
          <:ast< (MUTUALINDUCTIVE $f (VERNACARGLIST ($LIST $indl))) >>
      | "Fixpoint"; recs = specifrec; "." ->
          <:ast< (MUTUALRECURSIVE (VERNACARGLIST ($LIST $recs))) >>
      | "CoFixpoint"; corecs = specifcorec; "." ->
          <:ast< (MUTUALCORECURSIVE (VERNACARGLIST ($LIST $corecs))) >>
      | IDENT "Scheme"; schemes = specifscheme; "." ->
          <:ast< (INDUCTIONSCHEME (VERNACARGLIST ($LIST $schemes))) >>
      ] ];

      
      definition_tail:
    	[ [ ";"; idl = Command.ne_ident_comma_list;
            ":"; c = Command.command; c2 = definition_tail ->
              <:ast< (LAMBDALIST $c ($SLAM $idl $c2)) >>
	| "]"; ":"; ty = Command.command; ":=" ; c = Command.command -> 
	    <:ast< (CAST $c $ty) >>
 	| "]"; ":="; c = Command.command -> c 
	] ];

  END

(* State management *)
GEXTEND Gram
  vernac:
    [ [ 
        IDENT "Save"; IDENT "State"; id = identarg; "." ->
          <:ast< (SaveState $id "") >>
      | IDENT "Save"; IDENT "State"; id = identarg; s = stringarg; "." ->
          <:ast< (SaveState $id $s) >>
      | IDENT "Write"; IDENT "States"; id = identarg; "." ->
          <:ast< (WriteStates $id) >>
      | IDENT "Write"; IDENT "States"; id = stringarg; "." ->
          <:ast< (WriteStates $id) >>
      | IDENT "Restore";  IDENT "State"; id = identarg; "." ->
          <:ast< (RestoreState $id) >>
      | IDENT "Remove";  IDENT "State"; id = identarg; "." ->
          <:ast< (RemoveState $id) >>
      | IDENT "Reset"; IDENT "after"; id = identarg; "." ->
          <:ast< (ResetAfter $id) >>
      | IDENT "Reset"; IDENT "Initial"; "." -> <:ast< (ResetInitial) >>
      | IDENT "Reset"; IDENT "Section"; id = identarg; "." ->
          <:ast< (ResetSection $id) >>
      | IDENT "Reset"; id = identarg; "." -> <:ast< (ResetName $id) >>

(* Modules and Sections *)   

      | IDENT "Read"; IDENT "Module"; id = identarg; "." ->
          <:ast< (ReadModule $id) >>
      | IDENT "Require"; import = import_tok; specif = specif_tok;
        id = identarg; "." -> <:ast< (Require $import $specif $id) >>
      | IDENT "Require"; import = import_tok; specif = specif_tok;
        id = identarg; filename = stringarg; "." ->
          <:ast< (RequireFrom $import $specif $id $filename) >>
      | IDENT "Section"; id = identarg; "." -> <:ast< (BeginSection $id) >>
      | IDENT "Chapter"; id = identarg; "." -> <:ast< (BeginSection $id) >>
      | IDENT "Module"; id = identarg; "." -> <:ast< (BeginModule $id) >>
      | IDENT "Begin"; IDENT "Silent"; "." -> <:ast< (BeginSilent) >>
      | IDENT "End"; IDENT "Silent"; "." -> <:ast< (EndSilent) >>
      | IDENT "End"; id = identarg; "." -> <:ast< (EndSection $id) >>
      | IDENT "Declare"; IDENT "ML"; IDENT "Module";
        l = ne_stringarg_list; "." -> <:ast< (DeclareMLModule ($LIST $l)) >>
      | IDENT "Import"; id = identarg; "." -> <:ast< (ImportModule $id) >>
	  (* Transparent and Opaque *)
      | IDENT "Transparent"; l = ne_identarg_list; "." ->
          <:ast< (TRANSPARENT ($LIST $l)) >>
      | IDENT "Opaque"; l = ne_identarg_list; "." -> 
	  <:ast< (OPAQUE ($LIST $l)) >>
      
	  (* Extraction *)
      | IDENT "Extraction"; id = identarg; "." ->
          <:ast< (PrintExtractId $id) >>
      | IDENT "Extraction"; "." -> <:ast< (PrintExtract) >>

(* Grammar extensions, Coercions, Implicits *)
	  
     | IDENT "Coercion"; s = identarg; ":="; c1 = Command.command; "." ->
         <:ast< (DEFINITION "COERCION" $s (COMMAND $c1)) >>
     | IDENT "Coercion"; s = identarg; ":="; c1 = Command.command; ":";
        c2 = Command.command; "." ->
          <:ast< (DEFINITION "COERCION" $s (COMMAND (CAST $c1 $c2))) >>
     | IDENT "Coercion"; IDENT "Local"; s = identarg; ":="; 
	c1 = Command.command; "." ->
          <:ast< (DEFINITION "LCOERCION" $s (COMMAND $c1)) >>
     | IDENT "Coercion"; IDENT "Local"; s = identarg; ":="; 
	c1 = Command.command; ":"; c2 = Command.command; "." ->
          <:ast< (DEFINITION "LCOERCION" $s (COMMAND (CAST $c1 $c2))) >>
	  
	  
     | IDENT "Syntactic"; "Definition"; id = identarg; ":="; com = comarg;
        "." -> <:ast< (SyntaxMacro $id $com) >>
     | IDENT "Syntactic"; "Definition"; id = identarg; ":="; com = comarg;
        "|"; n = numarg; "." -> <:ast< (SyntaxMacro $id $com $n) >>
     | IDENT "Print"; "Grammar"; uni = identarg; ent = identarg; "." ->
         <:ast< (PrintGrammar $uni $ent) >>
     | IDENT "Identity"; IDENT "Coercion"; IDENT "Local"; f = identarg;
        ":"; c = identarg; ">->"; d = identarg; "." ->
          <:ast< (COERCION "LOCAL" "IDENTITY" $f $c $d) >>
     | IDENT "Identity"; IDENT "Coercion"; f = identarg; ":";
        c = identarg; ">->"; d = identarg; "." ->
          <:ast< (COERCION "" "IDENTITY" $f $c $d) >>
     | IDENT "Coercion"; IDENT "Local"; f = identarg; ":"; c = identarg;
        ">->"; d = identarg; "." ->
          <:ast< (COERCION "LOCAL" "" $f $c $d) >>
     | IDENT "Coercion"; f = identarg; ":"; c = identarg; ">->";
        d = identarg; "." -> <:ast< (COERCION "" "" $f $c $d) >>
     | IDENT "Class"; IDENT "Local"; c = identarg; "." ->
         <:ast< (CLASS "LOCAL" $c) >>
     | IDENT "Class"; c = identarg; "." -> <:ast< (CLASS "" $c) >>
     | IDENT "Implicit"; IDENT "Arguments"; IDENT "On"; "." ->
         <:ast< (IMPLICIT_ARGS_ON) >>
     | IDENT "Implicit"; IDENT "Arguments"; IDENT "Off"; "." ->
         <:ast< (IMPLICIT_ARGS_OFF) >>
     | IDENT "Implicits"; id = identarg; "["; l = numarg_list; "]"; "." ->
         <:ast< (IMPLICITS "" $id ($LIST $l)) >>
     | IDENT "Implicits"; id = identarg; "." ->
         <:ast< (IMPLICITS "Auto" $id) >> 
 ] ];
    END

(* Proof commands *)
GEXTEND Gram
  vernac:
    [ [ IDENT "Goal"; c = comarg; "." -> <:ast< (GOAL $c) >>
      | IDENT "Goal"; "." -> <:ast< (GOAL) >>
      | "Proof"; "." -> <:ast< (GOAL) >>
      | IDENT "Abort"; "." -> <:ast< (ABORT) >>
      | "Qed"; "." -> <:ast< (SaveNamed) >>
      | IDENT "Save"; "." -> <:ast< (SaveNamed) >>
      | IDENT "Defined"; "." -> <:ast< (DefinedNamed) >>
      | IDENT "Save"; IDENT "Remark"; id = identarg; "." ->
          <:ast< (SaveAnonymousRmk $id) >>
      | IDENT "Save"; IDENT "Theorem"; id = identarg; "." ->
          <:ast< (SaveAnonymousThm $id) >>
      | IDENT "Save"; id = identarg; "." -> <:ast< (SaveAnonymousThm $id) >>
      | IDENT "Suspend"; "." -> <:ast< (SUSPEND) >>
      | IDENT "Resume"; "." -> <:ast< (RESUME) >>
      | IDENT "Resume"; id = identarg; "." -> <:ast< (RESUME $id) >>
      | IDENT "Abort"; IDENT "All"; "." -> <:ast< (ABORTALL) >>
      | IDENT "Abort"; id = identarg; "." -> <:ast< (ABORT $id) >>
      | IDENT "Restart"; "." -> <:ast< (RESTART) >>
      | "Proof"; c = comarg; "." -> <:ast< (PROOF $c) >>
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
      | IDENT "Existential"; n = numarg; ":="; c = Command.command; "." ->
          <:ast< (EXISTENTIAL $n (COMMAND $c)) >>
      | IDENT "Existential"; n = numarg; ":="; c1 = Command.command; ":";
        c2 = Command.command; "." ->
          <:ast< (EXISTENTIAL $n (COMMAND (CAST $c1 $c2))) >>
      | IDENT "Existential"; n = numarg; ":"; c2 = Command.command; ":=";
        c1 = Command.command; "." ->
          <:ast< (EXISTENTIAL $n (COMMAND (CAST $c1 $c2))) >>
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

(* Tactic Definition *)

      | IDENT "Tactic"; "Definition"; id = identarg; "[";
        ids = ne_identarg_list; "]"; ":="; tac = Prim.astact; "." ->
          <:ast< (TacticDefinition $id (AST $tac) ($LIST $ids)) >>
      | IDENT "Tactic"; "Definition"; id = identarg; ":="; tac = Prim.astact;
        "." -> <:ast< (TacticDefinition $id (AST $tac)) >>

(* Hints for Auto and EAuto *)

      | IDENT "Hint"; hintname = identarg; dbname = opt_identarg_list; ":=";
	IDENT "Resolve"; c = comarg; "." ->
	  <:ast<(HintResolve $hintname (VERNACARGLIST ($LIST $dbname)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Immediate"; c = comarg; "." ->
	  <:ast<(HintImmediate $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Unfold"; c = identarg; "." ->
	  <:ast<(HintUnfold $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Constructors"; c = identarg;  "." ->
	  <:ast<(HintConstructors $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Extern"; n = numarg; c = comarg ; tac = tacarg; "." ->
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
                hyptyp = comarg;
                pri = numarg;
                tac = Prim.astact; "." -> 
          <:ast< (HintDestruct $na (AST $dloc) $hyptyp $pri (AST $tac))>>

      | n = numarg; ":"; tac = tacarg; "." ->
          <:ast< (SOLVE $n (TACTIC $tac)) >> 

(*This entry is not commented, only for debug*)
      | IDENT "PrintConstr"; com = comarg; "." ->
          <:ast< (PrintConstr $com)>>
      ] ];
  END
