
(* $Id$ *)

(* These are the entries without which MakeBare cannot be compiled *)

open Pcoq

open Vernac

GEXTEND Gram
  vernac:
    [ RIGHTA

     [ "Load"; verbosely = [ IDENT "Verbose" -> "Verbose" | -> "" ];
       s = [ s = STRING -> s | s = IDENT -> s ]; "." ->
         <:ast< (LoadFile ($STR $verbosely) ($STR $s)) >>

     | "Compile";
       verbosely =
         [ IDENT "Verbose" -> "Verbose"
         | -> "" ];
       IDENT "Module";
       only_spec =
         [ IDENT "Specification" -> "Specification"
         | -> "" ];
       mname = [ s = STRING -> s | s = IDENT -> s ];
       fname = OPT [ s = STRING -> s | s = IDENT -> s ]; "." ->
         let fname = match fname with Some s -> s | None -> mname in
         <:ast< (CompileFile ($STR $verbosely) ($STR $only_spec)
                   ($STR $mname) ($STR $fname))>> ]]
  ;
END

GEXTEND Gram
  GLOBAL: vernac Prim.syntax_entry Prim.grammar_entry;

  vernac:
    [[ "Token"; s = STRING; "." -> <:ast< (TOKEN ($STR $s)) >>

     | "Grammar"; univ=IDENT; tl=LIST1 Prim.grammar_entry SEP "with"; "." ->
         <:ast< (GRAMMAR ($VAR univ) (ASTLIST ($LIST tl))) >>

     | "Syntax"; whatfor=IDENT; el=LIST1 Prim.syntax_entry SEP ";"; "." ->
         <:ast< (SYNTAX ($VAR whatfor) (ASTLIST ($LIST el))) >>
     | IDENT "Infix"; as_ = entry_prec; n = numarg; op = Prim.string;
       p = identarg; "." -> <:ast< (INFIX (AST $as_) $n $op $p) >>
     | IDENT "Distfix"; as_ = entry_prec; n = numarg; s = Prim.string;
       p = identarg; "." -> <:ast< (DISTFIX (AST $as_) $n $s $p) >> ]]
  ;

  (* Syntax entries for Grammar. Only grammar_entry is exported *)
  Prim.grammar_entry:
    [[ nont = Prim.ident; etyp = Prim.entry_type; ":=";
       ep = entry_prec; rl = LIST0 grammar_rule SEP "|" ->
         <:ast< (GRAMMARENTRY $nont $etyp $ep ($LIST rl)) >> ]]
  ;
  entry_prec:
    [[ IDENT "LEFTA" -> <:ast< {LEFTA} >>
     | IDENT "RIGHTA" -> <:ast< {RIGHTA} >>
     | IDENT "NONA" -> <:ast< {NONA} >>
     | ->  <:ast< {NONE} >> ] ]
  ;
  grammar_rule:
    [[ name = rule_name; "["; pil = LIST0 production_item; "]"; "->";
       a = Prim.astact ->
        <:ast< (GRAMMARRULE ($ID name) $a ($LIST pil)) >> ]]
  ;
  rule_name:
    [[ name = IDENT -> name ]]
  ;
  production_item:
    [[ s = STRING -> <:ast< ($STR $s) >>
     | nt = non_terminal; po = OPT [ "("; p = Prim.ident; ")" -> p ] ->
         match po with
           | Some p -> <:ast< (NT $nt $p) >>
           | _ -> <:ast< (NT $nt) >> ]]
  ;
  non_terminal:
    [[ u = Prim.ident; ":"; nt = Prim.ident -> <:ast< (QUAL $u $nt) >>
     | nt = Prim.ident -> <:ast< $nt >> ]]
  ;


  (* Syntax entries for Syntax. Only syntax_entry is exported *)
  Prim.syntax_entry:
    [ [ IDENT "level"; p = precedence; ":"; rl = LIST1 syntax_rule SEP "|" ->
          <:ast< (SYNTAXENTRY $p ($LIST $rl)) >> ] ]
  ;
  syntax_rule:
    [ [ nm = IDENT; "["; s = Prim.astpat; "]"; "->"; u = unparsing ->
          <:ast< (SYNTAXRULE ($ID $nm) $s $u) >> ] ]
  ;
  precedence:
    [ [ a = Prim.number ->  <:ast< (PREC $a 0 0) >>
      | "["; a1 = Prim.number; a2 = Prim.number; a3 = Prim.number; "]" ->
          <:ast< (PREC $a1 $a2 $a3) >> ] ]
  ;
  unparsing:
    [ [ "["; ll = LIST0 next_hunks; "]" -> <:ast< (UNPARSING ($LIST $ll))>> ] ]
  ;
  next_hunks:
    [ [ IDENT "FNL" -> <:ast< (UNP_FNL) >>
      | IDENT "TAB" -> <:ast< (UNP_TAB) >>
      | c = STRING -> <:ast< (RO ($STR $c)) >>
      | "[";
        x =
          [ b = box; ll = LIST0 next_hunks -> <:ast<(UNP_BOX $b ($LIST $ll))>>
          | n = Prim.number; m = Prim.number -> <:ast< (UNP_BRK $n $m) >>
          | IDENT "TBRK";
            n = Prim.number; m = Prim.number -> <:ast< (UNP_TBRK $n $m) >> ];
        "]" -> x
      | e = Prim.ast; oprec = OPT [ ":"; pr = paren_reln_or_extern -> pr ] ->
          match oprec with
	    | Some pr -> <:ast< (PH $e $pr) >>
            | None -> <:ast< (PH $e {Any}) >> ]]
  ;
  box:
    [ [ "<"; bk = box_kind; ">" -> bk ] ]
  ;
  box_kind:
    [ [ IDENT "h"; n = Prim.number -> <:ast< (PpHB $n) >>
      | IDENT "v"; n = Prim.number -> <:ast< (PpVB $n) >>
      | IDENT "hv"; n = Prim.number -> <:ast< (PpHVB $n) >>
      | IDENT "hov"; n = Prim.number -> <:ast< (PpHOVB $n) >>
      | IDENT "t" -> <:ast< (PpTB) >> ] ]
  ;
  paren_reln_or_extern:
    [ [ IDENT "L" -> <:ast< {L} >>
      | IDENT "E" -> <:ast< {E} >>
      | pprim = STRING; precrec = OPT [ ":"; p = precedence -> p ] ->
	  match precrec with
	    | Some p -> <:ast< (EXTERN ($STR $pprim) $p) >>
            | None -> <:ast< (EXTERN ($STR $pprim)) >> ] ]
  ;
END

