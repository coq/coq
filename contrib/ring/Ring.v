
(* $Id$ *)

Require Export Bool.
Require Export Ring_theory.
Require Export Quote.
Require Export Ring_normalize.
Require Export Ring_abstract.

Declare ML Module "ring".

Grammar tactic simple_tactic : Ast :=
  ring [ "Ring" constrarg_list($arg) ] -> [(Ring ($LIST $arg))].

Syntax tactic level 0:
  ring [ << (Ring ($LIST $lc)) >> ] -> [ "Ring" [1 1] (LISTSPC ($LIST $lc)) ] 
| ring_e [ << (Ring) >> ] -> ["Ring"].
 
Grammar vernac vernac : Ast := 
  addring [ "Add" "Ring" 
      	     constrarg($a) constrarg($aplus) constrarg($amult) constrarg($aone)
      	     constrarg($azero) constrarg($aopp) constrarg($aeq) constrarg($t)
      	     "[" ne_constrarg_list($l) "]" "." ] 
  -> [(AddRing $a $aplus $amult $aone $azero $aopp $aeq $t
      	 ($LIST $l))]

| addsemiring [ "Add" "Semi" "Ring" 
      	       	 constrarg($a) constrarg($aplus) constrarg($amult) 
                 constrarg($aone) constrarg($azero) constrarg($aeq) 
                 constrarg($t) 
      	       	 "[" ne_constrarg_list($l) "]" "." ] 
  -> [(AddSemiRing $a $aplus $amult $aone $azero $aeq $t
      	   ($LIST $l))]
| addabstractring [ "Add" "Abstract" "Ring" 
      	     constrarg($a) constrarg($aplus) constrarg($amult)
             constrarg($aone) constrarg($azero) constrarg($aopp)
             constrarg($aeq) constrarg($t) "." ] 
  -> [(AddAbstractRing $a $aplus $amult $aone $azero $aopp $aeq $t)]

| addabstractsemiring [ "Add" "Abstract" "Semi" "Ring" 
      	       	 constrarg($a) constrarg($aplus) constrarg($amult) 
                 constrarg($aone) constrarg($azero) constrarg($aeq) 
                 constrarg($t) "." ] 
  -> [(AddAbstractSemiRing $a $aplus $amult $aone $azero $aeq $t )]
.

(* As an example, we provide an instantation for bool. *)
(* Other instatiations are given in ArithRing and ZArithRing in the
   same directory *)

Definition BoolTheory : (Ring_Theory xorb andb true false [b:bool]b eqb).
Split; Simpl.
Destruct n; Destruct m; Reflexivity.
Destruct n; Destruct m; Destruct p; Reflexivity.
Destruct n; Destruct m; Reflexivity.
Destruct n; Destruct m; Destruct p; Reflexivity.
Destruct n; Reflexivity.
Destruct n; Reflexivity.
Destruct n; Reflexivity.
Destruct n; Destruct m; Destruct p; Reflexivity.
Destruct x; Destruct y; Reflexivity Orelse Tauto.
Defined.

Add Ring bool xorb andb true false [b:bool]b eqb BoolTheory [ true false ].
