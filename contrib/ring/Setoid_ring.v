Require Export Setoid_ring_theory.
Require Export Quote.
Require Export Setoid_ring_normalize.

Declare ML Module "ring".

Grammar tactic simple_tactic : ast :=
  ring [ "Ring" constrarg_list($arg) ] -> [(Ring ($LIST $arg))].

Syntax tactic level 0:
  ring [ << (Ring ($LIST $lc)) >> ] -> [ "Ring" [1 1] (LISTSPC ($LIST $lc)) ] 
| ring_e [ << (Ring) >> ] -> ["Ring"].

Grammar vernac vernac : ast := 
| addsetoidring [ "Add" "Setoid" "Ring"
      	    constrarg($a) constrarg($aequiv) constrarg($asetth) constrarg($aplus) constrarg($amult) 
	    constrarg($aone) constrarg($azero) constrarg($aopp) constrarg($aeq) constrarg($pm)
	    constrarg($mm) constrarg($om) constrarg($t) "[" ne_constrarg_list($l) "]" "." ] 
  -> [(AddSetoidRing $a $aequiv $asetth $aplus $amult $aone $azero $aopp $aeq $pm $mm $om $t
      	 ($LIST $l))]
| addsetoidsemiring [ "Add" "Semi" "Setoid" "Ring" 
      	  constrarg($a) constrarg($aequiv) constrarg($asetth) constrarg($aplus)
	  constrarg($amult) constrarg($aone) constrarg($azero) constrarg($aeq) 
          constrarg($pm) constrarg($mm) constrarg($t) "[" ne_constrarg_list($l) "]" "." ] 
  -> [(AddSemiSetoidRing $a $aequiv $asetth $aplus $amult $aone $azero $aeq $pm $mm $t
      	   ($LIST $l))]
.
