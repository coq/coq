
(* $Id$ *)

open Pcoq
open Command

GEXTEND Gram
  pattern_list:
    [ [  -> []
      | p = pattern; pl = pattern_list -> p :: pl ] ]
  ;
(*
  lsimple_pattern:
    [ [ c = simple_pattern2 -> c ] ]
  ;
*)
  pattern:
    [ [ id = ident -> id
      | "("; p = lsimple_pattern; ")" -> p ] ]
  ;
  simple_pattern_list:
    [ [  -> []
      | p = simple_pattern; pl = simple_pattern_list ->
	   p :: pl ] ]
  ;
  lsimple_pattern:
    [ [ id = ident; lp = ne_pattern_list ->
	  <:ast< (PATTCONSTRUCT $id ($LIST $lp)) >>
      | p = pattern; "as"; id = ident -> <:ast< (PATTAS $id $p)>>
      | c1 = simple_pattern; ","; c2 = simple_pattern ->
          <:ast< (PATTCONSTRUCT pair $c1 $c2) >>
      | "("; p = lsimple_pattern; ")" -> p ] ]
  ;
(*
  pattern:
    [ [ p = simple_pattern -> p ] ]
  ;
*)
  ne_pattern_list:
    [ [ c1 = pattern; cl = ne_pattern_list -> c1 :: cl
      | c1 = pattern -> [c1] ] ]
  ;
  equation:
    [ [ lhs = ne_pattern_list; "=>"; rhs = command ->
	      <:ast< (EQN $rhs ($LIST $lhs)) >> ] ]
  ;
  ne_eqn_list:
    [ [ e = equation; "|"; leqn = ne_eqn_list -> e :: leqn
      | e = equation -> [e] ] ]
  ;

  command1:
    [ [ "<"; l1 = lcommand; ">"; "Cases"; lc = ne_command_list; "of";
        OPT "|"; eqs = ne_eqn_list; "end" ->
          <:ast< (MULTCASE $l1 (TOMATCH ($LIST $lc)) ($LIST $eqs)) >>
      | "Cases"; lc = ne_command_list; "of";
	OPT "|"; eqs = ne_eqn_list; "end" ->
          <:ast< (MULTCASE "SYNTH" (TOMATCH ($LIST $lc)) ($LIST $eqs)) >>
      | "<"; l1 = lcommand; ">"; "Cases"; lc = ne_command_list; "of";
        "end" ->
          <:ast< (MULTCASE $l1 (TOMATCH ($LIST $lc))) >>
      | "Cases"; lc = ne_command_list; "of"; "end" -> 
          <:ast< (MULTCASE "SYNTH" (TOMATCH ($LIST $lc))) >> ] ]
  ;
END;
