
(* $Id$ *)

open Pcoq

open Command

GEXTEND Gram
  pattern_list:
    [ [  -> ([],[])
      | (id1,p) = pattern; (id2,pl) = pattern_list -> (id1@id2,[p :: pl]) ] ]
  ;
  lsimple_pattern:
    [ [ c = simple_pattern2 -> c ] ]
  ;
  simple_pattern:
    [ [ id = ident -> ([Ast.nvar_of_ast id], id)
      | "("; p = lsimple_pattern; ")" -> p ] ]
  ;
  simple_pattern_list:
    [ [  -> ([],[])
      | (id1,p) = simple_pattern; (id2,pl) = simple_pattern_list ->
	   (id1@id2,[p :: pl]) ] ]
  ;
  (* The XTRA"!" means we want to override the implicit arg mecanism of bdize,
     since params are not given in patterns *)
  simple_pattern2:
    [ [ (id1,p) = simple_pattern; (id2,lp) = pattern_list ->
          (id1@id2, <:ast< (APPLIST (XTRA "!" $p) ($LIST $lp)) >>)
      | (id1,p) = simple_pattern; "as"; id = ident ->
          ([Ast.nvar_of_ast id::id1], <:ast< (XTRA"AS" $id $p) >>)
      | (id1,c1) = simple_pattern; ","; (id2,c2) = simple_pattern ->
          (id1@id2, <:ast< (APPLIST (XTRA "!" pair) $c1 $c2) >>) ] ]
  ;
  pattern:
    [ [ p = simple_pattern -> p ] ]
  ;
  ne_pattern_list:
    [ [ (id1,c1) = pattern; (id2,cl) = ne_pattern_list ->
	(id1@id2, [c1 :: cl])
      | (id1,c1) = pattern -> (id1,[c1]) ] ]
  ;
  equation:
    [ [ (ids,lhs) = ne_pattern_list; "=>"; rhs = command ->
          let br =
	    List.fold_right (fun s ast -> CoqAst.Slam loc (Some s) ast)
	      ids
	      <:ast< (XTRA"EQN" $rhs ($LIST $lhs)) >> in
	  let lid = List.map (fun s -> CoqAst.Id loc s) ids in
	  <:ast< (XTRA"LAMEQN"($LIST $lid) $br) >> ] ]
  ;
  ne_eqn_list:
    [ [ e = equation; "|"; leqn = ne_eqn_list -> [e :: leqn]
      | e = equation -> [e] ] ]
  ;

  command1:
    [ [ "<"; l1 = lcommand; ">"; "Cases"; lc = ne_command_list; "of";
        OPT "|"; eqs = ne_eqn_list; "end" ->
          <:ast< (XTRA"MULTCASE" $l1 (XTRA"TOMATCH" ($LIST $lc))
                    ($LIST $eqs)) >>
      | "Cases"; lc = ne_command_list; "of"; 
	OPT "|"; eqs = ne_eqn_list; "end" ->
          <:ast< (XTRA"MULTCASE" (XTRA"SYNTH")
                    (XTRA"TOMATCH"($LIST $lc)) ($LIST $eqs)) >>
      | "<"; l1 = lcommand; ">"; "Cases"; lc = ne_command_list; "of";
        "end" ->
          <:ast< (XTRA"MULTCASE" $l1 (XTRA"TOMATCH" ($LIST $lc))) >>
      | "Cases"; lc = ne_command_list; "of"; "end" -> 
          <:ast< (XTRA"MULTCASE" (XTRA"SYNTH")
                    (XTRA"TOMATCH"($LIST $lc))) >> ] ]
  ;
  END

