Declare ML Module "paths".
Declare ML Module "name_to_ast".
Declare ML Module "xlate".
Declare ML Module "vtp".
Declare ML Module "translate".
Declare ML Module "pbp".
Declare ML Module "dad".
(*
Declare ML Module "showproofutil".
Declare ML Module "showproof_ct".
Declare ML Module "showproof".
Declare ML Module "fine_search".
*)
Declare ML Module "debug_tac".
Declare ML Module "paths".
Declare ML Module "history".
Declare ML Module "centaur".
(* Require Export Illustrations. *)
Require Export AddDad.

Grammar vernac vernac : ast :=
  goal_cmd [ "Goal" "Cmd" numarg($n) "with" tacarg($tac) "." ] ->
        [(GOAL_CMD $n (TACTIC $tac))]
| kill_proof_after [ "Kill" "Proof" "after"  numarg($n)"." ] -> [(KILL_NODE $n)]
| kill_proof_at [ "Kill" "Proof" "at"  numarg($n)"." ] -> [(KILL_NODE $n)]
| kill_sub_proof [ "Kill" "SubProof" numarg($n) "." ] -> [(KILL_SUB_PROOF $n)]

| print_past_goal [ "Print" "Past" "Goal" numarg($n) "." ] ->
        [(PRINT_GOAL_AT $n) ]

| check_in_goal [ "CHECK_IN_GOAL" numarg($n) constrarg($c) "." ] ->
       [(CHECK_IN_GOAL "CHECK" $n $c)]
| eval_in_goal [ "EVAL_IN_GOAL" numarg($n) constrarg($c) "." ] ->
       [(CHECK_IN_GOAL "EVAL" $n $c)]
| compute_in_goal [ "COMPUTE_IN_GOAL" numarg($n) constrarg($c) "." ] ->
       [(CHECK_IN_GOAL "COMPUTE" $n $c)]
| centaur_reset [ "Centaur" "Reset" identarg($id) "." ] -> [(Centaur_Reset $id)]
| show_dad_rules [ "Show" "Dad" "Rules" "." ] -> [(Show_dad_rules)]
| start_pcoq [ "Start" "Pcoq" "Mode" "." ] -> [ (START_PCOQ) ]
| start_pcoq [ "Start" "Pcoq" "Debug" "Mode" "." ] -> [ (START_PCOQ_DEBUG) ].
Grammar vernac ne_id_list : List :=
   id_one [ identarg($id)] -> [$id]
 | id_more [identarg($id) ne_id_list($others)] -> [$id ($LIST $others)].

Grammar tactic ne_num_list : List :=
  ne_last [ numarg($n) ] -> [ $n ]
| ne_num_ste  [ numarg($n) ne_num_list($ns) ] -> [ $n ($LIST $ns)].

Grammar tactic two_numarg_list : List :=
  two_single_and_ne [ numarg($n) "to"  ne_num_list($ns)] ->
        [$n (TACTIC (to)) ($LIST $ns)]
| two_rec [ numarg($n) two_numarg_list($ns)] -> [ $n ($LIST $ns)].

Grammar tactic simple_tactic : ast :=
  pbp0 [ "Pbp" ] -> [(PcoqPbp)]
| pbp1 [ "Pbp" ne_num_list($ns) ] ->
         [ (PcoqPbp ($LIST $ns)) ]
| pbp2 [ "Pbp" identarg($id) ] -> [ (PcoqPbp $id) ]
| pbp3 [ "Pbp" identarg($id) ne_num_list($ns)] ->
         [ (PcoqPbp $id ($LIST $ns)) ]
| dad00 [ "Dad" "to" ] -> [(Dad (TACTIC (to)))]
| dad01 [ "Dad" "to" ne_num_list($ns) ] ->
        [(Dad (TACTIC (to)) ($LIST $ns))]
| dadnn [ "Dad" two_numarg_list($ns) ] -> [ (Dad ($LIST $ns)) ]
| debug_tac [ "DebugTac" tactic($tac) ] ->
  [(CtDebugTac (TACTIC $tac))]
| on_then_empty [ "OnThen" tactic($tac1) tactic($tac2) ] ->
    [(OnThen (TACTIC $tac1) (TACTIC $tac2))]
| on_then_ne [ "OnThen" tactic($tac1) tactic($tac2) ne_num_list($l) ] ->
  [(OnThen (TACTIC $tac1) (TACTIC $tac2) ($LIST $l))]
| debug_tac2 [ "DebugTac2" tactic($tac) ] ->
  [(CtDebugTac2 (TACTIC $tac))].


(* Maybe we should have syntactic rules to make sur that syntax errors are
   displayed with a readable syntax.  It is not sure, since the error reporting
   procedure changed from V6.1 and does not reprint the command anymore. *)
Grammar vernac vernac : ast :=
  text_proof_flag_on [ "Text" "Mode" "On" "." ] ->
       [(TEXT_MODE (AST {on}))]
| text_proof_flag_on [ "Text" "Mode" "Off" "." ] ->
       [(TEXT_MODE (AST {off}))].


