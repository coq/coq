Grammar vernac vernac : ast :=
 add_dad_rule00 ["AddDadRule" stringarg($name) constrarg($pat) 
       "first_path" "second_path" tacarg($tac) "."] ->
    [(AddDadRule $name $pat (NUMBERLIST) (NUMBERLIST) (TACTIC $tac))].
Grammar vernac vernac:ast :=
| add_dad_rule01 ["AddDadRule" stringarg($name) constrarg($pat)
       "first_path" "second_path" ne_numarg_list($l) tacarg($tac) "."] ->
    [(AddDadRule $name $pat (NUMBERLIST) (NUMBERLIST ($LIST $l)) (TACTIC $tac))]
| add_dad_rule10 ["AddDadRule" stringarg($name) constrarg($pat)
       "first_path" ne_numarg_list($l) "second_path" tacarg($tac) "."] ->
    [(AddDadRule $name $pat (NUMBERLIST ($LIST $l))(NUMBERLIST) (TACTIC $tac))]
| add_dad_rule11 ["AddDadRule" stringarg($name) constrarg($pat)
       "first_path" ne_numarg_list($l) "second_path" ne_numarg_list($l1)
       tacarg($tac) "."] ->
    [(AddDadRule $name $pat (NUMBERLIST ($LIST $l))(NUMBERLIST ($LIST $l1))
       (TACTIC $tac))].

Grammar vernac vernac : ast :=
 start_dad [ "StartDad" "."] -> [(StartDad)].
