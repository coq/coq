(** TODO: Figure out how to test "sanity" for the ltac profiler output *)
Fixpoint fact (n : nat) := match n with 0 => 1 | S n' => n * fact n' end.
Fixpoint walk (n : nat) := match n with 0 => tt | S n => walk n end.
Ltac slow := idtac + (do 2 (let x := eval lazy in (walk (fact 9)) in idtac)).
Ltac slow2 := idtac + (do 2 (let x := eval lazy in (walk (fact 9)) in idtac)).
Ltac multi := idtac + slow + slow2.
Set Ltac Profiling.
Goal True.
  Time try (multi; fail).
  (* Warning: Ltac Profiler cannot yet handle backtracking into multi-success
 tactics; profiling results may be wildly inaccurate.
 [profile-backtracking,ltac] *)
  Show Ltac Profile.
  (* Used to be:
total time:      0.000s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─multi ---------------------------------  47.1%  47.1%       1    0.000s
─slow ----------------------------------  35.3%  35.3%       1    0.000s
─slow2 ---------------------------------  17.6%  17.6%       1    0.000s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─multi ---------------------------------  47.1%  47.1%       1    0.000s
─slow ----------------------------------  35.3%  35.3%       1    0.000s
─slow2 ---------------------------------  17.6%  17.6%       1    0.000s

   *)
  (* Now:
total time:      2.074s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─multi ---------------------------------   0.0% 100.0%       6    1.119s
─slow ----------------------------------  54.0%  54.0%       3    1.119s
─slow2 ---------------------------------  46.0%  46.0%       3    0.955s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─multi ---------------------------------   0.0% 100.0%       6    1.119s
 ├─slow --------------------------------  54.0%  54.0%       3    1.119s
 └─slow2 -------------------------------  46.0%  46.0%       3    0.955s

*)
Abort.
