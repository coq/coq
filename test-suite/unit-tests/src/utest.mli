(** give a name to a unit test *)
val mk_test : string -> OUnit.test -> OUnit.test

(** simple ways to build a test *)
val mk_eq_test : string -> string -> 'a -> 'a -> OUnit.test
val mk_bool_test : string -> string -> bool -> OUnit.test

(** run unit tests *)
(* the string argument should be the name of the .ml file
   containing the tests; use __FILE__ for that purpose.
 *)
val run_tests : string -> out_channel -> OUnit.test list -> unit

(** open output channel for the test log file *)
(* the string argument should be the name of the .ml file
   containing the tests; use __FILE__ for that purpose.
 *)
val open_log_out_ch : string -> out_channel
