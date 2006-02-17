
val generate_new_structural_principle : 
  (* do we accept interactive proving *)
  bool ->
  (* induction principle on rel *) 
  Names.constant ->
  (* Name of the new principle *) 
  (Names.identifier) option -> 
  (* the compute functions to use   *)
  Names.constant array -> 
  (* We prove the nth- principle *)
  int  ->
  (* The tactic to use to make the proof w.r
     the number of params
  *)
  (int -> Tacmach.tactic) -> 
  unit



val my_reflexivity : Tacmach.tactic 

val prove_princ_for_struct : int -> Names.constant array -> int -> Tacmach.tactic
