
val generate_new_structural_principle : 
  (* induction principle on rel *) 
  Names.constant ->
  (* the elimination sort *)
  Term.sorts -> 
  (* Name of the new principle *) 
  (Names.identifier) option -> 
  (* do we want to use a principle with conclusion *)
  bool -> 
  (* the compute functions to use   *)
  Names.constant array -> 
  int  ->
  unit



val my_reflexivity : Tacmach.tactic 
