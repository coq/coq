
val generate_functional_principle : 
  (* do we accept interactive proving *)
  bool ->
  (* induction principle on rel *) 
  Term.types ->
  (* *)
  Term.sorts array option -> 
  (* Name of the new principle *) 
  (Names.identifier) option -> 
  (* the compute functions to use   *)
  Names.constant array -> 
  (* We prove the nth- principle *)
  int  ->
  (* The tactic to use to make the proof w.r
     the number of params
  *)
  (Term.constr array -> int -> Tacmach.tactic) -> 
  unit



(* val my_reflexivity : Tacmach.tactic  *)

val prove_princ_for_struct : 
  bool -> 
  int -> Names.constant array -> Term.constr array -> int -> Tacmach.tactic


val compute_new_princ_type_from_rel : Term.constr array -> Term.sorts array -> 
  Term.types -> Term.types

val make_scheme : (Names.identifier*Names.identifier*Rawterm.rawsort) list ->  unit
val make_case_scheme : (Names.identifier*Names.identifier*Rawterm.rawsort)  ->  unit
