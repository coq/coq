
val from_string : 
  Parameterized_signatures.parameterized_signature -> 
    string -> 
      Parameterized_words.word

val print_env :
  Linear_constraints.var_id list -> unit

val print_letters :
  Parameterized_words.factor list -> unit

val pretty_print :
    Parameterized_words.word -> unit

val interactive_ordering : 
  Parameterized_words.word Orderings_generalities.ordering
