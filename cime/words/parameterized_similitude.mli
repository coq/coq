
val compute_similitude : 
  Parameterized_words.word -> 
    Parameterized_words.word -> 
      Linear_constraints.formula

val test_similitude :
  Parameterized_words.word -> 
    Parameterized_words.word -> 
      bool

val test_weak_similitude :
  Parameterized_words.word -> 
    Parameterized_words.word -> 
      bool

val is_epsilon :
  Parameterized_words.word -> Linear_constraints.formula
