type t = Term.rel_declaration list
val assoc : 'a -> ('a * 'b * 'c) list -> 'b * 'c
val assoc_and_index : 'a -> ('a * 'b * 'c) list -> int * 'b * 'c
val id_of_name : Names.name -> Names.identifier
val subst_env : 'a -> 'b -> 'a * 'b
