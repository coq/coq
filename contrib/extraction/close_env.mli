
(*i $Id$ i*)

open Names
open Term

val close : global_reference list -> global_reference list

val module_env : identifier -> global_reference list
