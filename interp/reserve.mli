open Names
open Rawterm

val declare_reserved_type : identifier -> rawconstr -> unit
val find_reserved_type : identifier -> rawconstr
val anonymize_if_reserved : name -> rawconstr -> rawconstr
