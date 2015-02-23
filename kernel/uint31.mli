type t

      (* conversion to int *)
val to_int : t -> int
val of_int : int -> t
val of_uint : int -> t

     (* conversion to a string *)
val to_string : t -> string
val of_string : string -> t

      (* logical operations *)
val l_sl    : t -> t -> t
val l_sr    : t -> t -> t
val l_and   : t -> t -> t
val l_xor   : t -> t -> t
val l_or    : t -> t -> t

      (* Arithmetic operations *) 
val add     : t -> t -> t
val sub     : t -> t -> t
val mul     : t -> t -> t
val div     : t -> t -> t
val rem     : t -> t -> t
      
      (* Specific arithmetic operations *)
val mulc    : t -> t -> t * t
val div21   : t -> t -> t -> t * t
      
      (* comparison *)
val lt      : t -> t -> bool
val equal   : t -> t -> bool
val le      : t -> t -> bool
val compare : t -> t -> int

      (* head and tail *)
val head0   : t -> t
val tail0   : t -> t

(** Used by retroknowledge *)
val add_digit : t -> t -> t
