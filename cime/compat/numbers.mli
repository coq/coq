


(*

  the type of numbers (integer or rational)

*)

type t;;

val hash : t -> int;;

(*

  basic constants and conversion from machine ints

*)

val zero : t;;
val one : t;;
val two : t
val minus_one : t
val of_int : int -> t;;

(* 

   raises [Invalid_argument "Numbers.to_int"] if too big 

*)

val to_int : t -> int;;

(*

 basic operations overs rational numbers

*)

val is_zero : t -> bool;;
val denominator : t -> t

val add : t -> t -> t;;
val sub : t -> t -> t;;
val minus : t -> t;;
val abs : t -> t;;

val mult : t -> t -> t;;
val div : t -> t -> t;; 
val power_int : t -> int -> t;;


(*

  comparators

*)

val compare : t -> t -> int;;
val eq : t -> t -> bool;;
val neq : t -> t -> bool;;
val ge : t -> t -> bool;;
val gt : t -> t -> bool;;
val le : t -> t -> bool;;
val lt : t -> t -> bool;;
val max : t -> t -> t;;
val min : t -> t -> t;;

(*

integer operations

*)

val succ : t -> t;;
val pred : t -> t;;
val quo : t -> t -> t;;
val modulo : t -> t -> t;;

val pgcd : t -> t -> t
val full_pgcd : t -> t -> t * t * t
val ppcm : t -> t -> t

val div_floor : t -> t -> t
val div_ceil : t -> t -> t
val sqrt_floor : t -> t
val sqrt_ceil : t -> t
val root_floor : int -> t -> t
val root_ceil : int -> t -> t



(*

  parsing and printing

*)

val from_string : string -> t;;
val to_string : t -> string;;



