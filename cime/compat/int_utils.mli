
(*

  [power], [pgcd] = greatest common divisor, [ppcm] = least common multiple. 
 
  [full_pgcd x y] returns [d,k1,k2] such that d=gcd(x,y), x=k1*d and y=k2*d. 

*)

val power : int -> int -> int
val pgcd : int -> int -> int
val full_pgcd : int -> int -> int * int * int
val ppcm : int -> int -> int

(*i
val div_floor : int -> int -> int
val div_ceil : int -> int -> int
val sqrt_floor : int -> int
val sqrt_ceil : int -> int
val root_floor : int -> int -> int
val root_ceil : int -> int -> int
i*)
