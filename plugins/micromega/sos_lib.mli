(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val o : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

val num_1 : Num.num
val pow10 : int -> Num.num
val pow2 : int -> Num.num

val implode : string list -> string
val explode : string -> string list

val funpow : int -> ('a -> 'a) -> 'a -> 'a
val tryfind : ('a -> 'b) -> 'a list -> 'b

type ('a,'b) func =
 | Empty
 | Leaf of int * ('a*'b) list
 | Branch of int * int * ('a,'b) func * ('a,'b) func

val undefined : ('a, 'b) func
val is_undefined : ('a, 'b) func -> bool
val (|->) : 'a -> 'b -> ('a, 'b) func -> ('a, 'b) func
val (|=>) : 'a -> 'b -> ('a, 'b) func
val choose : ('a, 'b) func -> 'a * 'b
val combine : ('a -> 'a -> 'a) -> ('a -> bool) -> ('b, 'a) func -> ('b, 'a) func -> ('b, 'a) func
val (--) : int -> int -> int list

val tryapplyd : ('a, 'b) func -> 'a -> 'b -> 'b
val apply : ('a, 'b) func -> 'a -> 'b

val foldl : ('a -> 'b -> 'c -> 'a) -> 'a -> ('b, 'c) func -> 'a
val foldr : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) func -> 'c -> 'c
val mapf : ('a -> 'b) -> ('c, 'a) func -> ('c, 'b) func

val undefine : 'a -> ('a, 'b) func -> ('a, 'b) func

val dom : ('a, 'b) func -> 'a list
val graph : ('a, 'b) func -> ('a * 'b) list

val union : 'a list -> 'a list -> 'a list
val subtract : 'a list -> 'a list -> 'a list
val sort : ('a -> 'a -> bool) -> 'a list -> 'a list
val setify : 'a list -> 'a list
val increasing : ('a -> 'b) -> 'a -> 'a -> bool
val allpairs : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

val gcd_num : Num.num -> Num.num -> Num.num
val lcm_num : Num.num -> Num.num -> Num.num
val numerator : Num.num -> Num.num
val denominator : Num.num -> Num.num
val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a

val (>>) : ('a -> 'b * 'c) -> ('b -> 'd) -> 'a -> 'd * 'c
val (++) : ('a -> 'b * 'c) -> ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e

val a : 'a -> 'a list -> 'a * 'a list
val many : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
val some : ('a -> bool) -> 'a list -> 'a * 'a list
val possibly : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
val isspace : string -> bool
val parser_or : ('a -> 'b) -> ('a -> 'b) -> 'a -> 'b
val isnum : string -> bool
val atleast : int -> ('a -> 'b * 'a) -> 'a -> 'b list * 'a
val listof : ('a -> 'b * 'c) -> ('c -> 'd * 'a) -> string -> 'a -> 'b list * 'c

val temp_path : string
val string_of_file : string -> string
val file_of_string : string -> string -> unit

val deepen_until : int -> (int -> 'a) -> int -> 'a
exception TooDeep
