(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 This program is a small time and allocation profiler for Objective Caml } *)

(** Adapted from Christophe Raffalli *)

(** To use it, link it with the program you want to profile.

To trace a function "f" you first need to get a key for it by using :

let fkey = declare_profile "f";;

(the string is used to print the profile infomation). Warning: this
function does a side effect. Choose the ident you want instead "fkey".

Then if the function has ONE argument add the following just after
the definition of "f" or just after the declare_profile if this one
follows the definition of f.

let f = profile1 fkey f;;

If f has two arguments do the same with profile2, idem with 3, ...
For more arguments than provided in this module, make a new copy of
function profile and adapt for the needed arity.

If you want to profile two mutually recursive functions, you had better
to rename them :

let fkey = declare_profile "f";;
let gkey = declare_profile "g";;
let f' = .... f' ... g'
and g' = .... f' .... g'
;;

let f = profile fkey f';;
let g = profile gkey g';;

Before the program quits, you should call "print_profile ();;". It
produces a result of the following kind:

Function name              Own time Total time  Own alloc Tot. alloc     Calls
f                            0.28      0.47        116        116      5      4
h                            0.19      0.19          0          0      4      0
g                            0.00      0.00          0          0      0      0
others                       0.00      0.47        392        508             9
Est. overhead/total          0.00      0.47       2752       3260

- The first column is the name of the function.
- The third column give the time (utime + stime) spent inside the function.
- The second column give the time spend inside the function minus the
  time spend in other profiled functions called by it
- The 4th and 5th columns give the same for allocated words
- The 6th and 7th columns give the number of calls to the function and
  the number of calls to profiled functions inside the scope of the
  current function

Remarks:

- If a function has a polymorphic type, you need to supply it with at
  least one argument as in "let f a = profile1 fkey f a;;" (instead of
  "let f = profile1 fkey f;;") in order to get generalization of the
  type.
- Each line of the form "let f a = profile1 fkey f a;;" in your code
  counts for 5 words and each line of the form "let f
  = profile1 fkey f;;" counts for 6 words (a word is 4 or 8 bytes
  according to the architecture); this is counted for "others".
- Time fields for functions doing a little job is usually non pertinent.

i*)

type profile_key

val set_recording : string -> unit

val print_profile : unit -> unit
val reset_profile : unit -> unit
val init_profile : unit -> unit
val declare_profile : string -> profile_key

val profile1 : profile_key -> ('a -> 'b) -> 'a -> 'b
val profile2 : profile_key -> ('a -> 'b -> 'c) -> 'a -> 'b -> 'c
val profile3 :
  profile_key -> ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
val profile4 :
  profile_key -> ('a -> 'b -> 'c -> 'd -> 'e) -> 'a -> 'b -> 'c -> 'd -> 'e
val profile5 :
  profile_key ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f) -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f
val profile6 :
  profile_key ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g)
    -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g
val profile7 :
  profile_key ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h)
    -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h
val profile8 :
  profile_key ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i)
    -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i


(** Some utilities to compute the logical and physical sizes and depth
   of ML objects *)

(** Print logical size (in words) and depth of its argument 
   This function does not disturb the heap *)
val print_logical_stats : 'a -> unit

(** Print physical size, logical size (in words) and depth of its argument 
   This function allocates itself a lot (the same order of magnitude
   as the physical size of its argument) *)
val print_stats : 'a -> unit
