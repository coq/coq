
(*i $Id$ i*)

(* Profiling. *)

type profile_key

val actif : bool ref
val print_profile : unit -> unit
val reset_profile : unit -> unit
val init_profile : unit -> unit
val declare_profile : string -> profile_key
val profile : profile_key -> ('a -> 'b) -> 'a -> 'b
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
