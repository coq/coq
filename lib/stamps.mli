
(*i $Id$ i*)

(* Time stamps. *)

type 'a timestamped

(* [ts_mod] gives a ['b timestamped] with a new stamp *)
val ts_mod : ('a -> 'b) -> 'a timestamped -> 'b timestamped
val ts_it : 'a timestamped -> 'a
val ts_mk : 'a -> 'a timestamped
val ts_eq : 'a timestamped -> 'a timestamped -> bool
val ts_stamp : 'a timestamped -> int

type 'a idstamped

(* [ids_mod] gives a ['b stamped] with the same stamp *)
val ids_mod : ('a -> 'b) -> 'a idstamped -> 'b idstamped
val ids_it : 'a idstamped -> 'a
val ids_mk : 'a -> 'a idstamped
val ids_eq : 'a idstamped -> 'a idstamped -> bool
