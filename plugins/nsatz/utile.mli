
(* Printing *)
val pr : string -> unit
val prn : string -> unit
val prt0 : 'a -> unit
val prt : string -> unit
val info : (unit -> string) -> unit
val sinfo : string -> unit

(* Listes *)
val list_mem_eq : ('a -> 'b -> bool) -> 'a -> 'b list -> bool
val set_of_list_eq : ('a -> 'a -> bool) -> 'a list -> 'a list


val facteurs_liste : ('a -> 'a -> 'a) -> ('a -> bool) -> 'a list -> 'a list
val factorise_tableau :
  ('a -> 'b -> 'a) ->
  ('a -> bool) ->
  'a -> 'a array -> 'b array -> 'b array * ('a * int list) array
