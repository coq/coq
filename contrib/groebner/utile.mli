
(* Printing *)
val pr : string -> unit
val prn : string -> unit
val prt0 : 'a -> unit
val prt : string -> unit
val info : string -> unit

(* Array *)
val compte : 'a array -> 'a -> int
val maximum : int array -> int
val matrix_map : ('a -> 'b) -> 'a array array -> 'b array array
val array_select : ('a -> bool) -> 'a array -> 'a array
val array_test : ('a -> bool) -> 'a array -> bool
val array_find : 'a -> 'a array -> int

(* Listes *)
val set_of_list : 'a list -> 'a list
val list_mem_eq : ('a -> 'b -> bool) -> 'a -> 'b list -> bool
val set_of_list_eq : ('a -> 'a -> bool) -> 'a list -> 'a list
val list_select : ('a -> bool) -> 'a list -> 'a list

(* Memoization *)
val memo :
  ('a * 'b) list ref -> ('a -> 'a -> bool) -> 'b -> ('a -> 'b) -> 'a -> 'b
val memos :
  string -> ('a, 'b) Hashtbl.t -> ('c -> 'a) -> ('c -> 'b) -> 'c -> 'b


val facteurs_liste : ('a -> 'a -> 'a) -> ('a -> bool) -> 'a list -> 'a list
val factorise_tableau :
  ('a -> 'b -> 'a) ->
  ('a -> bool) ->
  'a -> 'a array -> 'b array -> 'b array * ('a * int list) array
