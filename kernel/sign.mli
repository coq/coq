
(* $Id$ *)

open Names

type 'a signature = identifier list * 'a list
type 'a db_signature = (name * 'a) list
type ('a,'b) env = ENVIRON of 'a signature * 'b db_signature

val nil_sign : 'a signature
val add_sign : (identifier * 'a) -> 'a signature -> 'a signature
val lookup_sign : identifier -> 'a signature -> (identifier * 'a)

val rev_sign : 'a signature -> 'a signature
val map_sign_typ : ('a -> 'b) -> 'a signature -> 'b signature
val isnull_sign : 'a signature -> bool
val hd_sign : 'a signature -> identifier * 'a
val tl_sign : 'a signature -> 'a signature
val sign_it : (identifier -> 'a -> 'b -> 'b) -> 'a signature -> 'b -> 'b
val it_sign : ('b -> identifier -> 'a -> 'b) -> 'b -> 'a signature -> 'b
val concat_sign : 'a signature -> 'a signature -> 'a signature
val ids_of_sign : 'a signature -> identifier list
val vals_of_sign : 'a signature -> 'a list

val nth_sign : 'a signature -> int -> (identifier * 'a)
val map_sign_graph : (identifier -> 'a -> 'b) -> 'a signature -> 'b list
val list_of_sign : 'a signature -> (identifier * 'a) list
val make_sign    : (identifier * 'a) list -> 'a signature
val do_sign : (identifier -> 'a -> unit) -> 'a signature -> unit
val uncons_sign : 'a signature -> (identifier * 'a) * 'a signature
val sign_length : 'a signature -> int
val mem_sign    : 'a signature -> identifier -> bool
val modify_sign : identifier -> 'a -> 'a signature -> 'a signature

val exists_sign : (identifier -> 'a -> bool) -> 'a signature -> bool
val sign_prefix : identifier -> 'a signature -> 'a signature
val add_sign_after : 
  identifier -> (identifier * 'a) -> 'a signature -> 'a signature
val add_sign_replacing : 
  identifier -> (identifier * 'a) -> 'a signature -> 'a signature
val prepend_sign : 'a signature -> 'a signature -> 'a signature


val gLOB : 'b signature -> ('b,'a) env

val add_rel : (name * 'a) -> ('b,'a) env -> ('b,'a) env 
val add_glob : (identifier * 'b) -> ('b,'a) env -> ('b,'a) env
val lookup_glob : identifier -> ('b,'a) env -> (identifier * 'b)
val lookup_rel : int -> ('b,'a) env  -> (name * 'a)
val mem_glob : identifier -> ('b,'a) env -> bool

val get_globals : ('b,'a) env -> 'b signature
val get_rels : ('b,'a) env -> 'a db_signature
val dbenv_it : (name -> 'b -> 'c -> 'c) -> ('a,'b) env -> 'c -> 'c
val it_dbenv : ('c -> name -> 'b -> 'c) -> 'c -> ('a,'b) env -> 'c
val map_rel_env : ('a -> 'b) -> ('c,'a) env -> ('c,'b) env
val map_var_env : ('c -> 'b) -> ('c,'a) env -> ('b,'a) env
val isnull_rel_env : ('a,'b) env -> bool
val uncons_rel_env : ('a,'b) env -> (name * 'b) * ('a,'b) env
val ids_of_env : ('a, 'b) env -> identifier list

type ('b,'a) search_result =
  | GLOBNAME of identifier  * 'b
  | RELNAME of int * 'a

val lookup_id : identifier -> ('b,'a) env -> ('b,'a) search_result


