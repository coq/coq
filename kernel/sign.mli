
(* $Id$ *)

(*i*)
open Names
open Generic
open Term
(*i*)

(* Signatures of named variables. *)

type 'a signature (* = [identifier list * 'a list] *)

val nil_sign : 'a signature
val add_sign : (identifier * 'a) -> 'a signature -> 'a signature
val lookup_sign : identifier -> 'a signature -> (identifier * 'a)

val rev_sign : 'a signature -> 'a signature
val map_sign_typ : ('a -> 'b) -> 'a signature -> 'b signature
val isnull_sign : 'a signature -> bool
val hd_sign : 'a signature -> identifier * 'a
val tl_sign : 'a signature -> 'a signature

(* [sign_it f sign a] iters [f] on [sign] starting from [a] and
   peeling [sign] from the oldest declaration *)

val sign_it : (identifier -> 'a -> 'b -> 'b) -> 'a signature -> 'b -> 'b

(* [it_sign f a sign] iters [f] on [sign] starting from [a] and
   peeling [sign] from the more recent declaration *)

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

val dunbind : identifier -> 'a signature -> 'a -> 'b term 
  -> 'a signature * 'b term
val dunbindv : identifier -> 'a signature -> 'a -> 'b term 
  -> 'a signature * 'b term array
val dbind : 'a signature -> 'b term -> 'a * 'b term
val dbindv : 'a signature -> 'b term array -> 'a * 'b term

(*s Signatures with named and de Bruijn variables. *)

type 'a db_signature (* = [ (name * 'a) list ] *)
type ('a,'b) sign = ENVIRON of 'a signature * 'b db_signature

val gLOB : 'b signature -> ('b,'a) sign

val add_rel : (name * 'a) -> ('b,'a) sign -> ('b,'a) sign 
val add_glob : (identifier * 'b) -> ('b,'a) sign -> ('b,'a) sign
val lookup_glob : identifier -> ('b,'a) sign -> (identifier * 'b)
val lookup_rel : int -> ('b,'a) sign  -> (name * 'a)
val mem_glob : identifier -> ('b,'a) sign -> bool

val nil_dbsign : 'a db_signature
val get_globals : ('b,'a) sign -> 'b signature
val get_rels : ('b,'a) sign -> 'a db_signature
val dbenv_it : (name -> 'b -> 'c -> 'c) -> ('a,'b) sign -> 'c -> 'c
val it_dbenv : ('c -> name -> 'b -> 'c) -> 'c -> ('a,'b) sign -> 'c
val map_rel_env : ('a -> 'b) -> ('c,'a) sign -> ('c,'b) sign
val map_var_env : ('c -> 'b) -> ('c,'a) sign -> ('b,'a) sign
val isnull_rel_env : ('a,'b) sign -> bool
val uncons_rel_env : ('a,'b) sign -> (name * 'b) * ('a,'b) sign
val ids_of_env : ('a, 'b) sign -> identifier list
val number_of_rels : ('b,'a) sign -> int

(*i This is for Cases i*)
(* raise [Not_found] if the integer is out of range *)
val change_name_env: ('a, 'b) sign -> int -> identifier -> ('a, 'b) sign

type ('b,'a) search_result =
  | GLOBNAME of identifier  * 'b
  | RELNAME of int * 'a

val lookup_id : identifier -> ('b,'a) sign -> ('b,'a) search_result


type 'b assumptions = (typed_type,'b) sign
type context = (typed_type,typed_type) sign
type var_context = typed_type signature

val unitize_env : 'a assumptions -> unit assumptions







