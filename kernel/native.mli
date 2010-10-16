type caml_prim =
  (* Int31 operations *)
  | Int31print
  (* Array operations *)
  | ArrayMake
  | ArrayGet
  | ArrayGetdefault
  | ArraySet
  | ArrayCopy
  | ArrayReroot
  | ArrayLength

type iterator =
  | Int31foldi
  | Int31foldi_down
 
type prim_op = 
  | Int31head0
  | Int31tail0

  | Int31add
  | Int31sub
  | Int31mul
  | Int31div
  | Int31mod
  | Int31lsr
  | Int31lsl
  | Int31land
  | Int31lor
  | Int31lxor

  | Int31addc
  | Int31subc
  | Int31addCarryC
  | Int31subCarryC

  | Int31mulc
  | Int31diveucl
  | Int31div21

  | Int31addMulDiv

  | Int31eq
  | Int31lt
  | Int31le

  | Int31compare
  | Int31eqb_correct

type op =
  | Oprim of prim_op
  | Ocaml_prim of caml_prim
  | Oiterator of iterator


val prim_to_string : prim_op -> string
val caml_prim_to_string : caml_prim -> string
val to_string : op -> string

type arg_kind =
  | Kparam (* not needed for the elavuation of the primitive*)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf *)

type args_red = arg_kind list

val op_kind : op -> args_red

val caml_prim_arity : caml_prim -> int * int
val arity : op -> int * int (* number of parameters, number of arguments *)

module type UINT31 =
    sig 
      type t

      (* conversion to int *)
      val to_int : t -> int
      val of_int : int -> t

     (* convertion to a string *)
      val to_string : t -> string
      val of_string : string -> t

      (* logical operations *)
      val l_sl    : t -> t -> t
      val l_sr    : t -> t -> t
      val l_and   : t -> t -> t
      val l_xor   : t -> t -> t
      val l_or    : t -> t -> t

      (* Arithmetic operations *) 
      val add     : t -> t -> t
      val sub     : t -> t -> t
      val mul     : t -> t -> t
      val div     : t -> t -> t
      val rem     : t -> t -> t
      
      (* Specific arithmetic operations *)
      val mulc    : t -> t -> t * t
      val div21   : t -> t -> t -> t * t
      
      (* comparison *)
      val lt      : t -> t -> bool
      val eq      : t -> t -> bool
      val le      : t -> t -> bool
      val compare : t -> t -> int

      (* head and tail *)
      val head0   : t -> t
      val tail0   : t -> t

   end

module Uint31 : UINT31

val max_array_length32 : int

module type PARRAY = 
  sig 
    type 'a t
    val length  : 'a t -> Uint31.t
    val get     : 'a t -> Uint31.t -> 'a
    val set     : 'a t -> Uint31.t -> 'a -> 'a t
    val default : 'a t -> 'a 
    val make    : Uint31.t -> 'a -> 'a t
    val init    : Uint31.t -> (int -> 'a) -> 'a -> 'a t
    val copy    : 'a t -> 'a t
    val reroot  : 'a t -> 'a t

    val map : ('a -> 'b) -> 'a t -> 'b t

    (* /!\ Unsafe function *)
    val of_array : 'a array -> 'a t

  end

(* Implementation using persistant array *)
module Parray : PARRAY

(* Implementation using array. Warning, the set operation copies array *)
module Narray : PARRAY with type 'a t = 'a array


(** Special Entries for Register **)

type prim_ind =
  | PIT_bool
  | PIT_carry
  | PIT_pair
  | PIT_cmp
  | PIT_eq

type prim_type =
  | PT_int31
  | PT_array

type retro_action =
  | Retro_ind of prim_ind
  | Retro_type of prim_type
  | Retro_inline 

type op_or_type = 
  | OT_op of op
  | OT_type of prim_type


val op_or_type_to_string : op_or_type -> string
val prim_ind_to_string : prim_ind -> string
