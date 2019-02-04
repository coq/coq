(** Representation of data allocated on the OCaml heap. *)
type data =
| Int of int
| Ptr of int
| Atm of int (* tag *)
| Fun of int (* address *)

type obj =
| Struct of int * data array (* tag × data *)
| Int63 of Uint63.t (* Primitive integer *)
| String of string

module LargeArray :
sig
  type 'a t
  val empty : 'a t
  val length : 'a t -> int
  val make : int -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val set : 'a t -> int -> 'a -> unit
end
(** A data structure similar to arrays but allowing to overcome the 2^22 length
    limitation on 32-bit architecture. *)

val parse_channel : in_channel -> (data * obj LargeArray.t)
val parse_string : string -> (data * obj LargeArray.t)

(** {6 Functorized version} *)

module type Input =
sig
  type t
  val input_byte : t -> int
  (** Input a single byte *)

  val input_binary_int : t -> int
  (** Input a big-endian 31-bits signed integer *)
end
(** Type of inputs *)

module type S =
sig
  type input
  val parse : input -> (data * obj LargeArray.t)
  (** Return the entry point and the reification of the memory out of a
      marshalled structure. *)
end

module Make (M : Input) : S with type input = M.t
(** Functorized version of the previous code. *)

val instantiate : data * obj LargeArray.t -> Obj.t
(** Create the OCaml object out of the reified representation. *)
