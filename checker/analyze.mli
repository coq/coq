type data =
| Int of int
| Ptr of int
| Atm of int (* tag *)
| Fun of int (* address *)

type obj =
| Struct of int * data array (* tag × data *)
| String of string

val parse_channel : in_channel -> (data * obj array)
val parse_string : string -> (data * obj array)

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
  val parse : input -> (data * obj array)
  (** Return the entry point and the reification of the memory out of a
      marshalled structure. *)
end

module Make (M : Input) : S with type input = M.t
(** Functorized version of the previous code. *)
