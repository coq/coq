(* This is an interface for the code extracted from bootstrap/Monad.v.
   The relevant comments are overthere. *)

type ('a, 'b) list_view =
| Nil of exn
| Cons of 'a * 'b

type proofview = { solution : Evd.evar_map; comb : Goal.goal list }

type logicalState = proofview

type logicalEnvironment = Environ.env

(** status (safe/unsafe) * ( shelved goals * given up ) *)
type logicalMessageType = bool * ( Goal.goal list * Goal.goal list )



module NonLogical : sig

  type +'a t
  type 'a ref

  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val ignore : 'a t -> unit t
  val seq : unit t -> 'a t -> 'a t

  val new_ref : 'a -> 'a ref t
  val set : 'a ref -> 'a -> unit t
  val get : 'a ref -> 'a t

  val read_line : string t
  val print_char : char -> unit t
  val print : Pp.std_ppcmds -> unit t

  val raise : exn -> 'a t
  val catch : 'a t -> (exn -> 'a t) -> 'a t
  val timeout : int -> 'a t -> 'a t


  (* [run] performs effects. *)
  val run : 'a t -> 'a

end


module Logical : sig

  type +'a t

  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val ignore : 'a t -> unit t
  val seq : unit t -> 'a t -> 'a t

  val set : logicalState -> unit t
  val get : logicalState t
  val modify : (logicalState -> logicalState) -> unit t
  val put : logicalMessageType -> unit t
  val current : logicalEnvironment t

  val zero : exn -> 'a t
  val plus : 'a t -> (exn -> 'a t) -> 'a t
  val split : 'a t -> (('a,(exn->'a t)) list_view) t

  val lift : 'a NonLogical.t -> 'a t

  val run : 'a t -> logicalEnvironment -> logicalState -> (('a*logicalState)*logicalMessageType) NonLogical.t
end
