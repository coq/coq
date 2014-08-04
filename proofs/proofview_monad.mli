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


(** {6 Exceptions} *)


(** To help distinguish between exceptions raised by the IO monad from
    the one used natively by Coq, the former are wrapped in
    [Exception].  It is only used internally so that [catch] blocks of
    the IO monad would only catch exceptions raised by the [raise]
    function of the IO monad, and not for instance, by system
    interrupts. Also used in [Proofview] to avoid capturing exception
    from the IO monad ([Proofview] catches errors in its compatibility
    layer, and when lifting goal-level expressions). *)
exception Exception of exn
(** This exception is used to signal abortion in [timeout] functions. *)
exception Timeout
(** This exception is used by the tactics to signal failure by lack of
    successes, rather than some other exceptions (like system
    interrupts). *)
exception TacticFailure of exn


module NonLogical : sig

  type +'a t
  type 'a ref

  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val ignore : 'a t -> unit t
  val seq : unit t -> 'a t -> 'a t

  val ref : 'a -> 'a ref t
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
  val once : 'a t -> 'a t
  val break : (exn -> bool) -> 'a t -> 'a t

  val lift : 'a NonLogical.t -> 'a t

  val run : 'a t -> logicalEnvironment -> logicalState -> (('a*logicalState)*logicalMessageType) NonLogical.t
end
