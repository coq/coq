(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

type 'a pp = Format.formatter -> 'a -> unit

module Rule : sig
  type t =
    { targets : string list
    ; deps : string list
    ; action : string
    ; alias : string option
    }

  val pp : t pp
end

module Install : sig
  type t =
    { section : string
    ; package : string
    ; files : (string * string) list
    (* (source as target) *)
    }

  val pp : t pp
end

module Subdir : sig

  type 'a t = { subdir : string; payload : 'a }

  val pp : 'a pp -> 'a t pp
end
