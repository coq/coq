(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** Variant implementation. See {!Bitv} for documentation. *)

type t

val create : int -> bool -> t

val init : int -> (int -> bool) -> t

val append : t -> t -> t

val set : t -> int -> bool -> unit

val get : t -> int -> bool

val length : t -> int

val equal : t -> t -> bool

val max_length : int
(** @deprecated Use [exceed_max_length] instead. *)

val exceeds_max_length : int -> bool

val copy : t -> t

val fill : t -> int -> int -> bool -> unit

val iter : (bool -> unit) -> t -> unit
val map : (bool -> bool) -> t -> t

val iteri : (int -> bool -> unit) -> t -> unit
val mapi : (int -> bool -> bool) -> t -> t

val fold_left : ('a -> bool -> 'a) -> 'a -> t -> 'a
val fold_right : (bool -> 'a -> 'a) -> t -> 'a -> 'a
val foldi_left : ('a -> int -> bool -> 'a) -> 'a -> t -> 'a
val foldi_right : (int -> bool -> 'a -> 'a) -> t -> 'a -> 'a

val pop: t -> int

val iteri_true : (int -> unit) -> t -> unit

val bw_and : t -> t -> t
val bw_or  : t -> t -> t
val bw_xor : t -> t -> t
val bw_not : t -> t

val to_list : t -> int list
val of_list : int list -> t
val of_list_with_length : int list -> int -> t

val of_list_mapi : 'a list -> (int -> 'a -> bool) -> t

(** {2 Only if you know what you are doing...} *)

val unsafe_set : t -> int -> bool -> unit
val unsafe_get : t -> int -> bool

val all_true : t -> bool

val compose : t -> t -> t
