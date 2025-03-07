(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

(** Recursive scan of a directory *)
type 'a t

(** [scan ~prefix dir] scan for coq modules in dir [prefix] will
   inject a dir *)
val scan : prefix:string list -> string -> Coq_module.t t

(** [iter ~f dir_info] iterate contents, [prefix] denotes the sub-tree
   we are in *)
val iter : f:(prefix:string list -> 'a list -> unit) -> 'a t -> unit

(** [fold ~f ~init dir_info] fold over each folder's contents *)
val fold : f:(prefix:string list -> 'b -> 'a list -> 'b) -> init:'b -> 'a t -> 'b

(** Flatten the list of objects of a recursive scan *)
val coq_modules : 'a t -> 'a list

val pp : Format.formatter -> Coq_module.t t -> unit

(* To remove *)
val map : f:(prefix:string list -> 'a -> 'b) -> 'a t -> 'b t
