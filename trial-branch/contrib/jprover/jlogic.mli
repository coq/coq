(* The interface to manipulate [jterms], which is
   extracted and modified from Meta-Prl. *)

type rule =
   Ax | Andr | Andl | Orr | Orr1 | Orr2 | Orl | Impr | Impl | Negr | Negl
 | Allr | Alll| Exr | Exl | Fail | Falsel | Truer

module type JLogicSig =
  sig
    val is_all_term : Jterm.term -> bool
    val dest_all : Jterm.term -> string * Jterm.term * Jterm.term
    val is_exists_term : Jterm.term -> bool
    val dest_exists : Jterm.term -> string * Jterm.term * Jterm.term
    val is_and_term : Jterm.term -> bool
    val dest_and : Jterm.term -> Jterm.term * Jterm.term
    val is_or_term : Jterm.term -> bool
    val dest_or : Jterm.term -> Jterm.term * Jterm.term
    val is_implies_term : Jterm.term -> bool
    val dest_implies : Jterm.term -> Jterm.term * Jterm.term
    val is_not_term : Jterm.term -> bool
    val dest_not : Jterm.term -> Jterm.term
    type inf_step = rule * (string * Jterm.term) * (string * Jterm.term)
    type inference = inf_step list
    val empty_inf : inference
    val append_inf :
      inference -> (string * Jterm.term) -> (string * Jterm.term) -> rule -> inference
    val print_inf : inference -> unit
  end

module JLogic : JLogicSig

val show_loading : string -> unit

type my_Debug = {
  mutable debug_name : string;
  mutable debug_description : string;
  debug_value : bool;
} 
val create_debug : 'a -> bool ref
val ruletable : rule -> string
