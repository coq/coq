(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Pp
open Pcoq

(** The Coq toplevel loop. *)

(** A buffer for the character read from a channel. We store the command
 * entered to be able to report errors without pretty-printing. *)

type input_buffer = {
  mutable prompt : unit -> string;
  mutable str : string; (** buffer of already read characters *)
  mutable len : int;    (** number of chars in the buffer *)
  mutable bols : int list; (** offsets in str of begining of lines *)
  mutable tokens : Pcoq.Gram.parsable; (** stream of tokens *)
  mutable start : int } (** stream count of the first char of the buffer *)

(** The input buffer of stdin. *)

val top_buffer : input_buffer
val set_prompt : (unit -> string) -> unit

(** Toplevel error explanation, dealing with locations, Drop, Ctrl-D
  May raise only the following exceptions: [Drop] and [End_of_input],
  meaning we get out of the Coq loop. *)

val print_toplevel_error : exn -> std_ppcmds

(** Parse and execute a vernac command. *)

val do_vernac : unit -> unit

(** Main entry point of Coq: read and execute vernac commands. *)

val loop : unit -> unit
