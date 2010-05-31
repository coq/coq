(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(** The Coq main module. The following function [start] will parse the
   command line, print the banner, initialize the load path, load the input
   state, load the files given on the command line, load the ressource file,
   produce the output state if any, and finally will launch [Toplevel.loop]. *)

val start : unit -> unit

(** [init_ide] is to be used by the Coq IDE.
   It does everything [start] does, except launching the toplevel loop.
   It returns the list of Coq files given on the command line. *)

val init_ide : System.physical_path list -> string list

