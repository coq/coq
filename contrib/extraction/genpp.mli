
(*i $Id$ i*)

(*s This module defines the generic part of the code production, as a
    functor [Make] taking extraction parameters as argument (of type
    [ExtractionParams]), including a renaming functor (of type
    [Extraction.Renaming]) and returning a module to output the
    code. *)

open Pp
open Names
open Miniml
open Vernacinterp

(*s Some utility functions, used in instance modules ([Caml], [Ocaml] and 
    [Haskell]). *)

val open_par : bool -> std_ppcmds
val close_par : bool -> std_ppcmds

val uncurry_list : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
val uncurry_list2 : ('a -> std_ppcmds) -> 'a list -> std_ppcmds

(*s Extraction parameters parsed on the command line. *)

type extraction_params = {
  needed : identifier list;		(*r constants to keep *)
  expand : identifier list;		(*r constants to expand *)
  expansion : bool;			(*r do we expand *)
  exact : bool				(*r without recursivity *)
}

val parse_param : vernac_arg list -> extraction_params

(*s The whole bunch of extraction parameters has the following signature. *)

module type ExtractionParams = 
  sig
    (* optimisation function *)
    val opt : extraction_params -> ml_decl list -> ml_decl list
    (* file suffix *)
    val suffixe : string
    (* co-inductive types are (not) allowed *)
    val cofix : bool
    (* pretty-print function *)
    val pp_of_env : ml_decl list -> std_ppcmds
    (* the renaming functions *)
    module Renaming : Extraction.Renaming
  end

(*s The functor itself. *)

module Make : functor (M : ExtractionParams) ->
  sig
    module Translation : Extraction.Translation
    val pp_recursive : extraction_params -> std_ppcmds
    val write_extraction_file : string -> extraction_params -> unit
    val write_extraction_module : identifier -> unit
  end
