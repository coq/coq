(****************************************************************************)
(*                                                                          *)
(*                          The Coq Proof Assistant                         *)
(*                                                                          *)
(*                                 Projet Coq                               *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(****************************************************************************)

(* $Id$ *)

open Pp
open Environ
open Term
open Nametab
open Pcoq
open Rawterm
open Extend

val pr_global : global_reference -> std_ppcmds
val gentermpr : Coqast.t -> std_ppcmds
val gentermpr_core : bool -> env -> constr -> std_ppcmds

val pr_qualid : qualid -> std_ppcmds
val pr_red_expr :
  ('a -> std_ppcmds) * ('b -> std_ppcmds) ->
    ('a,'b) red_expr_gen -> std_ppcmds

val pr_pattern : Tacexpr.pattern_ast -> std_ppcmds
val pr_constr : Genarg.constr_ast -> std_ppcmds
val pr_may_eval : ('a -> std_ppcmds) -> 'a may_eval -> std_ppcmds
