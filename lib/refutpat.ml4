(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo q_MLast.cmo" i*)

open Pcaml

(** * Non-irrefutable patterns

    This small camlp4 extension creates a "let*" variant of the "let"
    syntax that allow the use of a non-exhaustive pattern. The typical
    usage is:
        
      let* x::l = foo in ...

    when foo is already known to be non-empty. This way, no warnings by ocamlc.
    A Failure is raised if the pattern doesn't match the expression.
*)


EXTEND
 expr:
   [[ "let"; "*"; p = patt; "="; e1 = expr; "in"; e2 = expr ->
       <:expr< match $e1$ with
	        [ $p$ -> $e2$
                | _ -> failwith "Refutable pattern failed"
                ] >> ]];
END
