
(* $Id$ *)

open Inductive
open Environ
open Reduction

let mind_check_arities env mie =
  let check_arity id c =
    if not (is_arity env c) then raise (InductiveError (NotAnArity id))
  in
  List.iter (fun (id,ar,_,_) -> check_arity id ar) mie.mind_entry_inds

