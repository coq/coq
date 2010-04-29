(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*** This module implements an "untyped store", in this particular case we
        see it as an extensible record whose fields are left unspecified. ***)

type t

module Field : sig
  type 'a field = {
    set : 'a -> t -> t ;
    get : t -> 'a option ;
    remove : t -> t 
  }
  type 'a t = 'a field
end

val empty : t

val field : unit -> 'a Field.field
