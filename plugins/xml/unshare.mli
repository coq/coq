(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

exception CanNotUnshare;;

(* [unshare t] gives back a copy of t where all sharing has been removed   *)
(* Physical equality becomes meaningful on unshared terms. Hashtables that *)
(* use physical equality can now be used to associate information to evey  *)
(* node of the term.                                                       *)
val unshare: ?already_unshared:('a -> bool) -> 'a -> 'a
