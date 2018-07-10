(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)

open Genarg
open Ssrmatching

(** CS cpattern: (f _), (X in t), (t in X in t), (t as X in t) *)
val cpattern         : cpattern Pcoq.Entry.t
val wit_cpattern     : cpattern uniform_genarg_type

(** OS cpattern: f _, (X in t), (t in X in t), (t as X in t) *)
val lcpattern         : cpattern Pcoq.Entry.t
val wit_lcpattern     : cpattern uniform_genarg_type

(** OS rpattern: f _, in t, X in t, in X in t, t in X in t, t as X in t *)
val rpattern         : rpattern Pcoq.Entry.t
val wit_rpattern     : rpattern uniform_genarg_type
