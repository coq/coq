(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type ('constr, 'types, 'univs) t =
  | Int of Uint63.t
  | Float of Float64.t
  | Array of 'univs * 'constr array * 'constr * 'types

val fold :
  ('a -> 'constr -> 'a) ->
  ('a -> 'types -> 'a) ->
  'a ->
  ('constr, 'types, 'univs) t ->
  'a

val iter :
  ('constr -> unit) ->
  ('types -> unit) ->
  ('constr, 'types, 'univs) t ->
  unit

val map :
  ('constr -> 'constr) ->
  ('types -> 'types) ->
  ('univs -> 'univs) ->
  ('constr, 'types, 'univs) t ->
  ('constr, 'types, 'univs) t

val map_heterogenous :
  ('constr1 -> 'constr2) ->
  ('types1 -> 'types2) ->
  ('univs1 -> 'univs2) ->
  ('constr1, 'types1, 'univs1) t ->
  ('constr2, 'types2, 'univs2) t

val fold_map :
  ('a -> 'constr -> 'a * 'constr) ->
  'a ->
  ('constr, 'constr, 'univs) t ->
  'a * ('constr, 'constr, 'univs) t

val map_fun1 :
  ('a -> 'constr -> 'constr) ->
  'a ->
  ('constr, 'constr, 'univs) t ->
  ('constr, 'constr, 'univs) t

val equal :
  ('univs -> 'univs -> bool) ->
  ('constr -> 'constr -> bool) ->
  ('constr, 'constr, 'univs) t ->
  ('constr, 'constr, 'univs) t ->
  bool

val compare :
  ('constr -> 'constr -> int) ->
  ('constr, 'constr, 'univs) t ->
  ('constr, 'constr, 'univs) t ->
  int

val hash :
  ('univs -> int) ->
  ('constr array -> int) ->
  ('constr -> int) ->
  ('constr, 'constr, 'univs) t ->
  int

val hash_term :
  ('univs -> 'univs * int) ->
  ('constr array -> 'constr array * int) ->
  ('constr -> 'constr * int) ->
  ('constr, 'constr, 'univs) t ->
  ('constr, 'constr, 'univs) t * int

val exists_constr :
  ('constr -> bool) ->
  ('constr, 'types, 'univs) t ->
  bool

val fold_univs :
  ('a -> 'univs -> 'a) ->
  'a ->
  ('constr, 'types, 'univs) t ->
  'a

val matching :
  fail:(unit -> 'res) ->
  ('res -> 'constr1 -> 'constr2 -> 'res) ->
  ('constr1, 'constr1, _) t ->
  ('constr2, 'constr2, _) t ->
  'res ->
  'res

val debug_print :
  ('univs -> Pp.t) ->
  ('constr -> Pp.t) ->
  ('constr, 'constr, 'univs) t ->
  Pp.t
