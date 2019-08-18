(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Dynamic toplevel values *)

module ValT = Dyn.Make ()

module ValTMap = ValT.Map

module Val =
struct

  type 'a typ = 'a ValT.tag

  type _ tag =
  | Base : 'a typ -> 'a tag
  | List : 'a tag -> 'a list tag
  | Opt : 'a tag -> 'a option tag
  | Pair : 'a tag * 'b tag -> ('a * 'b) tag

  type t = Dyn : 'a typ * 'a -> t

  let eq = ValT.eq
  let repr = ValT.repr
  let create = ValT.create

  let pr : type a. a typ -> Pp.t = fun t -> Pp.str (repr t)

  let typ_list = ValT.create "list"
  let typ_opt = ValT.create "option"
  let typ_pair = ValT.create "pair"

  let rec inject : type a. a tag -> a -> t = fun tag x -> match tag with
  | Base t -> Dyn (t, x)
  | List tag -> Dyn (typ_list, List.map (fun x -> inject tag x) x)
  | Opt tag -> Dyn (typ_opt, Option.map (fun x -> inject tag x) x)
  | Pair (tag1, tag2) ->
    Dyn (typ_pair, (inject tag1 (fst x), inject tag2 (snd x)))

end
