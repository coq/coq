(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This is mostly a translation of OCaml stdlib/array.ml *)

(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Int.
Require Ltac2.Control.
Require Ltac2.Bool.
Require Ltac2.Message.

(* Question: what is returned in case of an out of range value?
   Answer:   Ltac2 throws a panic *)

Ltac2 @external empty : unit -> 'a array := "ltac2" "array_empty".
Ltac2 @external make : int -> 'a -> 'a array := "ltac2" "array_make".
Ltac2 @external length : 'a array -> int := "ltac2" "array_length".
Ltac2 @external get : 'a array -> int -> 'a := "ltac2" "array_get".
Ltac2 @external set : 'a array -> int -> 'a -> unit := "ltac2" "array_set".
Ltac2 @external lowlevel_blit : 'a array -> int -> 'a array -> int -> int -> unit := "ltac2" "array_blit".
Ltac2 @external lowlevel_fill : 'a array -> int -> int -> 'a -> unit := "ltac2" "array_fill".
Ltac2 @external concat : ('a array) list -> 'a array := "ltac2" "array_concat".

(* Low level array operations *)

Ltac2 lowlevel_sub (arr : 'a array) (start : int) (len : int) :=
  let l := length arr in
  match Int.equal l 0 with
  | true => empty ()
  | false =>
      let newarr:=make len (get arr 0) in
      lowlevel_blit arr start newarr 0 len;
      newarr
  end.

(* Array functions as defined in the OCaml library *)

Ltac2 init (l : int) (f : int->'a) :=
  let rec init_aux (dst : 'a array) (pos : int) (len : int) (f : int->'a) :=
    match Int.equal len 0 with
    | true => ()
    | false =>
        set dst pos (f pos);
        init_aux dst (Int.add pos 1) (Int.sub len 1) f
    end
  in
  match Int.le l 0 with
  | true => empty ()
  | false =>
      let arr:=make l (f 0) in
      init_aux arr 1 (Int.sub l 1) f;
      arr
  end.

Ltac2 make_matrix (sx : int) (sy : int) (v : 'a) :=
  let init1 i := v in
  let initr i := init sy init1 in
  init sx initr.

Ltac2 copy a := lowlevel_sub a 0 (length a).

Ltac2 append (a1 : 'a array) (a2 : 'a array) :=
  match Int.equal (length a1) 0 with
  | true => copy a2
  | false => match Int.equal (length a2) 0 with
             | true => copy a1
             | false =>
                 let newarr:=make (Int.add (length a1) (length a2)) (get a1 0) in
                 lowlevel_blit a1 0 newarr 0 (length a1);
                 lowlevel_blit a2 0 newarr (length a1) (length a2);
                 newarr
             end
  end.

Ltac2 sub (a : 'a array) (ofs : int) (len : int) :=
  Control.assert_valid_argument "Array.sub ofs<0" (Int.ge ofs 0);
  Control.assert_valid_argument "Array.sub len<0" (Int.ge len 0);
  Control.assert_bounds "Array.sub" (Int.le ofs (Int.sub (length a) len));
  lowlevel_sub a ofs len.

Ltac2 fill (a : 'a array) (ofs : int) (len : int) (v : 'a) :=
  Control.assert_valid_argument "Array.fill ofs<0" (Int.ge ofs 0);
  Control.assert_valid_argument "Array.fill len<0" (Int.ge len 0);
  Control.assert_bounds "Array.fill" (Int.le ofs (Int.sub (length a) len));
  lowlevel_fill a ofs len v.

Ltac2 blit (a1 : 'a array) (ofs1 : int) (a2 : 'a array) (ofs2 : int) (len : int) :=
  Control.assert_valid_argument "Array.blit ofs1<0" (Int.ge ofs1 0);
  Control.assert_valid_argument "Array.blit ofs2<0" (Int.ge ofs2 0);
  Control.assert_valid_argument "Array.blit len<0" (Int.ge len 0);
  Control.assert_bounds "Array.blit ofs1+len>len a1" (Int.le ofs1 (Int.sub (length a1) len));
  Control.assert_bounds "Array.blit ofs2+len>len a2" (Int.le ofs2 (Int.sub (length a2) len));
  lowlevel_blit a1 ofs1 a2 ofs2 len.

Ltac2 rec iter_aux (f : 'a -> unit) (a : 'a array) (pos : int) (len : int) :=
  match Int.equal len 0 with
  | true => ()
  | false => f (get a pos); iter_aux f a (Int.add pos 1) (Int.sub len 1)
  end.

Ltac2 iter (f : 'a -> unit) (a : 'a array) := iter_aux f a 0 (length a).

Ltac2 rec iter2_aux (f : 'a -> 'b -> unit) (a : 'a array) (b : 'b array) (pos : int) (len : int) :=
  match Int.equal len 0 with
  | true => ()
  | false => f (get a pos) (get b pos); iter2_aux f a b (Int.add pos 1) (Int.sub len 1)
  end.

Ltac2 rec iter2 (f : 'a -> 'b -> unit) (a : 'a array) (b : 'b array) :=
  Control.assert_valid_argument "Array.iter2" (Int.equal (length a) (length b));
  iter2_aux f a b 0 (length a).

Ltac2 map (f : 'a -> 'b) (a : 'a array) :=
  init (length a) (fun i => f (get a i)).

Ltac2 map2 (f : 'a -> 'b -> 'c) (a : 'a array) (b : 'b array) :=
  Control.assert_valid_argument "Array.map2" (Int.equal (length a) (length b));
  init (length a) (fun i => f (get a i) (get b i)).

Ltac2 rec iteri_aux (f : int -> 'a -> unit) (a : 'a array) (pos : int) (len : int) :=
  match Int.equal len 0 with
  | true => ()
  | false => f pos (get a pos); iteri_aux f a (Int.add pos 1) (Int.sub len 1)
  end.

Ltac2 iteri (f : int -> 'a -> unit) (a : 'a array) := iteri_aux f a 0 (length a).

Ltac2 mapi (f : int -> 'a -> 'b) (a : 'a array) :=
  init (length a) (fun i => f i (get a i)).

Ltac2 rec to_list_aux (a : 'a array) (pos : int) (len : int) :=
  match Int.equal len 0 with
  | true => []
  | false => get a pos :: to_list_aux a (Int.add pos 1) (Int.sub len 1)
  end.

Ltac2 to_list (a : 'a array) := to_list_aux a 0 (length a).

Ltac2 rec of_list_aux (ls : 'a list) (dst : 'a array) (pos : int) :=
  match ls with
  | [] => ()
  | hd::tl =>
      set dst pos hd;
      of_list_aux tl dst (Int.add pos 1)
  end.

Ltac2 of_list (ls : 'a list) :=
  (* Don't use List.length here because the List module might depend on Array some day *)
  let rec list_length (ls : 'a list) :=
    match ls with
    | [] => 0
    | _ :: tl => Int.add 1 (list_length tl)
    end in
  match ls with
  | [] => empty ()
  | hd::tl =>
      let anew := make (list_length ls) hd in
      of_list_aux ls anew 0;
      anew
  end.

Ltac2 rec fold_left_aux (f : 'a -> 'b -> 'a) (x : 'a) (a : 'b array) (pos : int) (len : int) :=
  match Int.equal len 0 with
  | true => x
  | false => fold_left_aux f (f x (get a pos)) a (Int.add pos 1) (Int.sub len 1)
  end.

Ltac2 fold_left (f : 'a -> 'b -> 'a) (x : 'a) (a : 'b array) := fold_left_aux f x a 0 (length a).

Ltac2 rec fold_right_aux (f : 'a -> 'b -> 'a) (x : 'a) (a : 'b array) (pos : int) (len : int) :=
  (* Note: one could compare pos<0.
     We keep an extra len parameter so that the function can be used for any sub array *)
  match Int.equal len 0 with
  | true => x
  | false => fold_right_aux f (f x (get a pos)) a (Int.sub pos 1) (Int.sub len 1)
  end.

Ltac2 fold_right (f : 'a -> 'b -> 'a) (x : 'a) (a : 'b array) := fold_right_aux f x a (Int.sub (length a) 1) (length a).

Ltac2 rec exist_aux (p : 'a -> bool) (a : 'a array) (pos : int) (len : int) :=
  match Int.equal len 0 with
  | true => false
  | false => match p (get a pos) with
             | true => true
             | false => exist_aux p a (Int.add pos 1) (Int.sub len 1)
             end
  end.

(* Note: named exist (as in Coq library) rather than exists cause exists is a notation *)
Ltac2 exist (p : 'a -> bool) (a : 'a array) := exist_aux p a 0 (length a).

Ltac2 rec for_all_aux (p : 'a -> bool) (a : 'a array) (pos : int) (len : int) :=
  match Int.equal len 0 with
  | true => true
  | false => match p (get a pos) with
             | true => for_all_aux p a (Int.add pos 1) (Int.sub len 1)
             | false => false
             end
  end.

Ltac2 for_all (p : 'a -> bool) (a : 'a array) := for_all_aux p a 0 (length a).

(* Note: we don't have (yet) a generic equality function in Ltac2 *)
Ltac2 mem (eq : 'a -> 'a -> bool) (x : 'a) (a : 'a array) :=
  exist (eq x) a.
