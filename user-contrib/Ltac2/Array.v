(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

(** This module implements fixed sized, mutable arrays.

    Unless specified otherwise, all functions defined below throw
    an exception in case of out of bounds indices, and arrays are indexed
    starting at [0]. *)

(** The empty array. *)
Ltac2 @external empty : 'a array := "rocq-runtime.plugins.ltac2" "array_empty".

(** [make n x] creates an array of length [n], with all elements set to [x]. *)
Ltac2 @external make : int -> 'a -> 'a array := "rocq-runtime.plugins.ltac2" "array_make".

(** Return the length of an array. *)
Ltac2 @external length : 'a array -> int := "rocq-runtime.plugins.ltac2" "array_length".

(** [get arr i] returns the [i]-th element of [arr]. *)
Ltac2 @external get : 'a array -> int -> 'a := "rocq-runtime.plugins.ltac2" "array_get".

(** [set arr i x] replaces [arr[i]] with [x]. This modifies [arr] in place. *)
Ltac2 @external set : 'a array -> int -> 'a -> unit := "rocq-runtime.plugins.ltac2" "array_set".

(** [lowlevel_blit from fofs to tofs len] copies [from[fofs...fofs+len-1]] to [to[tofs...tofs+len-1]] (bounds included).
    This modifies [to] in place.

    Consider using [blit] for nicer error messages. *)
Ltac2 @external lowlevel_blit : 'a array -> int -> 'a array -> int -> int -> unit := "rocq-runtime.plugins.ltac2" "array_blit".

(** [lowlevel_fill arr ofs len x] replaces [arr[ofs]], [arr[ofs+1]], ..., [arr[ofs+len-1]] with [x].
    This modifes [arr] in place.

    Consider using [fill] for nicer error messages. *)
Ltac2 @external lowlevel_fill : 'a array -> int -> int -> 'a -> unit := "rocq-runtime.plugins.ltac2" "array_fill".

(** [concat [a1 ; a2 ; ... ; aN]] returns the array [a1 ++ a2 ++ ... ++ an]. *)
Ltac2 @external concat : ('a array) list -> 'a array := "rocq-runtime.plugins.ltac2" "array_concat".

(** [lowlevel_sub arr ofs len] returns the subarray [arr[ofs...ofs+len-1]].
    The result is allocated as a new array, i.e. is not aliased with [arr].

    Consider using [sub] for nicer error messages. *)
Ltac2 lowlevel_sub (arr : 'a array) (start : int) (len : int) : 'a array :=
  let l := length arr in
  match Int.equal l 0 with
  | true => empty
  | false =>
      let newarr:=make len (get arr 0) in
      lowlevel_blit arr start newarr 0 len;
      newarr
  end.

(** [init n f] creates the array [| f 0 ; f 1 ; ... ; f (n-1) |]. *)
Ltac2 init (l : int) (f : int -> 'a) : 'a array :=
  let rec init_aux (dst : 'a array) (pos : int) (len : int) (f : int->'a) :=
    match Int.equal len 0 with
    | true => ()
    | false =>
        set dst pos (f pos);
        init_aux dst (Int.add pos 1) (Int.sub len 1) f
    end
  in
  match Int.le l 0 with
  | true => empty
  | false =>
      let arr:=make l (f 0) in
      init_aux arr 1 (Int.sub l 1) f;
      arr
  end.

(** [make_matrix sx sy v] creates an array of size [sx]
    which contains array of size [sy], filled with [v]. *)
Ltac2 make_matrix (sx : int) (sy : int) (v : 'a) : 'a array array :=
  let initr _ := make sy v in
  init sx initr.

(** Copy an array. The copied array can be modified without
    changing the original array (and vice versa). *)
Ltac2 copy (a : 'a array) : 'a array :=
  lowlevel_sub a 0 (length a).

(** [append a1 a2] appends [a1] and [a2].
    This allocates a new array, even if [a1] or [a2] is empty. *)
Ltac2 append (a1 : 'a array) (a2 : 'a array) : 'a array :=
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

(** [sub arr ofs len] returns the subarray [arr[ofs...ofs+len-1]].
    The result is allocated as a new array, i.e. is not aliased with [arr]. *)
Ltac2 sub (a : 'a array) (ofs : int) (len : int) : 'a array :=
  Control.assert_valid_argument "Array.sub ofs<0" (Int.ge ofs 0);
  Control.assert_valid_argument "Array.sub len<0" (Int.ge len 0);
  Control.assert_bounds "Array.sub" (Int.le ofs (Int.sub (length a) len));
  lowlevel_sub a ofs len.

(** [fill arr ofs len x] replaces [arr[ofs]], [arr[ofs+1]], ..., [arr[ofs+len-1]] with [x].
    This modifes [arr] in place. *)
Ltac2 fill (a : 'a array) (ofs : int) (len : int) (v : 'a) : unit :=
  Control.assert_valid_argument "Array.fill ofs<0" (Int.ge ofs 0);
  Control.assert_valid_argument "Array.fill len<0" (Int.ge len 0);
  Control.assert_bounds "Array.fill" (Int.le ofs (Int.sub (length a) len));
  lowlevel_fill a ofs len v.

(** [blit from fofs to tofs len] copies [from[fofs...fofs+len-1]] to [to[tofs...tofs+len-1]] (bounds included).
    This modifies [to] in place. *)
Ltac2 blit (a1 : 'a array) (ofs1 : int) (a2 : 'a array) (ofs2 : int) (len : int) : unit :=
  Control.assert_valid_argument "Array.blit ofs1<0" (Int.ge ofs1 0);
  Control.assert_valid_argument "Array.blit ofs2<0" (Int.ge ofs2 0);
  Control.assert_valid_argument "Array.blit len<0" (Int.ge len 0);
  Control.assert_bounds "Array.blit ofs1+len>len a1" (Int.le ofs1 (Int.sub (length a1) len));
  Control.assert_bounds "Array.blit ofs2+len>len a2" (Int.le ofs2 (Int.sub (length a2) len));
  lowlevel_blit a1 ofs1 a2 ofs2 len.

(** Helper function for [iter]. *)
Ltac2 rec iter_aux (f : 'a -> unit) (a : 'a array) (pos : int) (len : int) : unit :=
  match Int.equal len 0 with
  | true => ()
  | false => f (get a pos); iter_aux f a (Int.add pos 1) (Int.sub len 1)
  end.

(** [iter f arr] calls [f] on every element of [arr], from first to last. *)
Ltac2 iter (f : 'a -> unit) (a : 'a array) : unit :=
  iter_aux f a 0 (length a).

(** Helper function for [iter2]. *)
Ltac2 rec iter2_aux (f : 'a -> 'b -> unit) (a : 'a array) (b : 'b array) (pos : int) (len : int) : unit :=
  match Int.equal len 0 with
  | true => ()
  | false => f (get a pos) (get b pos); iter2_aux f a b (Int.add pos 1) (Int.sub len 1)
  end.

(** Same as [iter] but with two arrays.
    Throws an exception when the lengths of the arrays differ. *)
Ltac2 rec iter2 (f : 'a -> 'b -> unit) (a : 'a array) (b : 'b array) : unit :=
  Control.assert_valid_argument "Array.iter2" (Int.equal (length a) (length b));
  iter2_aux f a b 0 (length a).

(** Map a function over an array. Elements are processed from first to last.
    The result is allocated as a new array, i.e. it does not alias the original array. *)
Ltac2 map (f : 'a -> 'b) (a : 'a array) : 'b array :=
  init (length a) (fun i => f (get a i)).

(** Same as [map] but with two arrays.
    Throws an exception when the lengths of the arrays differ. *)
Ltac2 map2 (f : 'a -> 'b -> 'c) (a : 'a array) (b : 'b array) : 'c array :=
  Control.assert_valid_argument "Array.map2" (Int.equal (length a) (length b));
  init (length a) (fun i => f (get a i) (get b i)).

(** Helper function for [iteri]. *)
Ltac2 rec iteri_aux (f : int -> 'a -> unit) (a : 'a array) (pos : int) (len : int) : unit :=
  match Int.equal len 0 with
  | true => ()
  | false => f pos (get a pos); iteri_aux f a (Int.add pos 1) (Int.sub len 1)
  end.

(** Iterate a function over an array, passing the index of each argument to the function.
    Elements are processed from first to last. *)
Ltac2 iteri (f : int -> 'a -> unit) (a : 'a array) : unit :=
  iteri_aux f a 0 (length a).

(** Map a function over an array, passing the index of each argument to the function.
    Elements are processed from first to last. The result is allocated as a new array,
    i.e. it does not alias the original array. *)
Ltac2 mapi (f : int -> 'a -> 'b) (a : 'a array) : 'b array :=
  init (length a) (fun i => f i (get a i)).

(** Helper function to [to_list]. *)
Ltac2 rec to_list_aux (a : 'a array) (pos : int) (len : int) : 'a list :=
  match Int.equal len 0 with
  | true => []
  | false => get a pos :: to_list_aux a (Int.add pos 1) (Int.sub len 1)
  end.

(** Convert an array to a list. *)
Ltac2 to_list (a : 'a array) : 'a list :=
  to_list_aux a 0 (length a).

(** Helper function to [of_list]. *)
Ltac2 rec of_list_aux (ls : 'a list) (dst : 'a array) (pos : int) : unit :=
  match ls with
  | [] => ()
  | hd::tl =>
      set dst pos hd;
      of_list_aux tl dst (Int.add pos 1)
  end.

(** Convert a list into an array. *)
Ltac2 of_list (ls : 'a list) : 'a array :=
  (* Don't use List.length here because the List module might depend on Array some day *)
  let rec list_length (ls : 'a list) :=
    match ls with
    | [] => 0
    | _ :: tl => Int.add 1 (list_length tl)
    end in
  match ls with
  | [] => empty
  | hd :: _ =>
      let anew := make (list_length ls) hd in
      of_list_aux ls anew 0;
      anew
  end.

(** Helper function for [fold_left]. *)
Ltac2 rec fold_left_aux (f : 'a -> 'b -> 'a) (x : 'a) (a : 'b array) (pos : int) (len : int) : 'a :=
  match Int.equal len 0 with
  | true => x
  | false => fold_left_aux f (f x (get a pos)) a (Int.add pos 1) (Int.sub len 1)
  end.

(** Left fold over an array. *)
Ltac2 fold_left (f : 'a -> 'b -> 'a) (x : 'a) (a : 'b array) : 'a :=
  fold_left_aux f x a 0 (length a).

(** Helper function for [fold_right]. *)
Ltac2 rec fold_right_aux (f : 'a -> 'b -> 'b) (a : 'a array) (x : 'b) (pos : int) (len : int) : 'b :=
  (* Note: one could compare pos<0.
     We keep an extra len parameter so that the function can be used for any sub array *)
  match Int.equal len 0 with
  | true => x
  | false => fold_right_aux f a (f (get a pos) x) (Int.sub pos 1) (Int.sub len 1)
  end.

(** Right fold over an array. *)
Ltac2 fold_right (f : 'a -> 'b -> 'b) (a : 'a array) (x : 'b) : 'b :=
  fold_right_aux f a x (Int.sub (length a) 1) (length a).

(** Helper function for [exist]. *)
Ltac2 rec exist_aux (p : 'a -> bool) (a : 'a array) (pos : int) (len : int) : bool :=
  match Int.equal len 0 with
  | true => false
  | false => match p (get a pos) with
             | true => true
             | false => exist_aux p a (Int.add pos 1) (Int.sub len 1)
             end
  end.

(** [exist f arr] checks if [f] is true for _at least one_ element of [arr].
    In particular [exist f empty] is [false].

    We would call this [exists] a la OCaml's [List.exists],
    but that would be a syntax error (because it conflicts with the notation for tactic `exists`), so instead we name it exist. *)
Ltac2 exist (p : 'a -> bool) (a : 'a array) : bool :=
  exist_aux p a 0 (length a).

(** Helper function for [for_all]. *)
Ltac2 rec for_all_aux (p : 'a -> bool) (a : 'a array) (pos : int) (len : int) : bool :=
  match Int.equal len 0 with
  | true => true
  | false => match p (get a pos) with
             | true => for_all_aux p a (Int.add pos 1) (Int.sub len 1)
             | false => false
             end
  end.

(** [for_all f arr] checks if [f] is true for _all_ elements of [arr].
    In particular [for_all f empty] is [true]. *)
Ltac2 for_all (p : 'a -> bool) (a : 'a array) : bool :=
  for_all_aux p a 0 (length a).

(** [mem eq x arr] checks if an element of [arr] is equal to [x] according
    to the user-supplied equality function [eq] *)
Ltac2 mem (eq : 'a -> 'a -> bool) (x : 'a) (a : 'a array) : bool :=
  exist (eq x) a.

(** Helper function for [for_all2]. *)
Ltac2 rec for_all2_aux (p : 'a -> 'b -> bool) (a : 'a array) (b : 'b array) (pos : int) (len : int) : bool :=
  if Int.equal len 0
  then true
  else if p (get a pos) (get b pos)
       then for_all2_aux p a b (Int.add pos 1) (Int.sub len 1)
       else false.

(** Same as [for_all] but for two lists.
    Throws an exception when the lengths of the lists differ. *)
Ltac2 for_all2 (p : 'a -> 'b -> bool) (a : 'a array) (b : 'b array) : bool :=
  let lena := length a in
  let lenb := length b in
  if Int.equal lena lenb
  then for_all2_aux p a b 0 lena
  else Control.throw_invalid_argument "Array.for_all2".

(** Same as [for_all] but for two lists.
    Returns [false] when the lengths of the lists differ. *)
Ltac2 equal (p : 'a -> 'b -> bool) (a : 'a array) (b : 'b array) : bool :=
  let lena := length a in
  let lenb := length b in
  if Int.equal lena lenb
  then for_all2_aux p a b 0 lena
  else false.

(** Reverse an array. The result is allocated as a new array,
    i.e. it does not alias the original array. *)
Ltac2 rev (ar : 'a array) : 'a array :=
  let len := length ar in
  init len (fun i => get ar (Int.sub (Int.sub len i) 1)).
