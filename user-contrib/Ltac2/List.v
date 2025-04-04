(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The interface is an extended version of OCaml stdlib/list.ml. *)

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

(** Compute the length of a list. *)
Ltac2 rec length (ls : 'a list) : int :=
  match ls with
  | [] => 0
  | _ :: xs => Int.add 1 (length xs)
  end.

(** [compare_lengths ls1 ls2] is equal to [Int.compare (length ls1) (length ls2)],
    but is more efficient in most cases: it runs in O(min (length ls1) (length ls2))
    instead of O(max (length ls1) (length ls2)). *)
Ltac2 rec compare_lengths (ls1 : 'a list) (ls2 : 'b list) : int :=
  match ls1 with
  | []
    => match ls2 with
       | [] => 0
       | _ :: _ => -1
       end
  | _ :: ls1
    => match ls2 with
       | [] => 1
       | _ :: ls2 => compare_lengths ls1 ls2
       end
  end.

(** [compare_length_with ls n] is equal to [Int.compare (length ls) n],
    but is more efficient in most cases: it runs in O(min (length ls) n)
    instead of O(length ls). *)
Ltac2 rec compare_length_with (ls : 'a list) (n : int) : int :=
  match Int.lt n 0 with
  | true => 1
  | false
    => match ls with
       | [] => Int.compare 0 n
       | _ :: ls => compare_length_with ls (Int.sub n 1)
       end
  end.

Ltac2 cons (x : 'a) (xs : 'a list) : 'a list :=
  x :: xs.

(** Since Ltac2 distinguishes between backtracking and fatal exceptions,
    we provide option and default variants of functions which throw in the
    OCaml stdlib. *)

(** Return the first element of a list.
    Returns [None] if the list is empty. *)
Ltac2 hd_opt (ls : 'a list) : 'a option :=
  match ls with
  | [] => None
  | x :: _ => Some x
  end.

(** Return the first element of a list.
    Throw an exception if the list is empty. *)
Ltac2 hd (ls : 'a list) : 'a :=
  match ls with
  | [] => Control.throw_invalid_argument "List.hd"
  | x :: _ => x
  end.

(** Remove the first element from a list.
    The empty list is returned as is. *)
Ltac2 tl (ls : 'a list) : 'a list :=
  match ls with
  | [] => []
  | _ :: xs => xs
  end.

(** Destruct a list into its head and tail.
    Throws an exception if the list is empty. *)
Ltac2 dest (xs : 'a list) : 'a * 'a list :=
  match xs with
  | x :: xs => (x, xs)
  | [] => Control.throw_invalid_argument "List.dest: list empty"
  end.

(** Return [true] if the list is empty. *)
Ltac2 is_empty (xs : 'a list) : bool :=
  match xs with
  | _ :: _ => false
  | _ => true
  end.

(** Return the last element of a list.
    Returns [None] if the list is empty. *)
Ltac2 rec last_opt (ls : 'a list) : 'a option :=
  match ls with
  | [] => None
  | x :: xs
    => match xs with
       | [] => Some x
       | _ :: _ => last_opt xs
       end
  end.

(** Return the last element of a list.
    Throws an exception if the list is empty. *)
Ltac2 last (ls : 'a list) : 'a :=
  match last_opt ls with
  | None => Control.throw_invalid_argument "List.last"
  | Some v => v
  end.

(** Remove the last element of a list.
    The empty list is returned as is. *)
Ltac2 rec removelast (ls : 'a list) : 'a list :=
  match ls with
  | [] => []
  | x :: xs
    => match xs with
       | [] => []
       | _ :: _ => x :: removelast xs
       end
  end.

(** Helper function for [nth_opt]. *)
Ltac2 rec nth_opt_aux (ls : 'a list) (n : int) :=
  match ls with
  | [] => None
  | x :: xs
    => match Int.equal n 0 with
       | true => Some x
       | false => nth_opt_aux xs (Int.sub n 1)
       end
  end.

(** [nth_opt ls n] returns the [n]-th element [ls], starting at [0].
    Throws an exception if [n < 0]. Returns [None] if [n >= length ls]. *)
Ltac2 nth_opt (ls : 'a list) (n : int) : 'a option :=
  Control.assert_valid_argument "List.nth" (Int.ge n 0);
  nth_opt_aux ls n.

(** [nth ls n] returns the [n]-th element of [ls], starting at [0].
    Throws an exception if [n < 0] or [n >= length ls]. *)
Ltac2 nth (ls : 'a list) (n : int) : 'a :=
  match nth_opt ls n with
  | Some v => v
  | None => Control.throw_out_of_bounds "List.nth"
  end.

(** Reverse [l1], and append it with [l2]:
    [rev_append l1 l2 = append (rev l1) l2]. *)
Ltac2 rec rev_append (l1 : 'a list) (l2 : 'a list) : 'a list :=
  match l1 with
  | [] => l2
  | a :: l => rev_append l (a :: l2)
  end.

(** Reverse a list. *)
Ltac2 rev (l : 'a list) : 'a list :=
  rev_append l [].

(** Append two lists [ls1] and [ls2]. Complexity: O(length ls1). *)
Ltac2 rec append (ls1 : 'a list) (ls2 : 'a list) : 'a list :=
  match ls1 with
  | [] => ls2
  | x :: xs => x :: append xs ls2
  end.

(** Concatenate a list of lists. *)
Ltac2 rec concat (ls : 'a list list) : 'a list :=
  match ls with
  | [] => []
  | x :: xs => append x (concat xs)
  end.

(** Synonym for [concat]. *)
Ltac2 flatten (ls : 'a list list) : 'a list :=
  concat ls.

(** Iterate a function on each element of a list.
    Elements are processed from first to last. *)
Ltac2 rec iter (f : 'a -> unit) (ls : 'a list) : unit :=
  match ls with
  | [] => ()
  | l :: ls => f l; iter f ls
  end.

(** Helper function for [iteri]. *)
Ltac2 rec iteri_aux (i : int) (f : int -> 'a -> unit) (ls : 'a list) : unit :=
  match ls with
  | [] => ()
  | l :: ls => f i l; iteri_aux (Int.add i 1) f ls
  end.

(** Iterate a function [f] on each element of a list.
    [f] is additionally supplied the index of each element, starting at [0].
    Elements are processed from first to last. *)
Ltac2 iteri (f : int -> 'a -> unit) (ls : 'a list) : unit :=
  iteri_aux 0 f ls.

(** [map f [x0 ; x1 ; ... ; xN]] is [f x0 ; f x1 ; ... ; f xN].
    Elements are processed from first to last. *)
Ltac2 rec map (f : 'a -> 'b) (ls : 'a list) : 'b list :=
  match ls with
  | [] => []
  | l :: ls => f l :: map f ls
  end.

(** Helper function for [mapi]. *)
Ltac2 rec mapi_aux (i : int) (f : int -> 'a -> 'b) (ls : 'a list) : 'b list :=
  match ls with
  | [] => []
  | l :: ls => f i l :: mapi_aux (Int.add i 1) f ls
  end.

(** [mapi f [x0 ; x1 ; ... ; xN]] is [f 0 x0 ; f 1 x1 ; ... ; f N xN].
    Elements are processed from first to last. *)
Ltac2 mapi (f : int -> 'a -> 'b) (ls : 'a list) : 'b list :=
  mapi_aux 0 f ls.

(** Map a function over a list, and then concatenate the results. *)
Ltac2 rec flat_map (f : 'a -> 'b list) (xs : 'a list) : 'b list :=
  match xs with
  | [] => []
  | x :: xs => append (f x) (flat_map f xs)
  end.

(** [rev_map f l] is equal to [rev (map f l)],
    but is more efficient in most cases. *)
Ltac2 rev_map (f : 'a -> 'b) (ls : 'a list) : 'b list :=
  let rec rmap_f accu ls :=
      match ls with
      | [] => accu
      | a::l => rmap_f (f a :: accu) l
      end in
  rmap_f [] ls.

(** [fold_right f [a1; ...; an] init] is [f a1 (f a2 (... (f an init) ...))]. *)
Ltac2 rec fold_right (f : 'a -> 'b -> 'b) (ls : 'a list) (a : 'b) : 'b :=
  match ls with
  | [] => a
  | l :: ls => f l (fold_right f ls a)
  end.

(** [fold_left f init [b1; ...; bn]] is [f (... (f (f init b1) b2) ...) bn]. *)
Ltac2 rec fold_left (f : 'a -> 'b -> 'a) (a : 'a) (xs : 'b list) : 'a :=
  match xs with
  | [] => a
  | x :: xs => fold_left f (f a x) xs
  end.

Ltac2 fold_lefti (f : int -> 'a -> 'b -> 'a) (a : 'a) (xs : 'b list) : 'a :=
  let rec go i a xs :=
    match xs with
    | [] => a
    | x :: xs => go (Int.add i 1) (f i a x) xs
    end
  in go 0 a xs.

(** Iterate a function over two lists.
    Elements are processed from first to last.
    Throws an exception if the lengths of the lists differ. *)
Ltac2 rec iter2 (f : 'a -> 'b -> unit) (ls1 : 'a list) (ls2 : 'b list) : unit :=
  match ls1 with
  | []
    => match ls2 with
       | [] => ()
       | _ :: _ => Control.throw_invalid_argument "List.iter2"
       end
  | l1 :: ls1
    => match ls2 with
       | [] => Control.throw_invalid_argument "List.iter2"
       | l2 :: ls2
         => f l1 l2; iter2 f ls1 ls2
       end
  end.

(** Map a function over two lists.
    Elements are processed from first to last.
    Throws an exception if the lengths of the lists differ. *)
Ltac2 rec map2 (f : 'a -> 'b -> 'c) (ls1 : 'a list) (ls2 : 'b list) : 'c list :=
  match ls1 with
  | []
    => match ls2 with
       | [] => []
       | _ :: _ => Control.throw_invalid_argument "List.map2"
       end
  | l1 :: ls1
    => match ls2 with
       | [] => Control.throw_invalid_argument "List.map2"
       | l2 :: ls2
         => f l1 l2 :: map2 f ls1 ls2
       end
  end.

(** [rev_map2 f l1 l2] is equal to [rev (map2 f l1 l2)],
    but is more efficient in most cases. *)
Ltac2 rev_map2 (f : 'a -> 'b -> 'c) (ls1 : 'a list) (ls2 : 'b list) : 'c list :=
  let rec rmap2_f accu ls1 ls2 :=
      match ls1 with
      | []
        => match ls2 with
           | [] => accu
           | _ :: _ => Control.throw_invalid_argument "List.rev_map2"
           end
      | l1 :: ls1
        => match ls2 with
           | [] => Control.throw_invalid_argument "List.rev_map2"
           | l2 :: ls2
             => rmap2_f (f l1 l2 :: accu) ls1 ls2
           end
      end in
  rmap2_f [] ls1 ls2.

(** Right fold over two lists.
    Throws an exception if the lengths of the lists differ. *)
Ltac2 rec fold_right2 (f : 'a -> 'b -> 'c -> 'c) (ls1 : 'a list) (ls2 : 'b list) (a : 'c) : 'c :=
  match ls1 with
  | []
    => match ls2 with
       | [] => a
       | _ :: _ => Control.throw_invalid_argument "List.fold_right2"
       end
  | l1 :: ls1
    => match ls2 with
       | [] => Control.throw_invalid_argument "List.fold_right2"
       | l2 :: ls2
         => f l1 l2 (fold_right2 f ls1 ls2 a)
       end
  end.

(** Left fold over two lists.
    Throws an exception if the lengths of the lists differ. *)
Ltac2 rec fold_left2 (f : 'a -> 'b -> 'c -> 'a)  (a : 'a) (ls1 : 'b list) (ls2 : 'c list) : 'a :=
  match ls1 with
  | []
    => match ls2 with
       | [] => a
       | _ :: _ => Control.throw_invalid_argument "List.fold_left2"
       end
  | l1 :: ls1
    => match ls2 with
       | [] => Control.throw_invalid_argument "List.fold_left2"
       | l2 :: ls2
         => fold_left2 f (f a l1 l2) ls1 ls2
       end
  end.

(** [for_all f l] checks that [f] returns true on _all_ elements of the list [l].
    In particular [for_all f []] is [true]. *)
Ltac2 rec for_all (f : 'a -> bool) (ls : 'a list) : bool :=
  match ls with
  | [] => true
  | x :: xs => match f x with
               | true => for_all f xs
               | false => false
               end
  end.

(** [exist f l] checks that [f] returns true on _at least one_ element of the list [l].
    In particular [exist f []] is [false].

    We would call this [exists] a la OCaml's [List.exists],
    but that would be a syntax error (because it conflicts with the notation for tactic `exists`), so instead we name it exist. *)
Ltac2 rec exist (f : 'a -> bool) (ls : 'a list) : bool :=
  match ls with
  | [] => false
  | x :: xs => match f x with
               | true => true
               | false => exist f xs
               end
  end.

(** Helper function for [for_all2]. *)
Ltac2 rec for_all2_aux (on_length_mismatch : 'a list -> 'b list -> bool) f xs ys : bool :=
  match xs with
  | [] => match ys with
          | [] => true
          | _ :: _ => on_length_mismatch xs ys
          end
  | x :: xs'
    => match ys with
       | [] => on_length_mismatch xs ys
       | y :: ys'
         => match f x y with
            | true => for_all2_aux on_length_mismatch f xs' ys'
            | false => false
            end
       end
  end.

(** Same as [for_all] but for two lists.
    Throws an exception in case the lengths of the lists differ. *)
Ltac2 for_all2 (f : 'a -> 'b -> bool) (xs : 'a list) (ys : 'b list) : bool :=
  for_all2_aux (fun _ _ => Control.throw_invalid_argument "List.for_all2") f xs ys.

(** Same as [for_all] but for two lists.
    Returns [false] in case the lengths of the lists differ. *)
Ltac2 equal (f : 'a -> 'b -> bool) (xs : 'a list) (ys : 'b list) : bool :=
  for_all2_aux (fun _ _ => false) f xs ys.

(** Same as [exist] but for two lists.
    Throws an exception if the lengths of the lists differ. *)
Ltac2 rec exist2 (f : 'a -> 'b -> bool) (xs : 'a list) (ys : 'b list) : bool :=
  match xs with
  | [] => match ys with
          | [] => false
          | _ :: _ => Control.throw_invalid_argument "List.exist2"
          end
  | x :: xs'
    => match ys with
       | [] => Control.throw_invalid_argument "List.exist2"
       | y :: ys'
         => match f x y with
            | true => true
            | false => exist2 f xs' ys'
            end
       end
  end.

(** [find_opt f xs] returns the _first_ element of the list [xs] satisfying [f].
    Returns [None] if no element is found. *)
Ltac2 rec find_opt (f : 'a -> bool) (xs : 'a list) : 'a option :=
  match xs with
  | [] => None
  | x :: xs => match f x with
               | true => Some x
               | false => find_opt f xs
               end
  end.

(** [find f xs] returns the _first_ element of the list [xs] satisfying [f].
    Throws an exception if no element is found. *)
Ltac2 find (f : 'a -> bool) (xs : 'a list) : 'a :=
  match find_opt f xs with
  | Some v => v
  | None => Control.throw Not_found
  end.

(** [find_rev_opt f xs] returns the _last_ element of the list [xs] satisfying [f].
    Returns [None] if no element is found. *)
Ltac2 rec find_rev_opt (f : 'a -> bool) (xs : 'a list) : 'a option :=
  match xs with
  | [] => None
  | x :: xs => match find_rev_opt f xs with
               | Some v => Some v
               | None => match f x with
                         | true => Some x
                         | false => None
                         end
               end
  end.

(** [find_rev f xs] returns the _last_ element of the list [xs] satisfying [f].
    Throws an exception if no element is found. *)
Ltac2 find_rev (f : 'a -> bool) (xs : 'a list) : 'a :=
  match find_rev_opt f xs with
  | Some v => v
  | None => Control.throw Not_found
  end.

(** [mem eq a ls] checks if an element of [ls] is equal to [a] according
    to the user-supplied equality function [eq]. *)
Ltac2 mem (eq : 'a -> 'a -> bool) (a : 'a) (ls : 'a list) : bool :=
  exist (eq a) ls.

(** [filter f xs] removes all the elements of [xs] which do not satisfy [f]. *)
Ltac2 rec filter (f : 'a -> bool) (xs : 'a list) : 'a list :=
  match xs with
  | [] => []
  | x :: xs
    => match f x with
       | true => x :: filter f xs
       | false => filter f xs
       end
  end.

(** [filter_out f xs] removes all the elements of [xs] which satisfy [f]. *)
Ltac2 rec filter_out (f : 'a -> bool) (xs : 'a list) : 'a list :=
  filter (fun x => Bool.neg (f x)) xs.

(** Synonym for [filter]. *)
Ltac2 find_all (f : 'a -> bool) (ls : 'a list) : 'a list := filter f ls.

(** [remove eqb x ls] removes all elements of [ls] which are equal to [x],
    according to the user-supplied equality function [eqb]. *)
Ltac2 remove (eqb : 'a -> 'a -> bool) (x : 'a) (ls : 'a list) : 'a list :=
  filter_out (eqb x) ls.

(** [count_occ eqb x ls] counts how many elements of [ls] are equal to [x], according
    to the user-supplied equality function [eqb]. *)
Ltac2 count_occ (eqb : 'a -> 'a -> bool) (x : 'a) (ls : 'a list) : int :=
  length (filter (eqb x) ls).

(** [list_power ls1 ls2) is [ls2]^[ls1], or the set of sequences of elements
    of [ls2] indexed by elements of [ls1], sorted in lexicographic order. *)
Ltac2 rec list_power (ls1 : 'a list) (ls2 : 'b list) : ('a * 'b) list list :=
  match ls1 with
  | [] => [] :: []
  | x :: t
    => flat_map (fun f => map (fun y => (x, y) :: f) ls2)
                (list_power t ls2)
  end.

(** [partition f l] returns two lists [(l_true, l_false)] such that:
    - [l_true] is the sublist of elements of [l] which satisfy [f].
    - [l_false] is the sublist of elements of [l] which do not satisfy [f]. *)
Ltac2 rec partition (f : 'a -> bool) (l : 'a list) : 'a list * 'a list :=
  match l with
  | [] => ([], [])
  | x :: tl
    => let (g, d) := partition f tl in
       match f x with
       | true => ((x::g), d)
       | false => (g, (x::d))
       end
  end.

(** [list_prod ls1 ls2] returns the cartesian product of [ls1] and [ls2],
    i.e. the list of _all_ pairs [(x, y)] where [x] is in [ls1] and [y] is in [ls2]. *)
Ltac2 rec list_prod (ls1 : 'a list) (ls2 : 'b list) : ('a * 'b) list :=
  match ls1 with
  | [] => []
  | x :: t
    => append (map (fun y => (x, y)) ls2) (list_prod t ls2)
  end.

(** [fistn n ls] returns the first [n] elements of [ls].
    Throws an exception if [n < 0] or [n > length ls]. *)
Ltac2 rec firstn (n : int) (ls : 'a list) : 'a list :=
  Control.assert_valid_argument "List.firstn" (Int.ge n 0);
  match Int.equal n 0 with
  | true => []
  | false
    => match ls with
       | [] => Control.throw_out_of_bounds "List.firstn"
       | x :: xs
         => x :: firstn (Int.sub n 1) xs
       end
  end.

(** [skipn n ls] removes the first [n] elements of [ls].
    Throws an exception if [n < 0] or [n > length ls]. *)
Ltac2 rec skipn (n : int) (ls : 'a list) : 'a list :=
  Control.assert_valid_argument "List.skipn" (Int.ge n 0);
  match Int.equal n 0 with
  | true => ls
  | false
    => match ls with
       | [] => Control.throw_out_of_bounds "List.skipn"
       | _ :: xs
         => skipn (Int.sub n 1) xs
       end
  end.

(** [lastn n ls] returns the last [n] elements of [ls].
    Throws an exception if [n < 0] or [n > length ls]. *)
Ltac2 lastn (n : int) (ls : 'a list) : 'a list :=
  let l := length ls in
  Control.assert_valid_argument "List.lastn" (Int.ge n 0);
  Control.assert_bounds "List.lastn" (Int.le n l);
  skipn (Int.sub l n) ls.

(** [nodup eqb ls] removes duplicates from [ls], according
    to the user-suppplied equality function [eq]. *)
Ltac2 rec nodup (eqb : 'a -> 'a -> bool) (ls : 'a list) : 'a list :=
  match ls with
  | [] => []
  | x :: xs
    => match mem eqb x xs with
       | true => nodup eqb xs
       | false => x :: nodup eqb xs
       end
  end.

(** [seq start step last] returns the list [start ; (start + step) ; (start + 2*step) ; ...],
    stopping when [start + n*step >= last]. In particular the lower bound [start] is included,
    whereas the upper bound [last] is excluded. *)
Ltac2 rec seq (start : int) (step : int) (last : int) : int list :=
  match Int.lt (Int.sub last start) step with
  | true
    => []
  | false
    => start :: seq (Int.add start step) step last
  end.

(** [init n f] returns the list [f 0 ; f 1 ; ... ; f (n-1)].
    Throws an exception if [n < 0]. *)
Ltac2 init (n : int) (f : int -> 'a) : 'a list :=
  Control.assert_valid_argument "List.init" (Int.ge n 0);
  map f (seq 0 1 n).

(** [repeat x n] returns the list of length [n] with all elements equal to [x]. *)
Ltac2 repeat (x : 'a) (n : int) : 'a list :=
  init n (fun _ => x).

(** [assoc eqk k l] returns the first value associated to key [k] in an association list [l],
    using [eqk] to compare keys for equality.
    Throws an exception if no value is found. *)
Ltac2 assoc (eqk : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : 'v :=
  let eq_key kv := let (k', _) := kv in eqk k k' in
  let (_, v) := find eq_key l in
  v.

(** [assoc eqk k l] returns the first value associated to key [k] in an association list [l],
    using [eqk] to compare keys for equality.
    Returns [None] if no value is found. *)
Ltac2 assoc_opt (eqk : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : 'v option :=
  let eq_key kv := let (k', _) := kv in eqk k k' in
  match find_opt eq_key l with
  | Some kv => let (_, v) := kv in Some v
  | None => None
  end.

(** [mem_assoc eqk k l] checks if the key [k] is present in an association list [l],
    using [eqk] to compare keys for equality. *)
Ltac2 mem_assoc (eqk : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : bool :=
  let eq_key kv := let (k', _) := kv in eqk k k' in
  exist eq_key l.

(** [remove_assoc eqk k l] removes _all_ key/value pairs associated with key [k]
    from an association list [l], using [eqk] to compare keys for equality. *)
Ltac2 remove_assoc (eqk : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : ('k * 'v) list :=
  let eq_key kv := let (k', _) := kv in eqk k k' in
  filter_out eq_key l.

(** Split a list of pairs into a pair of lists. *)
Ltac2 rec split (ls : ('a * 'b) list) : 'a list * 'b list :=
  match ls with
  | [] => ([], [])
  | xy :: tl
    => let (x, y) := xy in
       let (left, right) := split tl in
       ((x::left), (y::right))
  end.

(** Combine two lists into a list of pairs. Only pairs of elements
    at the same position are considered.
    Throws an exception if the lengths of the lists differ. *)
Ltac2 rec combine (ls1 : 'a list) (ls2 : 'b list) : ('a * 'b) list :=
  match ls1 with
  | []
    => match ls2 with
       | [] => []
       | _ :: _ => Control.throw_invalid_argument "List.combine"
       end
  | x :: xs
    => match ls2 with
       | y :: ys
         => (x, y) :: combine xs ys
       | [] => Control.throw_invalid_argument "List.combine"
       end
  end.

(** [enumerate [x0 ; x1 ; x2 ; ...]] returns the list [(0, x0) ; (1, x1) ; (2, x2) ; ...]. *)
Ltac2 enumerate (ls : 'a list) :=
  mapi (fun i v => (i,v)) ls.

(** Merge two list sorted in increasing order into a sorted list,
    using a user-provided comparison function. *)
Ltac2 rec merge (cmp : 'a -> 'a -> int) (l1 : 'a list) (l2 : 'a list) : 'a list :=
  let rec merge_aux l2 :=
      match l1 with
      | [] => l2
      | a1 :: l1'
        => match l2 with
           | [] => l1
           | a2 :: l2'
             => match Int.le (cmp a1 a2) 0 with
                | true => a1 :: merge cmp l1' l2
                | false => a2 :: merge_aux l2'
                end
           end
      end in
  merge_aux l2.

Ltac2 rec merge_list_to_stack cmp stack l :=
  match stack with
  | [] => [Some l]
  | l' :: stack'
    => match l' with
       | None => Some l :: stack'
       | Some l'
         => None :: merge_list_to_stack cmp stack' (merge cmp l' l)
       end
  end.

Ltac2 rec merge_stack cmp stack :=
  match stack with
  | [] => []
  | l :: stack'
    => match l with
       | None => merge_stack cmp stack'
       | Some l => merge cmp l (merge_stack cmp stack')
       end
  end.

Ltac2 rec iter_merge cmp stack l :=
  match l with
  | [] => merge_stack cmp stack
  | a::l' => iter_merge cmp (merge_list_to_stack cmp stack [a]) l'
  end.

(** [sort cmp l] sorts the list [l] in increasing order,
    according to the user-supplied comparison function [cmp].

    It is currently implemented using a variant of merge sort. *)
Ltac2 sort (cmp : 'a -> 'a -> int) (l : 'a list) : 'a list :=
  iter_merge cmp [] l.

(** [sort cmp l] sorts the list [l] in increasing order and removes duplicates,
    according to the user-supplied comparison function [cmp].

    This takes advantage of the fact that removing duplicates from a sorted list
    is much faster than for an arbitrary list.  *)
Ltac2 sort_uniq (cmp : 'a -> 'a -> int) (l : 'a list) : 'a list :=
  let rec uniq l :=
      match l with
      | [] => []
      | x1 :: xs
        => match xs with
           | [] => x1 :: xs
           | x2 :: _
             => match Int.equal (cmp x1 x2) 0 with
                | true => uniq xs
                | false => x1 :: uniq xs
                end
           end
      end in
  uniq (sort cmp l).

(** [inclusive_range lb ub] returns the list [lb ; lb+1 ; lb+2 ; ... ; up].
    In particular both the lower bound [lb] and upper bound [ub] are included.  *)
Ltac2 inclusive_range (lb : int) (ub : int) : int list :=
  seq lb 1 (Int.add ub 1).

(** [range lb ub] returns the list [lb ; lb+1 ; lb+2 ; ... ; up-1].
    In particular the lower bound [lb] is included, whereas the upper bound [ub] is excluded. *)
Ltac2 range (lb : int) (ub : int) : int list :=
  seq lb 1 ub.

(** [concat_rev [x1; ..; xN-1; xN]] computes [rev xN ++ rev xN-1 ++ .. ++ x1].
    Note that [x1] is not reversed and appears in its original order.

    [concat_rev] is faster than [concat] and should be preferred over [concat]
    when the order of items does not matter. *)
Ltac2 concat_rev (ls : 'a list list) : 'a list :=
  let rec go ls acc :=
    match ls with
    | [] => acc
    | l :: ls => go ls (rev_append l acc)
    end
  in
  match ls with
  | [] => []
  | l :: ls => go ls l
  end.

(** [map_filter f l] maps [f] over [l], then removes all elements that are [None]. *)
Ltac2 rec map_filter (f : 'a -> 'b option) (l : 'a list) : 'b list :=
  match l with
  | [] => []
  | x :: l =>
    match f x with
    | Some y => y :: map_filter f l
    | None => map_filter f l
    end
  end.
