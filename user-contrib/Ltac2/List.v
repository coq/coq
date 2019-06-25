(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Ltac2 rec length (ls : 'a list) :=
  match ls with
  | [] => 0
  | _ :: xs => Int.add 1 (length xs)
  end.

Ltac2 rec compare_lengths (ls1 : 'a list) (ls2 : 'b list) :=
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

Ltac2 rec compare_length_with (ls : 'a list) (n : int) :=
  match Int.lt n 0 with
  | true => 1
  | false
    => match ls with
       | [] => Int.compare 0 n
       | _ :: ls => compare_length_with ls (Int.sub n 1)
       end
  end.

Ltac2 cons (x : 'a) (xs : 'a list) :=
  x :: xs.

(* Since Ltac-2 distinguishes between backtracking and fatal exceptions,
   we provide option and default variants of functions which throw in the
   OCaml stdlib. *)

Ltac2 hd_opt (ls : 'a list) :=
  match ls with
  | [] => None
  | x :: xs => Some x
  end.

Ltac2 hd (ls : 'a list) :=
  match ls with
  | [] => Control.throw_invalid_argument "List.hd"
  | x :: xs => x
  end.

Ltac2 tl (ls : 'a list) :=
  match ls with
  | [] => []
  | x :: xs => xs
  end.

Ltac2 rec last_opt (ls : 'a list) :=
  match ls with
  | [] => None
  | x :: xs
    => match xs with
       | [] => Some x
       | _ :: _ => last_opt xs
       end
  end.

Ltac2 last (ls : 'a list) :=
  match last_opt ls with
  | None => Control.throw_invalid_argument "List.last"
  | Some v => v
  end.

Ltac2 rec removelast (ls : 'a list) :=
  match ls with
  | [] => []
  | x :: xs
    => match xs with
       | [] => []
       | _ :: _ => x :: removelast xs
       end
  end.

Ltac2 rec nth_opt_aux (ls : 'a list) (n : int) :=
  match ls with
  | [] => None
  | x :: xs
    => match Int.equal n 0 with
       | true => Some x
       | false => nth_opt_aux xs (Int.sub n 1)
       end
  end.

Ltac2 nth_opt (ls : 'a list) (n : int) :=
  Control.assert_valid_argument "List.nth" (Int.ge n 0);
  nth_opt_aux ls n.

Ltac2 nth (ls : 'a list) (n : int) :=
  match nth_opt ls n with
  | Some v => v
  | None => Control.throw_out_of_bounds "List.nth"
  end.

Ltac2 rec rev_append (l1 : 'a list) (l2 : 'a list) :=
  match l1 with
  | [] => l2
  | a :: l => rev_append l (a :: l2)
  end.

Ltac2 rev l := rev_append l [].

Ltac2 rec append ls1 ls2 :=
  match ls1 with
  | [] => ls2
  | x :: xs => x :: append xs ls2
  end.

Ltac2 rec concat (ls : 'a list list) :=
  match ls with
  | [] => []
  | x :: xs => append x (concat xs)
  end.

Ltac2 flatten (ls : 'a list list) := concat ls.

Ltac2 rec iter (f : 'a -> unit) (ls : 'a list) :=
  match ls with
  | [] => ()
  | l :: ls => f l; iter f ls
  end.

Ltac2 rec iteri_aux (i : int) (f : int -> 'a -> unit) (ls : 'a list) :=
  match ls with
  | [] => ()
  | l :: ls => f i l; iteri_aux (Int.add i 1) f ls
  end.

Ltac2 iteri (f : int -> 'a -> unit) (ls : 'a list) :=
  iteri_aux 0 f ls.

Ltac2 rec map (f : 'a -> 'b) (ls : 'a list) :=
  match ls with
  | [] => []
  | l :: ls => f l :: map f ls
  end.

Ltac2 rec mapi_aux (i : int) (f : int -> 'a -> 'b) (ls : 'a list) :=
  match ls with
  | [] => []
  | l :: ls => f i l :: mapi_aux (Int.add i 1) f ls
  end.

Ltac2 mapi (f : int -> 'a -> 'b) (ls : 'a list) :=
  mapi_aux 0 f ls.

Ltac2 rec flat_map (f : 'a -> 'b list) (xs : 'a list) :=
  match xs with
  | [] => []
  | x :: xs => append (f x) (flat_map f xs)
  end.

(* from the OCaml std lib *)
Ltac2 rev_map (f : 'a -> 'b) (ls : 'a list) :=
  let rec rmap_f accu ls :=
      match ls with
      | [] => accu
      | a::l => rmap_f (f a :: accu) l
      end in
  rmap_f [] ls.

Ltac2 rec fold_right (f : 'a -> 'b -> 'b) (a : 'b) (ls : 'a list) :=
  match ls with
  | [] => a
  | l :: ls => f l (fold_right f a ls)
  end.

Ltac2 rec fold_left (f : 'a -> 'b -> 'a) (xs : 'b list) (a : 'a) :=
  match xs with
  | [] => a
  | x :: xs => fold_left f xs (f a x)
  end.

Ltac2 rec iter2 (f : 'a -> 'b -> unit) (ls1 : 'a list) (ls2 : 'b list) :=
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

Ltac2 rec map2 (f : 'a -> 'b -> 'c) (ls1 : 'a list) (ls2 : 'b list) :=
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

(* from the OCaml std lib *)
Ltac2 rev_map2 (f : 'a -> 'b -> 'c) (ls1 : 'a list) (ls2 : 'b list) :=
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

Ltac2 rec fold_right2 (f : 'a -> 'b -> 'c -> 'c) (a : 'c) (ls1 : 'a list) (ls2 : 'b list) :=
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
         => f l1 l2 (fold_right2 f a ls1 ls2)
       end
  end.

Ltac2 rec fold_left2 (f : 'a -> 'b -> 'c -> 'a) (ls1 : 'b list) (ls2 : 'c list) (a : 'a) :=
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
         => fold_left2 f ls1 ls2 (f a l1 l2)
       end
  end.

Ltac2 rec for_all f ls :=
  match ls with
  | [] => true
  | x :: xs => match f x with
               | true => for_all f xs
               | false => false
               end
  end.

(* we would call this [exists] a la OCaml's [List.exists], but that's a syntax error, so instead we name it exist *)
Ltac2 rec exist f ls :=
  match ls with
  | [] => false
  | x :: xs => match f x with
               | true => true
               | false => exist f xs
               end
  end.

Ltac2 rec for_all2 f xs ys :=
  match xs with
  | [] => match ys with
          | [] => true
          | y :: ys' => Control.throw_invalid_argument "List.for_all2"
          end
  | x :: xs'
    => match ys with
       | [] => Control.throw_invalid_argument "List.for_all2"
       | y :: ys'
         => match f x y with
            | true => for_all2 f xs' ys'
            | false => false
            end
       end
  end.

Ltac2 rec exist2 f xs ys :=
  match xs with
  | [] => match ys with
          | [] => false
          | y :: ys' => Control.throw_invalid_argument "List.exist2"
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

Ltac2 rec find_opt f xs :=
  match xs with
  | [] => None
  | x :: xs => match f x with
               | true => Some x
               | false => find_opt f xs
               end
  end.

Ltac2 find f xs :=
  match find_opt f xs with
  | Some v => v
  | None => Control.throw Not_found
  end.

Ltac2 rec find_rev_opt f xs :=
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

Ltac2 find_rev f xs :=
  match find_rev_opt f xs with
  | Some v => v
  | None => Control.throw Not_found
  end.

Ltac2 mem (eq : 'a -> 'a -> bool) (a : 'a) (ls : 'a list) :=
  exist (eq a) ls.

Ltac2 rec filter f xs :=
  match xs with
  | [] => []
  | x :: xs
    => match f x with
       | true => x :: filter f xs
       | false => filter f xs
       end
  end.

Ltac2 rec filter_out f xs :=
  filter (fun x => Bool.neg (f x)) xs.

Ltac2 find_all (f : 'a -> bool) (ls : 'a list) := filter f ls.

Ltac2 remove (eqb : 'a -> 'a -> bool) (x : 'a) (ls : 'a list) :=
  filter_out (eqb x) ls.

Ltac2 count_occ (eqb : 'a -> 'a -> bool) (x : 'a) (ls : 'a list) :=
  length (filter (eqb x) ls).

(* from the Coq stdlib *)
Ltac2 rec list_power (ls1 : 'a list) (ls2 : 'b list) :=
  match ls1 with
  | [] => [] :: []
  | x :: t
    => flat_map (fun f => map (fun y => (x, y) :: f) ls2)
                (list_power t ls2)
  end.

Ltac2 rec partition (f : 'a -> bool) (l : 'a list) :=
  match l with
  | [] => ([], [])
  | x :: tl
    => let (g, d) := partition f tl in
       match f x with
       | true => ((x::g), d)
       | false => (g, (x::d))
       end
  end.

(* from the Coq stdlib *)
(** [list_prod] has the same signature as [combine], but unlike
     [combine], it adds every possible pairs, not only those at the
     same position. *)

Ltac2 rec list_prod (ls1 : 'a list) (ls2 : 'b list) :=
  match ls1 with
  | [] => []
  | x :: t
    => append (map (fun y => (x, y)) ls2) (list_prod t ls2)
  end.

Ltac2 rec firstn (n : int) (ls : 'a list) :=
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

Ltac2 rec skipn (n : int) (ls : 'a list) :=
  Control.assert_valid_argument "List.skipn" (Int.ge n 0);
  match Int.equal n 0 with
  | true => ls
  | false
    => match ls with
       | [] => Control.throw_out_of_bounds "List.skipn"
       | x :: xs
         => skipn (Int.sub n 1) xs
       end
  end.

Ltac2 lastn (n : int) (ls : 'a list) :=
  let l := length ls in
  Control.assert_valid_argument "List.lastn" (Int.ge n 0);
  Control.assert_bounds "List.lastn" (Int.le n l);
  skipn (Int.sub l n).

Ltac2 rec nodup (eqb : 'a -> 'a -> bool) (ls : 'a list) :=
  match ls with
  | [] => []
  | x :: xs
    => match mem eqb x xs with
       | true => nodup eqb xs
       | false => x :: nodup eqb xs
       end
  end.

(* seq start 1 last = start :: start + 1 :: ... :: (last - 1) *)
Ltac2 rec seq (start : int) (step : int) (last : int) :=
  match Int.lt (Int.sub last start) step with
  | true
    => []
  | false
    => start :: seq (Int.add start step) step last
  end.

Ltac2 init (len : int) (f : int -> 'a) :=
  Control.assert_valid_argument "List.init" (Int.ge len 0);
  map f (seq 0 1 len).

Ltac2 repeat (x : 'a) (n : 'int) :=
  init n (fun _ => x).

Ltac2 assoc (eqk : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) :=
  let eq_key kv := let (k', _) := kv in eqk k k' in
  let (_, v) := find eq_key l in
  v.

Ltac2 assoc_opt (eqk : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) :=
  let eq_key kv := let (k', _) := kv in eqk k k' in
  match find_opt eq_key l with
  | Some kv => let (_, v) := kv in Some v
  | None => None
  end.

Ltac2 mem_assoc (eqk : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) :=
  let eq_key kv := let (k', _) := kv in eqk k k' in
  exist eq_key l.

Ltac2 remove_assoc (eqk : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) :=
  let eq_key kv := let (k', _) := kv in eqk k k' in
  filter_out eq_key l.

Ltac2 rec split (ls : ('a * 'b) list) :=
  match ls with
  | [] => ([], [])
  | xy :: tl
    => let (x, y) := xy in
       let (left, right) := split tl in
       ((x::left), (y::right))
  end.

Ltac2 rec combine (ls1 : 'a list) (ls2 : 'b list) :=
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

Ltac2 enumerate (ls : 'a list) :=
  combine (seq 0 1 (length ls)) ls.

(* from Coq stdlib *)
Ltac2 rec merge (cmp : 'a -> 'a -> int) (l1 : 'a list) (l2 : 'b list) :=
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

Ltac2 sort cmp l := iter_merge cmp [] l.

(* TODO: maybe replace this with a faster implementation *)
Ltac2 sort_uniq (cmp : 'a -> 'a -> int) (l : 'a list) :=
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
