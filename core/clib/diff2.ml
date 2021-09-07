(* copied from https://github.com/leque/ocaml-diff.git and renamed from "diff.ml" *)

(*
 * Copyright (C) 2016 OOHASHI Daichi
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *)

type 'a common =
  [ `Common of int * int * 'a ]

type 'a edit =
  [ `Added of int * 'a
  | `Removed of int * 'a
  | 'a common
  ]

module type SeqType = sig
  type t
  type elem
  val get : t -> int -> elem
  val length : t -> int
end

module type S = sig
  type t
  type elem

  val lcs :
      ?equal:(elem -> elem -> bool) ->
      t -> t -> elem common list

  val diff :
      ?equal:(elem -> elem -> bool) ->
      t -> t -> elem edit list

  val fold_left :
      ?equal:(elem -> elem -> bool) ->
      f:('a -> elem edit -> 'a) ->
      init:'a ->
      t -> t -> 'a

  val iter :
      ?equal:(elem -> elem -> bool) ->
      f:(elem edit -> unit) ->
      t -> t -> unit
end

module Make(M : SeqType) : (S with type t = M.t and type elem = M.elem) = struct
  type t = M.t
  type elem = M.elem

  let lcs ?(equal = (=)) a b =
    let n = M.length a in
    let m = M.length b in
    let mn = m + n in
    let sz = 2 * mn + 1 in
    let vd = Array.make sz 0 in
    let vl = Array.make sz 0 in
    let vr = Array.make sz [] in
    let get v i = Array.get v (i + mn) in
    let set v i x = Array.set v (i + mn) x in
    let finish () =
      let rec loop i maxl r =
        if i > mn then
          List.rev r
        else if get vl i > maxl then
          loop (i + 1) (get vl i) (get vr i)
        else
          loop (i + 1) maxl r
      in loop (- mn) 0 []
    in
    if mn = 0 then
      []
    else
      (* For d <- 0 to mn Do *)
      let rec dloop d =
        assert (d <= mn);
        (* For k <- -d to d in steps of 2 Do *)
        let rec kloop k =
          if k > d then
            dloop @@ d + 1
          else
            let x, l, r =
              if k = -d || (k <> d && get vd (k - 1) < get vd (k + 1)) then
                get vd (k + 1), get vl (k + 1), get vr (k + 1)
              else
                get vd (k - 1) + 1, get vl (k - 1), get vr (k - 1)
            in
            let x, y, l, r =
              let rec xyloop x y l r =
                if x < n && y < m && equal (M.get a x) (M.get b y) then
                  xyloop (x + 1) (y + 1) (l + 1) (`Common(x, y, M.get a x) :: r)
                else
                  x, y, l, r
              in xyloop x (x - k) l r
            in
            set vd k x;
            set vl k l;
            set vr k r;
            if x >= n && y >= m then
              (* Stop *)
              finish ()
            else
              kloop @@ k + 2
        in kloop @@ -d
      in dloop 0

  let fold_left ?(equal = (=)) ~f ~init a b =
    let ff x y = f y x in
    let fold_map f g x from to_ init =
      let rec loop i init =
        if i >= to_ then
          init
        else
          loop (i + 1) (f (g i @@ M.get x i) init)
      in loop from init
    in
    let added i x = `Added (i, x) in
    let removed i x = `Removed (i, x) in
    let rec loop cs apos bpos init =
      match cs with
      | [] ->
          init
          |> fold_map ff removed a apos (M.length a)
          |> fold_map ff added b bpos (M.length b)
      | `Common (aoff, boff, _) as e :: rest ->
          init
          |> fold_map ff removed a apos aoff
          |> fold_map ff added b bpos boff
          |> ff e
          |> loop rest (aoff + 1) (boff + 1)
    in loop (lcs ~equal a b) 0 0 init

  let diff ?(equal = (=)) a b =
    fold_left ~equal ~f:(fun xs x -> x::xs) ~init:[] a b

  let iter ?(equal = (=)) ~f a b =
    fold_left a b
      ~equal
      ~f:(fun () x -> f x)
      ~init:()
end
