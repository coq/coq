(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Mapping under pairs *)

let on_fst f (a,b) = (f a,b)
let on_snd f (a,b) = (a,f b)
let map_pair f (a,b) = (f a,f b)

(* Mapping under pairs *)

let on_pi1 f (a,b,c) = (f a,b,c)
let on_pi2 f (a,b,c) = (a,f b,c)
let on_pi3 f (a,b,c) = (a,b,f c)

(* Projections from triplets *)

let pi1 (a,_,_) = a
let pi2 (_,a,_) = a
let pi3 (_,_,a) = a

(* Characters *)

let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let is_digit c = (c >= '0' && c <= '9')
let is_ident_tail c =
  is_letter c || is_digit c || c = '\'' || c = '_'
let is_blank = function
  | ' ' | '\r' | '\t' | '\n' -> true
  | _ -> false

module Empty =
struct
  type t = { abort : 'a. 'a }
  let abort (x : t) = x.abort
end

(* Strings *)

module String : CString.ExtS = CString

let subst_command_placeholder s t =
  let buff = Buffer.create (String.length s + String.length t) in
  let i = ref 0 in
  while (!i < String.length s) do
    if s.[!i] = '%' && !i+1 < String.length s && s.[!i+1] = 's'
    then (Buffer.add_string buff t;incr i)
    else Buffer.add_char buff s.[!i];
    incr i
  done;
  Buffer.contents buff

(* Lists *)

module List : CList.ExtS = CList

let (@) = CList.append

(* Arrays *)

module Array : CArray.ExtS = CArray

(* Sets *)

module Set = CSet

(* Maps *)

module Map = CMap

(* Stacks *)

module Stack = CStack

(* Matrices *)

let matrix_transpose mat =
  List.fold_right (List.map2 (fun p c -> p::c)) mat
    (if List.is_empty mat then [] else List.map (fun _ -> []) (List.hd mat))

(* Functions *)

let identity x = x

(** Left-to-right function composition:
    
    [f1 %> f2] is [fun x -> f2 (f1 x)].

    [f1 %> f2 %> f3] is [fun x -> f3 (f2 (f1 x))].

    [f1 %> f2 %> f3 %> f4] is [fun x -> f4 (f3 (f2 (f1 x)))]

    etc.
*)
let (%>) f g x = g (f x)

let const x _ = x

let iterate =
  let rec iterate_f f n x =
    if n <= 0 then x else iterate_f f (pred n) (f x)
  in
  iterate_f

let repeat n f x =
  let rec loop i = if i <> 0 then (f x; loop (i - 1)) in loop n

let app_opt f x =
  match f with
  | Some f -> f x
  | None -> x

(* Stream *)

let stream_nth n st =
  try List.nth (Stream.npeek (n+1) st) n
  with Failure _ -> raise Stream.Failure

let stream_njunk n st =
  repeat n Stream.junk st

(* Delayed computations *)

type 'a delayed = unit -> 'a

let delayed_force f = f ()

(* Misc *)

type ('a, 'b) union = ('a, 'b) CSig.union = Inl of 'a | Inr of 'b
type 'a until = 'a CSig.until = Stop of 'a | Cont of 'a
type ('a, 'b) eq = ('a, 'b) CSig.eq = Refl : ('a, 'a) eq

let sym : type a b. (a, b) eq -> (b, a) eq = fun Refl -> Refl

module Union =
struct
  let map f g = function
    | Inl a -> Inl (f a)
    | Inr b -> Inr (g b)

  (** Lifting equality onto union types. *)
  let equal f g x y = match x, y with
    | Inl x, Inl y -> f x y
    | Inr x, Inr y -> g x y
    | _, _ -> false

  let fold_left f g a = function
    | Inl y -> f a y
    | Inr y -> g a y
end

let map_union = Union.map

type iexn = Exninfo.iexn

let iraise = Exninfo.iraise

let open_utf8_file_in fname =
  let is_bom s =
    Int.equal (Char.code (Bytes.get s 0)) 0xEF &&
    Int.equal (Char.code (Bytes.get s 1)) 0xBB &&
    Int.equal (Char.code (Bytes.get s 2)) 0xBF
  in
  let in_chan = open_in fname in
  let s = Bytes.make 3 ' ' in
  if input in_chan s 0 3 < 3 || not (is_bom s) then seek_in in_chan 0;
  in_chan

(** A trick which can typically be used to store on the fly the
   computation of values in the "when" clause of a "match" then
   retrieve the evaluated result in the r.h.s of the clause *)

let set_temporary_memory () =
  let a = ref None in
  (fun x -> assert (!a = None); a := Some x; x),
  (fun () -> match !a with Some x -> x | None -> assert false)
