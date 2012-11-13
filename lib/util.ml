(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

let is_letter c = (c >= 'a' && c <= 'z') or (c >= 'A' && c <= 'Z')
let is_digit c = (c >= '0' && c <= '9')
let is_ident_tail c =
  is_letter c or is_digit c || c = '\'' or c = '_'
let is_blank = function
  | ' ' | '\r' | '\t' | '\n' -> true
  | _ -> false

(* Strings *)

module String : CString.ExtS = CString

let parse_loadpath s =
  let l = String.split '/' s in
  if List.mem "" l then
    invalid_arg "parse_loadpath: find an empty dir in loadpath";
  l

let subst_command_placeholder s t =
  let buff = Buffer.create (String.length s + String.length t) in
  let i = ref 0 in
  while (!i < String.length s) do
    if s.[!i] = '%' & !i+1 < String.length s & s.[!i+1] = 's'
    then (Buffer.add_string buff t;incr i)
    else Buffer.add_char buff s.[!i];
    incr i
  done;
  Buffer.contents buff

module Stringset = Set.Make(String)
module Stringmap = Map.Make(String)

(* Lists *)

module List : CList.ExtS = CList

let (@) = CList.append

(* Arrays *)

module Array : CArray.ExtS = CArray

(* Matrices *)

let matrix_transpose mat =
  List.fold_right (List.map2 (fun p c -> p::c)) mat
    (if mat = [] then [] else List.map (fun _ -> []) (List.hd mat))

(* Functions *)

let identity x = x

let compose f g x = f (g x)

let const x _ = x

let iterate f =
  let rec iterate_f n x =
    if n <= 0 then x else iterate_f (pred n) (f x)
  in
  iterate_f

let repeat n f x =
  let rec loop i = if i <> 0 then (f x; loop (i - 1)) in loop n

let iterate_for a b f x =
  let rec iterate i v = if i > b then v else iterate (succ i) (f i v) in
  iterate a x

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

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset = Set.Make(Int)
module Intmap = Map.Make(Int)

(*s interruption *)

let interrupt = ref false
let check_for_interrupt () =
  if !interrupt then begin interrupt := false; raise Sys.Break end
