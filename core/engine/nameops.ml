(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

(* Utilities *)

module Subscript =
struct

type t = {
  ss_zero : int;
  (** Number of leading zeros of the subscript *)
  ss_subs : int;
  (** Digital value of the subscript, zero meaning empty *)
}

let rec overflow n =
  Int.equal (n mod 10) 9 && (Int.equal (n / 10) 0 || overflow (n / 10))

let zero = { ss_subs = 0; ss_zero = 0 }

let succ s =
  if Int.equal s.ss_subs 0 then
    if Int.equal s.ss_zero 0 then
      (* [] -> [0] *)
      { ss_zero = 1; ss_subs = 0 }
    else
      (* [0...00] -> [0..01] *)
      { ss_zero = s.ss_zero - 1; ss_subs = 1 }
  else if overflow s.ss_subs then
    if Int.equal s.ss_zero 0 then
      (* [9...9] -> [10...0] *)
      { ss_zero = 0; ss_subs = 1 + s.ss_subs }
    else
      (* [0...009...9] -> [0...010...0] *)
      { ss_zero = s.ss_zero - 1; ss_subs = 1 + s.ss_subs }
  else
    (* [0...0n] -> [0...0{n+1}] *)
    { ss_zero = s.ss_zero; ss_subs = s.ss_subs + 1 }

let equal s1 s2 =
  Int.equal s1.ss_zero s2.ss_zero && Int.equal s1.ss_subs s2.ss_subs

let compare s1 s2 =
  (* Lexicographic order is reversed in order to ensure that [succ] is strictly
      increasing. *)
  let c = Int.compare s1.ss_subs s2.ss_subs in
  if Int.equal c 0 then Int.compare s1.ss_zero s2.ss_zero else c

end

let code_of_0 = Char.code '0'
let code_of_9 = Char.code '9'

let cut_ident skip_quote s =
  let s = Id.to_string s in
  let slen = String.length s in
  (* [n'] is the position of the first non nullary digit *)
  let rec numpart n n' =
    if Int.equal n 0 then
      (* ident made of _ and digits only [and ' if skip_quote]: don't cut it *)
      slen
    else
      let c = Char.code (String.get s (n-1)) in
      if Int.equal c code_of_0 && not (Int.equal n slen) then
        numpart (n-1) n'
      else if code_of_0 <= c && c <= code_of_9 then
        numpart (n-1) (n-1)
      else if skip_quote && (Int.equal c (Char.code '\'') || Int.equal c (Char.code '_')) then
        numpart (n-1) (n-1)
      else
        n'
  in
  numpart slen slen

let repr_ident s =
  let numstart = cut_ident false s in
  let s = Id.to_string s in
  let slen = String.length s in
  if Int.equal numstart slen then
    (s, None)
  else
    (String.sub s 0 numstart,
     Some (int_of_string (String.sub s numstart (slen - numstart))))

let make_ident sa = function
  | Some n ->
      let c = Char.code (String.get sa (String.length sa -1)) in
      let s =
        if c < code_of_0 || c > code_of_9 then sa ^ (string_of_int n)
        else sa ^ "_" ^ (string_of_int n) in
      Id.of_string s
  | None -> Id.of_string sa

let root_of_id id =
  let suffixstart = cut_ident true id in
  Id.of_string (String.sub (Id.to_string id) 0 suffixstart)

(* Return the same identifier as the original one but whose {i subscript} is incremented.
   If the original identifier does not have a suffix, [0] is appended to it.

   Example mappings:

   [bar]   ↦ [bar0]
   [bar0]  ↦ [bar1]
   [bar00] ↦ [bar01]
   [bar1]  ↦ [bar2]
   [bar01] ↦ [bar02]
   [bar9]  ↦ [bar10]
   [bar09] ↦ [bar10]
   [bar99] ↦ [bar100]
*)
let increment_subscript id =
  let id = Id.to_string id in
  let len = String.length id in
  let rec add carrypos =
    let c = id.[carrypos] in
    if is_digit c then
      if Int.equal (Char.code c) (Char.code '9') then begin
        assert (carrypos>0);
        add (carrypos-1)
      end
      else begin
        let newid = Bytes.of_string id in
        Bytes.fill newid (carrypos+1) (len-1-carrypos) '0';
        Bytes.set newid carrypos (Char.chr (Char.code c + 1));
        newid
      end
    else begin
      let newid = Bytes.of_string (id^"0") in
      if carrypos < len-1 then begin
        Bytes.fill newid (carrypos+1) (len-1-carrypos) '0';
        Bytes.set newid (carrypos+1) '1'
      end;
      newid
    end
  in Id.of_bytes (add (len-1))

let has_subscript id =
  let id = Id.to_string id in
  is_digit (id.[String.length id - 1])

let get_subscript id =
  let id0 = id in
  let id = Id.to_string id in
  let len = String.length id in
  let rec get_suf accu pos =
    if pos < 0 then (pos, accu)
    else
      let c = id.[pos] in
      if is_digit c then get_suf (Char.code c - Char.code '0' :: accu) (pos - 1)
      else (pos, accu)
  in
  let (pos, suf) = get_suf [] (len - 1) in
  if Int.equal pos (len - 1) then (id0, Subscript.zero)
  else
    let id = String.sub id 0 (pos + 1) in
    let rec compute_zeros accu = function
    | [] -> (accu, [])
    | 0 :: l -> compute_zeros (succ accu) l
    | _ :: _ as l -> (accu, l)
    in
    let (ss_zero, suf) = compute_zeros 0 suf in
    let rec compute_suf accu = function
    | [] -> accu
    | n :: l -> compute_suf (10 * accu + n) l
    in
    let ss_subs = compute_suf 0 suf in
    (Id.of_string id, { Subscript.ss_subs; ss_zero; })

let add_subscript id ss =
  if Subscript.equal Subscript.zero ss then id
  else if Int.equal ss.Subscript.ss_subs 0 then
    let id = Id.to_string id in
    let pad = String.make ss.Subscript.ss_zero '0' in
    Id.of_string (Printf.sprintf "%s%s" id pad)
  else
    let id = Id.to_string id in
    let pad = String.make ss.Subscript.ss_zero '0' in
    let suf = ss.Subscript.ss_subs in
    Id.of_string (Printf.sprintf "%s%s%i" id pad suf)

let forget_subscript id =
  let numstart = cut_ident false id in
  let newid = Bytes.make (numstart+1) '0' in
  String.blit (Id.to_string id) 0 newid 0 numstart;
  (Id.of_bytes newid)

let add_suffix id s = Id.of_string (Id.to_string id ^ s)
let add_prefix s id = Id.of_string (s ^ Id.to_string id)

let atompart_of_id id = fst (repr_ident id)

(* Names *)

module type ExtName =
sig

  include module type of struct include Names.Name end

  exception IsAnonymous

  val fold_left : ('a -> Id.t -> 'a) -> 'a -> t -> 'a
  val fold_right : (Id.t -> 'a -> 'a) -> t -> 'a -> 'a
  val iter : (Id.t -> unit) -> t -> unit
  val map : (Id.t -> Id.t) -> t -> t
  val fold_left_map : ('a -> Id.t -> 'a * Id.t) -> 'a -> t -> 'a * t
  val fold_right_map : (Id.t -> 'a -> Id.t * 'a) -> Name.t -> 'a -> Name.t * 'a
  val get_id : t -> Id.t
  val pick : t -> t -> t
  val pick_annot : t Context.binder_annot -> t Context.binder_annot -> t Context.binder_annot
  val cons : t -> Id.t list -> Id.t list
  val to_option : Name.t -> Id.t option

end

module Name : ExtName =
struct

  include Names.Name

  exception IsAnonymous

  let fold_left f a = function
    | Name id -> f a id
    | Anonymous -> a

  let fold_right f na a =
    match na with
    | Name id -> f id a
    | Anonymous -> a

  let iter f na = fold_right (fun x () -> f x) na ()

  let map f = function
    | Name id -> Name (f id)
    | Anonymous -> Anonymous

  let fold_left_map f a = function
    | Name id -> let (a, id) = f a id in (a, Name id)
    | Anonymous -> a, Anonymous

  let fold_right_map f na a = match na with
    | Name id -> let (id, a) = f id a in (Name id, a)
    | Anonymous -> Anonymous, a

  let get_id = function
    | Name id -> id
    | Anonymous -> raise IsAnonymous

  let pick na1 na2 =
    match na1 with
    | Name _ -> na1
    | Anonymous -> na2

  let pick_annot na1 na2 =
    let open Context in
    match na1.binder_name with
    | Name _ -> na1 | Anonymous -> na2

  let cons na l =
    match na with
    | Anonymous -> l
    | Name id -> id::l

  let to_option = function
    | Anonymous -> None
    | Name id -> Some id

end

(* Metavariables *)
let pr_meta = Pp.int
let string_of_meta = string_of_int
