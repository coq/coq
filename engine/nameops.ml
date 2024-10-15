(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

(** Segment trees: efficient lookup of the next free integer *)
module SegTree :
sig
  type t
  val empty : t
  val mem : int -> t -> bool
  val add : int -> t -> t
  val remove : int -> t -> t

  val next : int -> t -> int
  (** [next n s] returns the smallest integer [k] not in [s] s.t. [n <= k] *)

  val fresh : int -> t -> int * t
  (** Efficient composition of [next] and [add] *)

  val max_elt_opt : t -> int option

end =
struct

module Segment =
struct
  type t = int * int (* segment [p, q[, in particular p < q *)
  let compare (p, _) (q, _) = Int.compare p q
end

module SegSet = Set.Make(Segment)

type t = SegSet.t
(* Invariants: forall [p1, q1[, [p2, q2[ in such a set, either:
  - p1 = p2 and q1 = q2
  - p1 < q1 < p2 < q2
  - p2 < q2 < p1 < q1 *)

let empty = SegSet.empty

let mem n s =
  let find (_p, q) = n < q in
  match SegSet.find_first_opt find s with
  | None -> false
  | Some (p, _q) -> p <= n

let add n s =
  let find_min (_p, q) = n < q in
  let find_max (_p, q) = q <= n in
  match SegSet.find_first_opt find_min s with
  | None ->
    (* n larger than all elements *)
    begin match SegSet.max_elt_opt s with
    | None -> SegSet.add (n, n + 1) s
    | Some (pl, ql) ->
      if Int.equal n ql then SegSet.add (pl, n + 1) (SegSet.remove (pl, ql) s)
      else SegSet.add (n, n + 1) s
    end
  | Some (pr, qr) ->
    if pr <= n then s (* already present *)
    else match SegSet.find_last_opt find_max s with
    | None ->
      (* n smaller than all elements *)
      if Int.equal pr (n + 1) then
        SegSet.add (n, qr) (SegSet.remove (pr, qr) s)
      else SegSet.add (n, n + 1) s
    | Some (pl, ql) ->
      (* pl < ql <= n < pr < qr *)
      if Int.equal ql n && Int.equal pr (n + 1) then
        SegSet.add (pl, qr) (SegSet.remove (pl, ql) (SegSet.remove (pr, qr) s))
      else if Int.equal ql n then
        SegSet.add (pl, n + 1) (SegSet.remove (pl, ql) s)
      else if Int.equal pr (n + 1) then
        SegSet.add (n, qr) (SegSet.remove (pr, qr) s)
      else
        SegSet.add (n, n + 1) s

let remove n s =
  let find_min (_p, q) = n < q in
  match SegSet.find_first_opt find_min s with
  | None -> s
  | Some (pr, qr) ->
    if pr <= n then
      let s = SegSet.remove (pr, qr) s in
      if Int.equal (pr + 1) qr then s
      else if Int.equal pr n then SegSet.add (n + 1, qr) s
      else if Int.equal (n + 1) qr then SegSet.add (pr, n) s
      else SegSet.add (pr, n) (SegSet.add (n + 1, qr) s)
   else s

let next n s =
  let find (_p, q) = n < q in
  match SegSet.find_first_opt find s with
  | None -> n
  | Some (p, q) -> if p <= n then q else n

let fresh n s =
  let find_min (_p, q) = n < q in
  let find_max (_p, q) = q <= n in
  match SegSet.find_first_opt find_min s with
  | None ->
    let s = match SegSet.max_elt_opt s with
    | None -> SegSet.add (n, n + 1) s
    | Some (pl, ql) ->
      if Int.equal n ql then SegSet.add (pl, n + 1) (SegSet.remove (pl, ql) s)
      else SegSet.add (n, n + 1) s
    in
    n, s
  | Some (pr, qr) ->
    if pr <= n then
      (* equivalent to adding qr *)
      let next = SegSet.find_first_opt (fun (p, _q) -> qr < p) s in
      let s = match next with
      | None -> SegSet.add (pr, qr + 1) (SegSet.remove (pr, qr) s)
      | Some (pk, qk) ->
        if Int.equal (qr + 1) pk then
          SegSet.add (pr, qk) (SegSet.remove (pk, qk) (SegSet.remove (pr, qr) s))
        else
          SegSet.add (pr, qr + 1) (SegSet.remove (pr, qr) s)
      in
      qr, s
    else
      let s = match SegSet.find_last_opt find_max s with
      | None ->
        if Int.equal pr (n + 1) then
          SegSet.add (n, qr) (SegSet.remove (pr, qr) s)
        else SegSet.add (n, n + 1) s
      | Some (pl, ql) ->
        if Int.equal ql n && Int.equal pr (n + 1) then
          SegSet.add (pl, qr) (SegSet.remove (pl, ql) (SegSet.remove (pr, qr) s))
        else if Int.equal ql n then
          SegSet.add (pl, n + 1) (SegSet.remove (pl, ql) s)
        else if Int.equal pr (n + 1) then
          SegSet.add (n, qr) (SegSet.remove (pr, qr) s)
        else
          SegSet.add (n, n + 1) s
      in
      n, s

let max_elt_opt s = match SegSet.max_elt_opt s with
| None -> None
| Some (p, q) -> Some (q - 1)

end

module SubSet =
struct

  type t = {
    num : SegTree.t;
    pre : SegTree.t list; (* lists are OK because we are already logarithmic *)
  }
  (* We represent sets of subscripts by case-splitting on ss_zero.
     If it is zero, we store the number in the [num] set. Otherwise, we know
     the set of possible values is finite. At position k, [pre] contains a set
     of maximum size 10^k representing k-digit numbers with at least one leading
     zero. *)

  let empty = {
    num = SegTree.empty;
    pre = [];
  }

  let rec pow10 k accu = if k <= 0 then accu else pow10 (k - 1) (10 * accu)

  let rec log10 n accu = if n <= 0 then accu else log10 (n / 10) (accu + 1)

  let max_subscript ss =
    let exp = log10 ss.Subscript.ss_subs 0 + ss.Subscript.ss_zero - 1 in
    pow10 exp 1

  let add ss s =
    let open Subscript in
    if Int.equal ss.ss_zero 0 then
      { s with num = SegTree.add ss.ss_subs s.num }
    else
      let pre =
        let len = List.length s.pre in
        if len < ss.ss_zero then
          s.pre @ List.make (ss.ss_zero - len) SegTree.empty
        else s.pre
      in
      let set = match List.nth_opt pre (ss.ss_zero - 1) with
      | None -> assert false
      | Some m -> SegTree.add ss.ss_subs m
      in
      { s with pre = List.assign pre (ss.ss_zero - 1) set }

  let remove ss s =
    let open Subscript in
    if Int.equal ss.ss_zero 0 then
      { s with num = SegTree.remove ss.ss_subs s.num }
    else match List.nth_opt s.pre (ss.ss_zero - 1) with
    | None -> s
    | Some m ->
      let m = SegTree.remove ss.ss_subs m in
      { s with pre = List.assign s.pre (ss.ss_zero - 1) m }

  let mem ss s =
    let open Subscript in
    if Int.equal ss.ss_zero 0 then SegTree.mem ss.ss_subs s.num
    else match List.nth_opt s.pre (ss.ss_zero - 1) with
    | None -> false
    | Some m -> SegTree.mem ss.ss_subs m

  let ss_O = { Subscript.ss_zero = 1; ss_subs = 0 } (* [0] *)

  let next ss s =
    let open Subscript in
    if ss.ss_zero > 0 then
      match List.nth_opt s.pre (ss.ss_zero - 1) with
      | None -> ss
      | Some m ->
        let next = SegTree.next ss.ss_subs m in
        let max = max_subscript ss in
        if max <= next then (* overflow *)
          { ss_zero = 0; ss_subs = SegTree.next max s.num }
        else
          { ss_zero = ss.ss_zero; ss_subs = next }
    else if Int.equal ss.ss_subs 0 then
      (* Handle specially [] *)
      if not @@ SegTree.mem 0 s.num then Subscript.zero
      else match s.pre with
      | [] -> ss_O
      | m :: _ ->
        if SegTree.mem 0 m then { ss_zero = 0; ss_subs = SegTree.next 1 s.num }
        else ss_O
    else
      { ss_zero = 0; ss_subs = SegTree.next ss.ss_subs s.num }

  let fresh ss s =
    let open Subscript in
    if ss.ss_zero > 0 then
      match List.nth_opt s.pre (ss.ss_zero - 1) with
      | None -> ss, add ss s
      | Some m ->
        let subs, m = SegTree.fresh ss.ss_subs m in
        let max = max_subscript ss in
        if max <= subs then
          let subs, num = SegTree.fresh max s.num in
          { ss_zero = 0; ss_subs = subs }, { s with num }
        else
          let s = { s with pre = List.assign s.pre (ss.ss_zero - 1) m } in
          { ss_zero = ss.ss_zero; ss_subs = subs }, s
    else if Int.equal ss.ss_subs 0 then
      if not @@ SegTree.mem 0 s.num then
        Subscript.zero, { num = SegTree.add 0 s.num; pre = s.pre }
      else match s.pre with
      | [] -> ss_O, { num = s.num; pre = [SegTree.add 0 SegTree.empty] }
      | m :: rem ->
        if SegTree.mem 0 m then
          let subs, num = SegTree.fresh 1 s.num in
          { ss_zero = 0; ss_subs = subs }, { num; pre = s.pre }
        else ss_O, { num = s.num; pre = SegTree.add 0 SegTree.empty :: rem }
    else
      let subs, num = SegTree.fresh ss.ss_subs s.num in
      { ss_zero = 0; ss_subs = subs }, { s with num }

  let max_elt_opt s =
    let mapi i m = match SegTree.max_elt_opt m with
    | None -> None
    | Some k -> Some { Subscript.ss_zero = i; ss_subs = k }
    in
    let maxs = List.mapi mapi (s.num :: s.pre) in
    let fold s accu = match s with
    | None -> accu
    | Some ss ->
      match accu with
      | None -> Some ss
      | Some ss' -> if Subscript.compare ss ss' <= 0 then accu else s
    in
    List.fold_left fold None maxs

end

module Fresh =
struct

type t = SubSet.t Id.Map.t

let empty = Id.Map.empty

let add id m =
  let (id, s) = get_subscript id in
  let old = try Id.Map.find id m with Not_found -> SubSet.empty in
  Id.Map.add id (SubSet.add s old) m

let remove id m =
  let (id, s) = get_subscript id in
  match Id.Map.find id m with
  | old -> Id.Map.add id (SubSet.remove s old) m
  | exception Not_found -> m

let mem id m =
  let (id, s) = get_subscript id in
  try SubSet.mem s (Id.Map.find id m)
  with Not_found -> false

let next id0 m =
  let (id, s) = get_subscript id0 in
  match Id.Map.find_opt id m with
  | None -> id0
  | Some old ->
    let ss = SubSet.next s old in
    add_subscript id ss

let fresh id0 m =
  let (id, s) = get_subscript id0 in
  match Id.Map.find_opt id m with
  | None ->
    id0, Id.Map.add id (SubSet.add s SubSet.empty) m
  | Some old ->
    let ss, n = SubSet.fresh s old in
    add_subscript id ss, Id.Map.add id n m

let of_list l =
  List.fold_left (fun accu id -> add id accu) empty l

let of_set s =
  Id.Set.fold add s empty

let of_named_context_val s =
  of_set @@ Environ.ids_of_named_context_val s

let max_map s =
  let filter id m = SubSet.max_elt_opt m in
  Id.Map.filter_map filter s

end

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
  val pick_annot : (t,'r) Context.pbinder_annot -> (t,'r) Context.pbinder_annot -> (t,'r) Context.pbinder_annot
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
