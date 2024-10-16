(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(* ** Utility functions **                                              *)
(*                                                                      *)
(* - Modules CoqToCaml, CamlToCoq                                       *)
(* - Modules Cmp, Tag, TagSet                                           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

open NumCompat
module Z_ = NumCompat.Z

module ISet = struct
  include Int.Set

  let pp o s = iter (fun i -> Printf.fprintf o "%i " i) s
end

module IMap = struct
  include Int.Map

  let from k m =
    let _, _, r = split (k - 1) m in
    r
end

let rec pp_list s f o l =
  match l with
  | [] -> ()
  | [e] -> f o e
  | e :: l -> f o e; output_string o s; pp_list s f o l

let finally f rst =
  try
    let res = f () in
    rst (); res
  with reraise ->
    (try rst () with any -> raise reraise);
    raise reraise

let all_pairs f l =
  let pair_with acc e l = List.fold_left (fun acc x -> f e x :: acc) acc l in
  let rec xpairs acc l =
    match l with [] -> acc | e :: lx -> xpairs (pair_with acc e l) lx
  in
  xpairs [] l

let rec is_sublist f l1 l2 =
  match (l1, l2) with
  | [], _ -> true
  | e :: l1', [] -> false
  | e :: l1', e' :: l2' ->
    if f e e' then is_sublist f l1' l2' else is_sublist f l1 l2'

let extract pred l =
  List.fold_left
    (fun (fd, sys) e ->
      match fd with
      | None -> (
        match pred e with None -> (fd, e :: sys) | Some v -> (Some (v, e), sys)
        )
      | _ -> (fd, e :: sys))
    (None, []) l

let extract_all pred l =
  List.fold_left
    (fun (s1, s2) e ->
      match pred e with None -> (s1, e :: s2) | Some v -> (v :: s1, s2))
    ([], []) l

let simplify f sys =
  let sys', b =
    List.fold_left
      (fun (sys', b) c ->
        match f c with None -> (c :: sys', b) | Some c' -> (c' :: sys', true))
      ([], false) sys
  in
  if b then Some sys' else None

let generate_acc f acc sys =
  List.fold_left
    (fun sys' c -> match f c with None -> sys' | Some c' -> c' :: sys')
    acc sys

let generate f sys = generate_acc f [] sys

let saturate p f sys =
  let rec sat acc l =
    match extract p l with
    | None, _ -> acc
    | Some r, l' ->
      let n = generate (f r) (l' @ acc) in
      sat (n @ acc) l'
  in
  try sat [] sys
  with x ->
    Printexc.print_backtrace stdout;
    raise x

let iterate_until_stable f x =
  let rec iter x = match f x with None -> x | Some x' -> iter x' in
  iter x

let rec app_funs l x =
  match l with
  | [] -> None
  | f :: fl -> ( match f x with None -> app_funs fl x | Some x' -> Some x' )

(**
  * MODULE: Rocq to Caml data-structure mappings
  *)

module CoqToCaml = struct
  open Micromega

  let rec nat = function O -> 0 | S n -> nat n + 1

  let rec positive p =
    match p with
    | XH -> 1
    | XI p -> 1 + (2 * positive p)
    | XO p -> 2 * positive p

  let n nt = match nt with N0 -> 0 | Npos p -> positive p

  let rec index i =
    (* Swap left-right ? *)
    match i with XH -> 1 | XI i -> 1 + (2 * index i) | XO i -> 2 * index i

  let rec positive_big_int p =
    match p with
    | XH -> Z_.one
    | XI p -> Z_.add Z_.one (Z_.mul Z_.two (positive_big_int p))
    | XO p -> Z_.mul Z_.two (positive_big_int p)

  let z_big_int x =
    match x with
    | Z0 -> Z_.zero
    | Zpos p -> positive_big_int p
    | Zneg p -> Z_.neg (positive_big_int p)

  let z x = match x with Z0 -> 0 | Zpos p -> index p | Zneg p -> -index p

  let q_to_num {qnum = x; qden = y} =
    let open Q.Notations in
    Q.of_bigint (z_big_int x) // Q.of_bigint (z_big_int (Zpos y))
end

(**
  * MODULE: Caml to Rocq data-structure mappings
  *)

module CamlToCoq = struct
  open Micromega

  let rec nat = function 0 -> O | n -> S (nat (n - 1))

  let rec positive n =
    if Int.equal n 1 then XH
    else if Int.equal (n land 1) 1 then XI (positive (n lsr 1))
    else XO (positive (n lsr 1))

  let n nt =
    if nt < 0 then assert false
    else if Int.equal nt 0 then N0
    else Npos (positive nt)

  let rec index n =
    if Int.equal n 1 then XH
    else if Int.equal (n land 1) 1 then XI (index (n lsr 1))
    else XO (index (n lsr 1))

  let z x =
    match compare x 0 with
    | 0 -> Z0
    | 1 -> Zpos (positive x)
    | _ ->
      (* this should be -1 *)
      Zneg (positive (-x))

  let positive_big_int n =
    let rec _pos n =
      if Z_.equal n Z_.one then XH
      else
        let q, m = Z_.quomod n Z_.two in
        if Z_.equal Z_.one m then XI (_pos q) else XO (_pos q)
    in
    _pos n

  let bigint x =
    match Z_.sign x with
    | 0 -> Z0
    | 1 -> Zpos (positive_big_int x)
    | _ -> Zneg (positive_big_int (Z_.neg x))

  let q n =
    { Micromega.qnum = bigint (Q.num n)
    ; Micromega.qden = positive_big_int (Q.den n) }
end

(**
  * MODULE: Comparisons on lists: by evaluating the elements in a single list,
  * between two lists given an ordering, and using a hash computation
  *)

module Cmp = struct
  let rec compare_lexical l =
    match l with
    | [] -> 0 (* Equal *)
    | f :: l ->
      let cmp = f () in
      if Int.equal cmp 0 then compare_lexical l else cmp

  let rec compare_list cmp l1 l2 =
    match (l1, l2) with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | e1 :: l1, e2 :: l2 ->
      let c = cmp e1 e2 in
      if Int.equal c 0 then compare_list cmp l1 l2 else c
end

(**
  * MODULE: Labels for atoms in propositional formulas.
  * Tags are used to identify unused atoms in CNFs, and propagate them back to
  * the original formula. The translation back to Rocq then ignores these
  * superfluous items, which speeds the translation up a bit.
  *)

module type Tag = sig
  type t = int

  val from : int -> t
  val next : t -> t
  val pp : out_channel -> t -> unit
  val compare : t -> t -> int
  val max : t -> t -> t
  val to_int : t -> int
end

module Tag : Tag = struct
  type t = int

  let from i = i
  let next i = i + 1
  let max : int -> int -> int = max
  let pp o i = output_string o (string_of_int i)
  let compare : int -> int -> int = Int.compare
  let to_int x = x
end

(**
  * MODULE: Ordered sets of tags.
  *)

module TagSet = struct
  include Set.Make (Tag)
end

module McPrinter = struct
  module Mc = Micromega

  let pp_nat o n = Printf.fprintf o "%i" (CoqToCaml.nat n)

  let pp_positive o x = Printf.fprintf o "%i" (CoqToCaml.positive x)

  let pp_z o x =
  Printf.fprintf o "%s" (NumCompat.Z.to_string (CoqToCaml.z_big_int x))

  let pp_pol pp_c o e =
    let rec pp_pol o e =
    match e with
    | Mc.Pc n -> Printf.fprintf o "Pc %a" pp_c n
    | Mc.Pinj (p, pol) ->
      Printf.fprintf o "Pinj(%a,%a)" pp_positive p pp_pol pol
    | Mc.PX (pol1, p, pol2) ->
      Printf.fprintf o "PX(%a,%a,%a)" pp_pol pol1 pp_positive p pp_pol pol2
  in
  pp_pol o e

  let pp_psatz pp_z o e =
  let rec pp_cone o e =
    match e with
    | Mc.PsatzLet (e1, e2) ->
      Printf.fprintf o "(Let %a %a)%%nat" pp_cone e1 pp_cone e2
    | Mc.PsatzIn n -> Printf.fprintf o "(In %a)%%nat" pp_nat n
    | Mc.PsatzMulC (e, c) ->
      Printf.fprintf o "( %a [*] %a)" (pp_pol pp_z) e pp_cone c
    | Mc.PsatzSquare e -> Printf.fprintf o "(%a^2)" (pp_pol pp_z) e
    | Mc.PsatzAdd (e1, e2) ->
      Printf.fprintf o "(%a [+] %a)" pp_cone e1 pp_cone e2
    | Mc.PsatzMulE (e1, e2) ->
      Printf.fprintf o "(%a [*] %a)" pp_cone e1 pp_cone e2
    | Mc.PsatzC p -> Printf.fprintf o "(%a)%%positive" pp_z p
    | Mc.PsatzZ -> Printf.fprintf o "0"
  in
  pp_cone o e

let rec pp_proof_term o = function
  | Micromega.DoneProof -> Printf.fprintf o "D"
  | Micromega.RatProof (cone, rst) ->
    Printf.fprintf o "R[%a,%a]" (pp_psatz pp_z) cone pp_proof_term rst
  | Micromega.CutProof (cone, rst) ->
    Printf.fprintf o "C[%a,%a]" (pp_psatz pp_z) cone pp_proof_term rst
  | Micromega.SplitProof (p, p1, p2) ->
    Printf.fprintf o "S[%a,%a,%a]" (pp_pol pp_z) p pp_proof_term p1
      pp_proof_term p2
  | Micromega.EnumProof (c1, c2, rst) ->
    Printf.fprintf o "EP[%a,%a,%a]" (pp_psatz pp_z) c1 (pp_psatz pp_z) c2
      (pp_list "," pp_proof_term)
      rst
  | Micromega.ExProof (p, prf) ->
    Printf.fprintf o "Ex[%a,%a]" pp_positive p pp_proof_term prf

end


(** As for Unix.close_process, our Unix.waipid will ignore all EINTR *)

let rec waitpid_non_intr pid =
  try snd (Unix.waitpid [] pid)
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr pid

(**
  * Forking routine, plumbing the appropriate pipes where needed.
  *)

let command exe_path args vl =
  (* creating pipes for stdin, stdout, stderr *)
  let stdin_read, stdin_write = Unix.pipe ()
  and stdout_read, stdout_write = Unix.pipe ()
  and stderr_read, stderr_write = Unix.pipe () in
  (* Create the process *)
  let pid =
    Unix.create_process exe_path args stdin_read stdout_write stderr_write
  in
  (* Write the data on the stdin of the created process *)
  let outch = Unix.out_channel_of_descr stdin_write in
  output_value outch vl;
  flush outch;
  (* Wait for its completion *)
  let status = waitpid_non_intr pid in
  finally
    (* Recover the result *)
      (fun () ->
      match status with
      | Unix.WEXITED 0 -> (
        let inch = Unix.in_channel_of_descr stdout_read in
        try Marshal.from_channel inch
        with (End_of_file | Failure _) as exn ->
          failwith
            (Printf.sprintf "command \"%s\" exited with code 0 but result could not be read back: %s"
               exe_path
               (Printexc.to_string exn)) )
      | Unix.WEXITED i ->
        failwith (Printf.sprintf "command \"%s\" exited %i" exe_path i)
      | Unix.WSIGNALED i ->
        failwith (Printf.sprintf "command \"%s\" killed %i" exe_path i)
      | Unix.WSTOPPED i ->
        failwith (Printf.sprintf "command \"%s\" stopped %i" exe_path i))
    (* Cleanup  *)
      (fun () ->
      List.iter
        (fun x -> try Unix.close x with Unix.Unix_error _ -> ())
        [ stdin_read
        ; stdin_write
        ; stdout_read
        ; stdout_write
        ; stderr_read
        ; stderr_write ])

(** Hashing utilities *)

module Hash = struct
  module Mc = Micromega
  open Hashset.Combine

  let int_of_eq_op1 =
    Mc.(function Equal -> 0 | NonEqual -> 1 | Strict -> 2 | NonStrict -> 3)

  let int_of_eq_op2 =
    Mc.(
      function
      | OpEq -> 0 | OpNEq -> 1 | OpLe -> 2 | OpGe -> 3 | OpLt -> 4 | OpGt -> 5)

  let eq_op1 o1 o2 = Int.equal (int_of_eq_op1 o1) (int_of_eq_op1 o2)
  let eq_op2 o1 o2 = Int.equal (int_of_eq_op2 o1) (int_of_eq_op2 o2)
  let hash_op1 h o = combine h (int_of_eq_op1 o)

  let rec eq_positive p1 p2 =
    match (p1, p2) with
    | Mc.XH, Mc.XH -> true
    | Mc.XI p1, Mc.XI p2 -> eq_positive p1 p2
    | Mc.XO p1, Mc.XO p2 -> eq_positive p1 p2
    | _, _ -> false

  let eq_z z1 z2 =
    match (z1, z2) with
    | Mc.Z0, Mc.Z0 -> true
    | Mc.Zpos p1, Mc.Zpos p2 | Mc.Zneg p1, Mc.Zneg p2 -> eq_positive p1 p2
    | _, _ -> false

  let eq_q {Mc.qnum = qn1; Mc.qden = qd1} {Mc.qnum = qn2; Mc.qden = qd2} =
    eq_z qn1 qn2 && eq_positive qd1 qd2

  let rec eq_pol eq p1 p2 =
    match (p1, p2) with
    | Mc.Pc c1, Mc.Pc c2 -> eq c1 c2
    | Mc.Pinj (i1, p1), Mc.Pinj (i2, p2) -> eq_positive i1 i2 && eq_pol eq p1 p2
    | Mc.PX (p1, i1, p1'), Mc.PX (p2, i2, p2') ->
      eq_pol eq p1 p2 && eq_positive i1 i2 && eq_pol eq p1' p2'
    | _, _ -> false

  let eq_pair eq1 eq2 (x1, y1) (x2, y2) = eq1 x1 x2 && eq2 y1 y2

  let hash_pol helt =
    let rec hash acc = function
      | Mc.Pc c -> helt (combine acc 1) c
      | Mc.Pinj (p, c) -> hash (combine (combine acc 1) (CoqToCaml.index p)) c
      | Mc.PX (p1, i, p2) ->
        hash (hash (combine (combine acc 2) (CoqToCaml.index i)) p1) p2
    in
    hash

  let hash_pair h1 h2 h (e1, e2) = h2 (h1 h e1) e2
  let hash_elt f h e = combine h (f e)
  let hash_string h (e : string) = hash_elt Hashtbl.hash h e
  let hash_z = hash_elt CoqToCaml.z
  let hash_q = hash_elt (fun q -> Hashtbl.hash (CoqToCaml.q_to_num q))
end

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
