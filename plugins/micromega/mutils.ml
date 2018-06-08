(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

let rec pp_list f o l =
  match l with
    | [] -> ()
    | e::l -> f o e ; output_string o ";" ; pp_list f o l


let finally f rst =
  try
    let res = f () in
      rst () ; res
  with reraise ->
    (try rst ()
    with any -> raise reraise
    ); raise reraise

let rec try_any l x =
 match l with
  | [] -> None
  | (f,s)::l -> match f x with
     | None -> try_any l x
     | x -> x

let all_sym_pairs f l = 
  let pair_with acc e l = List.fold_left (fun acc x -> (f e x) ::acc) acc l in

  let rec xpairs acc l = 
    match l with
      | [] -> acc
      | e::l -> xpairs (pair_with acc e l) l in
    xpairs [] l

let all_pairs f l = 
  let pair_with acc e l = List.fold_left (fun acc x -> (f e x) ::acc) acc l in

  let rec xpairs acc l = 
    match l with
      | [] -> acc
      | e::lx -> xpairs (pair_with acc e l) lx in
    xpairs [] l

let rec is_sublist f l1 l2 =
  match l1 ,l2 with
    | [] ,_ -> true
    | e::l1', [] -> false
    | e::l1' , e'::l2' ->
	if f e e' then is_sublist f l1' l2'
	else is_sublist f l1 l2'

let extract pred l = 
  List.fold_left (fun (fd,sys) e -> 
		    match fd with
		    | None -> 
			begin
			  match pred e with
			  | None -> fd, e::sys
			  | Some v -> Some(v,e) , sys
			end
		    |  _   -> (fd, e::sys)
		 ) (None,[]) l

open Num
open Big_int

let ppcm x y =
 let g = gcd_big_int x y in
 let x' = div_big_int x g in
 let y' = div_big_int y g in
  mult_big_int g (mult_big_int x' y')

let denominator = function
 | Int _ | Big_int _ -> unit_big_int
 | Ratio r -> Ratio.denominator_ratio r

let numerator = function
 | Ratio r -> Ratio.numerator_ratio r
 | Int i -> Big_int.big_int_of_int i
 | Big_int i -> i

let rec ppcm_list c l =
 match l with
  | [] -> c
  | e::l -> ppcm_list (ppcm c (denominator e)) l

let rec rec_gcd_list c l  =
 match l with
  | [] -> c
  | e::l -> rec_gcd_list (gcd_big_int  c (numerator e)) l

let gcd_list l =
 let res = rec_gcd_list zero_big_int l in
  if Int.equal (compare_big_int res zero_big_int) 0
  then unit_big_int else res

let rats_to_ints l =
 let c = ppcm_list unit_big_int l in
  List.map (fun x ->  (div_big_int (mult_big_int (numerator x) c)
			(denominator x))) l

(* assoc_pos j [a0...an] = [j,a0....an,j+n],j+n+1 *)
(**
  * MODULE: Coq to Caml data-structure mappings
  *)

module CoqToCaml =
struct
 open Micromega

 let rec nat = function
  | O -> 0
  | S n -> (nat n) + 1


 let rec positive p =
  match p with
   | XH -> 1
   | XI p -> 1+ 2*(positive p)
   | XO p -> 2*(positive p)

 let n nt =
  match nt with
   | N0 -> 0
   | Npos p -> positive p

 let rec index i = (* Swap left-right ? *)
  match i with
   | XH -> 1
   | XI i -> 1+(2*(index i))
   | XO i -> 2*(index i)

 open Big_int

 let rec positive_big_int p =
  match p with
   | XH -> unit_big_int
   | XI p -> add_int_big_int 1 (mult_int_big_int 2 (positive_big_int p))
   | XO p -> (mult_int_big_int 2 (positive_big_int p))

 let z_big_int x =
  match x with
   | Z0 -> zero_big_int
   | Zpos p -> (positive_big_int p)
   | Zneg p -> minus_big_int (positive_big_int p)

 let q_to_num {qnum = x ; qden = y} =
  Big_int (z_big_int x) // (Big_int (z_big_int (Zpos y)))

end


(**
  * MODULE: Caml to Coq data-structure mappings
  *)

module CamlToCoq =
struct
 open Micromega

 let rec nat = function
  | 0 -> O
  | n -> S (nat (n-1))


 let rec positive n =
  if Int.equal n 1 then XH
  else if Int.equal (n land 1) 1 then XI (positive (n lsr 1))
  else  XO (positive (n lsr 1))

 let n nt =
  if nt < 0
  then assert false
  else if Int.equal nt 0 then N0
  else Npos (positive nt)

 let rec index  n =
  if Int.equal n 1 then XH
  else if Int.equal (n land 1) 1 then XI (index (n lsr 1))
  else  XO (index (n lsr 1))


 let z x =
  match compare x 0 with
   | 0 -> Z0
   | 1 -> Zpos (positive x)
   | _ -> (* this should be -1 *)
      Zneg (positive (-x))

 open Big_int

 let positive_big_int n =
  let two = big_int_of_int 2 in
  let rec _pos n =
   if eq_big_int n unit_big_int then XH
   else
    let (q,m) = quomod_big_int n two  in
     if eq_big_int unit_big_int m
     then XI (_pos q)
     else XO (_pos q) in
   _pos n

 let bigint x =
  match sign_big_int x with
   | 0 -> Z0
   | 1 -> Zpos (positive_big_int x)
   | _ -> Zneg (positive_big_int (minus_big_int x))

 let q n =
  {Micromega.qnum = bigint (numerator n) ;
   Micromega.qden = positive_big_int (denominator n)}

end

(**
  * MODULE: Comparisons on lists: by evaluating the elements in a single list,
  * between two lists given an ordering, and using a hash computation
  *)

module Cmp =
struct

 let rec compare_lexical l =
  match l with
   | [] -> 0 (* Equal *)
   | f::l ->
      let cmp = f () in
       if Int.equal cmp 0 then compare_lexical l else cmp

 let rec compare_list cmp l1 l2 =
  match l1 , l2 with
   | []  , [] -> 0
   | []  , _  -> -1
   | _   , [] -> 1
   | e1::l1 , e2::l2 ->
      let c = cmp e1 e2 in
       if Int.equal c 0 then compare_list cmp l1 l2 else c

end

(**
  * MODULE: Labels for atoms in propositional formulas. 
  * Tags are used to identify unused atoms in CNFs, and propagate them back to
  * the original formula. The translation back to Coq then ignores these
  * superfluous items, which speeds the translation up a bit.
  *)

module type Tag =
sig

  type t

  val from : int -> t
  val next : t -> t
  val pp : out_channel -> t -> unit
  val compare : t -> t -> int

end

module Tag : Tag =
struct

  type t = int

  let from i = i
  let next i = i + 1
  let pp o i = output_string o (string_of_int i)
  let compare : int -> int -> int = Int.compare

end

(**
  * MODULE: Ordered sets of tags.
  *)

module TagSet = Set.Make(Tag)

(** As for Unix.close_process, our Unix.waipid will ignore all EINTR *)

let rec waitpid_non_intr pid =
  try snd (Unix.waitpid [] pid)
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr pid

(**
  * Forking routine, plumbing the appropriate pipes where needed.
  *)

let command exe_path args vl =
  (* creating pipes for stdin, stdout, stderr *)
  let (stdin_read,stdin_write) = Unix.pipe ()
  and (stdout_read,stdout_write) = Unix.pipe ()
  and (stderr_read,stderr_write) = Unix.pipe () in

  (* Create the process *)
  let pid = Unix.create_process exe_path args stdin_read stdout_write stderr_write in

  (* Write the data on the stdin of the created process *)
  let outch = Unix.out_channel_of_descr stdin_write in
    output_value outch vl ;
    flush outch ;

  (* Wait for its completion *)
    let status = waitpid_non_intr pid in

      finally
        (* Recover the result *)
	(fun () ->
	  match status with
	    | Unix.WEXITED 0 ->
		let inch = Unix.in_channel_of_descr stdout_read in
		begin
                  try Marshal.from_channel inch
                  with any ->
                    failwith
                      (Printf.sprintf "command \"%s\" exited %s" exe_path
                         (Printexc.to_string any))
                end
	    | Unix.WEXITED i   ->
                failwith (Printf.sprintf "command \"%s\" exited %i" exe_path i)
	    | Unix.WSIGNALED i ->
                failwith (Printf.sprintf "command \"%s\" killed %i" exe_path i)
	    | Unix.WSTOPPED i  ->
                failwith (Printf.sprintf "command \"%s\" stopped %i" exe_path i))
        (* Cleanup  *)
	(fun () ->
	  List.iter (fun x -> try Unix.close x with any -> ())
            [stdin_read; stdin_write;
             stdout_read; stdout_write;
             stderr_read; stderr_write])

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
