(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** An equation is of the following form a1.x1 + a2.x2 = c
*)

type var = int
type id  = int

module Itv =
struct
  let debug = false

  type t = int * int (* We only consider closed intervals *)

  exception Empty

  let output o (lb,ub) =
    Printf.fprintf o "[%i,%i]" lb ub

  let wf o (lb,ub) =
    if lb <= ub then ()
    else Printf.fprintf o "error %a\n" output (lb,ub)

  (** [mul_cst c (lb,ub)] requires c > 0 *)
  let mul_cst c (lb,ub) = (c * lb, c * ub)

  (** [opp (lb,ub)] is multplication by -1 *)
  let opp (lb,ub) = (-ub,-lb)

  let opp i1  =
    let i = opp i1 in
    if debug then Printf.printf  "opp %a -> %a\n" output i1  output i;
      i

  (** [div (lb,ub) c] requires c > 0, lb >= 0 *)
  let div (lb,ub) c =
    let lb = lb /c + (if lb  mod c = 0 then 0 else 1) in
    let ub = ub / c in
    if lb <= ub then (lb,ub) else raise Empty

  let div i c =
    try let r = div i c in
      if debug then Printf.printf  "%a div %i -> %a\n" output i c output r;
    r
    with Empty ->
      if debug then Printf.printf  "%a div %i -> Empty \n" output i c;
      raise Empty

  let add (lb1,ub1) (lb2,ub2) =
    (lb1+lb2,ub1+ub2)

  let add i1 i2 =
      let i = add i1 i2 in
      if debug then Printf.printf  "%a add %a -> %a\n" output i1 output i2 output i;
      i

  let inter : t -> t -> t =
    fun (lb1,ub1) (lb2,ub2) ->
    let ub = max lb1 lb2 in
    let lb = min ub1 ub2 in
    if ub <= lb
    then (ub,lb)
    else raise Empty

  let inter i1 i2 =
    try
      let i = inter i1 i2 in
      if debug then Printf.printf  "%a inter %a -> %a\n" output i1 output i2 output i;
      i
    with Empty ->
      if debug then Printf.printf  "%a inter %a -> Empty\n" output i1 output i2 ;
      raise Empty

  (* [enum (lb,ub)] is only defined for finite intervals *)
  let enum (lb,ub) =
    match Int.compare lb ub with
    | 0 -> (lb,None)
    | _ -> (lb,Some (lb+1,ub))

  let range (lb,ub) = ub - lb + 1

  let top = (min_int,max_int)

  let lt i1 i2 =
    range i1 < range i2

end

module ItvMap =
struct

  module M = Map.Make(Int)

  include M

  let refine_with v i m =
    try
      let i0 = M.find v m in
      let i' = Itv.inter i i0 in
      (Itv.lt i' i0,i',M.add v i' m)
    with Not_found ->
      (true, i, M.add v i m)

  let pick m =
    let (x,i,r) =
      fold (fun v i (v',i',r') ->
          let r = Itv.range i in
          if r < r' then (v,i,r) else (v',i',r')) m (min_int,Itv.top,max_int) in
    if x = min_int then raise Not_found else (x,i)

  let output o m =
    Printf.fprintf o "[";
    iter (fun k (lb,ub) -> Printf.fprintf o "x%i -> [%i,%i] " k lb ub) m;
    Printf.fprintf o "]";


end

exception Unsat

module Eqn =
struct
  type t   = (var * int) list * int

  let empty = ([],0)

  let rec output_lin o l =
    match l with
    | [] -> Printf.fprintf o "0"
    | [x,v] -> Printf.fprintf o "%i.x%i" v x
    | (x,v)::l' -> Printf.fprintf o "%i.x%i + %a" v x output_lin l'

  let normalise (l,c) =
    match l with
    | [] -> if c = 0 then None else raise Unsat
    | _  -> Some(l,c)


  let rec no_dup l =
    match l with
    | [] -> true
    | (x,v)::l -> try
        let _ = List.assoc x l in
        false
      with Not_found -> no_dup l


  let add (l1,c1) (l2,c2) =
    (l1@l2,c1+c2)

  let add e1 e2 =
    let r = add e1 e2 in
    if no_dup (fst r) then ()
    else Printf.printf "add(duplicate)%a %a" output_lin (fst e1) output_lin (fst e2) ;
    r


  let itv_of_ax m (var,coe) =
    Itv.mul_cst coe (ItvMap.find var m)

  let itv_list m l =
    List.fold_left (fun i (var,coe) ->
        Itv.add i (itv_of_ax m (var,coe))) (0,0) l

  let get_remove x l =
    let l' = List.remove_assoc x l in
    let c  = try List.assoc x l with Not_found -> 0 in
    (c,l')



end
type eqn = Eqn.t

open Eqn

let debug = false

(** Given an equation a1.x1 + ... an.xn = c,
    bound all the variables xi in [0; c/ai] *)

let init_bound m (v,c) =
  match v with
  | [] -> if c = 0 then m else raise Unsat
  | [x,v] -> let (_,_,m) = ItvMap.refine_with x (Itv.div (c,c) v) m in m
  |   _   ->
    List.fold_left (fun m (var,coe)  ->
        let (_,_,m) = ItvMap.refine_with var (0,c / coe) m in
        m)  m v

let init_bounds sys =
  List.fold_left init_bound ItvMap.empty sys

let init_bounds sys =
  let m = init_bounds sys in
  if debug then Printf.printf "init_bound : %a\n" ItvMap.output m;
  m


(* [refine_bound p m acc (v,c)]
    improves the bounds of the equation v + acc = c
*)


let rec refine_bound p m acc (v,c) =
  Itv.wf stdout acc;
  match v with
  | [] -> (m,p)
  | (var,coe)::v' ->
    if debug then Printf.printf "Refining %i.x%i + %a + %a = %i\n" coe var
      Itv.output acc output_lin v' c;
    let itv_acc_l = Itv.inter (0,c) (Itv.add acc (itv_list m v')) in
    let itv_coe_var =  Itv.add (c,c) (Itv.opp itv_acc_l) in
    let i      =  Itv.div itv_coe_var coe in
    let (b,i',m) = ItvMap.refine_with var i m in
    refine_bound (p || b)
      m (Itv.add (Itv.mul_cst coe i') acc) (v',c)

let refine_bounds p m l =
  List.fold_left (fun (m,p) eqn ->
      refine_bound p m (0,0) eqn) (m,p) l

let refine_until_fix m l =
  let rec iter_refine m =
    let (m',b) = refine_bounds false m l in
    if b then iter_refine m' else m' in
  iter_refine m




let subst x a l =

  let subst_eqn acc (v,c) =
    let (coe,v') = Eqn.get_remove x v in
    let (v',c') = (v', c - coe * a) in
    match v' with
    | [] -> if c' = 0 then acc
      else raise Unsat
    | _ -> (v',c')::acc in

  List.fold_left subst_eqn [] l

let output_list elt o l =
  Printf.fprintf o "[";
  List.iter (fun e -> Printf.fprintf o "%a; " elt e) l;
  Printf.fprintf o "]"

let output_equations o l =
    let output_equation o (l,c) =
        Printf.fprintf o "%a = %i" output_lin l c in
    output_list output_equation o l

let output_intervals o m =
  ItvMap.iter (fun k v -> Printf.fprintf o "x%i:%a " k Itv.output v) m


type solution = (var * int) list

let solve_system l =

  let rec solve m l =
    if debug then Printf.printf "Solve %a\n" output_equations l;

    match l with
    | [] -> [m] (* we have a solution *)
    | _  ->
      try
        let m' = refine_until_fix m l in
        try
        if debug then Printf.printf "Refined %a\n" ItvMap.output m' ;
        let (k,i) = ItvMap.pick m' in
        let (v,itv') = Itv.enum i in
        (* We recursively solve using k = v *)
        let sol1 =
          List.map (ItvMap.add k (v,v))
            (solve (ItvMap.remove k m) (subst k v l)) in
        let sol2 =
          match itv' with
          | None -> []
          | Some itv' ->
            (* We recursively solve with a smaller interval *)
            solve (ItvMap.add k itv' m) l in
        sol1 @ sol2
        with    | Not_found -> Printf.printf "NOT FOUND %a %a\n" output_equations l output_intervals m'; raise Not_found
      with (Unsat | Itv.Empty) as e ->
        begin
          if debug then Printf.printf "Unsat detected %s\n" (Printexc.to_string e);
          [] end
  in

  try
    let l = CList.map_filter Eqn.normalise l in
    solve (init_bounds l) l
  with Itv.Empty | Unsat -> []



let enum_sol m =
  let rec augment_sols x (lb,ub) s =
    let slb = if lb = 0 then s
      else List.rev_map (fun s -> (x,lb)::s) s in
    if lb = ub then slb
    else let sl = augment_sols x (lb+1,ub) s in
      List.rev_append slb sl in

  ItvMap.fold augment_sols m [[]]

let enum_sols l =
  List.fold_left (fun s m -> List.rev_append (enum_sol m) s) [] l


let solve_and_enum l = enum_sols (solve_system l)


let output_solution o s =
  let output_var_coef o (x,v) =
    Printf.fprintf o "x%i:%i" x v in
  output_list output_var_coef o s ;
  Printf.fprintf o "\n"

let output_solutions o l = output_list output_solution o l

(** Incremental construction of systems of equations *)
open Mutils

type system = Eqn.t IMap.t

let empty : system = IMap.empty

let set_constant (idx:int) (c:int) (s:system) : Eqn.t =
  let e = try IMap.find idx s with
    |Not_found -> Eqn.empty in
  (fst e,c)

let make_mon (idx:int) (v:var) (c:int) (s:system) : system  =
  IMap.add idx ([v,c],0) s

let merge (s1:system) (s2:system) : system =
  IMap.merge (fun k e1 e2 ->
      match e1 , e2 with
      | None , None -> None
      | None , Some e | Some e , None -> Some e
      | Some e1, Some e2 -> Some (Eqn.add e1 e2)) s1 s2
