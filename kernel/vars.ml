(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Esubst
open Context

(*********************)
(*     Occurring     *)
(*********************)

exception LocalOccur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn n c =
  let rec closed_rec n c = match Constr.kind c with
    | Constr.Rel m -> if m>n then raise LocalOccur
    | _ -> Constr.iter_with_binders succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)

let closed0 = closedn 0

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term =
  let rec occur_rec n c = match Constr.kind c with
    | Constr.Rel m -> if Int.equal m n then raise LocalOccur
    | _ -> Constr.iter_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M
  for n <= p < n+m *)

let noccur_between n m term =
  let rec occur_rec n c = match Constr.kind c with
    | Constr.Rel p -> if n<=p && p<n+m then raise LocalOccur
    | _        -> Constr.iter_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* Checking function for terms containing existential variables.
 The function [noccur_with_meta] considers the fact that
 each existential variable (as well as each isevar)
 in the term appears applied to its local context,
 which may contain the CoFix variables. These occurrences of CoFix variables
 are not considered *)

let isMeta c = match Constr.kind c with
| Constr.Meta _ -> true
| _ -> false

let noccur_with_meta n m term =
  let rec occur_rec n c = match Constr.kind c with
    | Constr.Rel p -> if n<=p && p<n+m then raise LocalOccur
    | Constr.App(f,cl) ->
        (match Constr.kind f with
           | Constr.Cast (c,_,_) when isMeta c -> ()
           | Constr.Meta _ -> ()
           | _ -> Constr.iter_with_binders succ occur_rec n c)
    | Constr.Evar (_, _) -> ()
    | _ -> Constr.iter_with_binders succ occur_rec n c
  in
  try (occur_rec n term; true) with LocalOccur -> false

(*********************)
(*      Lifting      *)
(*********************)

(* The generic lifting function *)
let rec exliftn el c = match Constr.kind c with
  | Constr.Rel i -> Constr.mkRel(reloc_rel i el)
  | _ -> Constr.map_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn n k =
  match el_liftn (pred k) (el_shft n el_id) with
    | ELID -> (fun c -> c)
    | el -> exliftn el

let lift n = liftn n 1

(*********************)
(*   Substituting    *)
(*********************)

(* (subst1 M c) substitutes M for Rel(1) in c
   we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
   M1,...,Mn for respectively Rel(1),...,Rel(n) in c *)

(* 1st : general case *)

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo: info; sit: 'a }

let rec lift_substituend depth s =
  match s.sinfo with
    | Closed -> s.sit
    | Open -> lift depth s.sit
    | Unknown ->
        s.sinfo <- if closed0 s.sit then Closed else Open;
        lift_substituend depth s

let make_substituend c = { sinfo=Unknown; sit=c }

let substn_many lamv n c =
  let lv = Array.length lamv in
  if Int.equal lv 0 then c
  else
    let rec substrec depth c = match Constr.kind c with
      | Constr.Rel k     ->
          if k<=depth then c
          else if k-depth <= lv then lift_substituend depth lamv.(k-depth-1)
          else Constr.mkRel (k-lv)
      | _ -> Constr.map_with_binders succ substrec depth c in
    substrec n c

(*
let substkey = Profile.declare_profile "substn_many";;
let substn_many lamv n c = Profile.profile3 substkey substn_many lamv n c;;
*)

let make_subst = function
| [] -> [||]
| hd :: tl ->
  let subst = Array.make (1 + List.length tl) (make_substituend hd) in
  let iteri i x = Array.unsafe_set subst (succ i) (make_substituend x) in
  let () = CList.iteri iteri tl in
  subst

let substnl laml n = substn_many (make_subst laml) n
let substl laml = substnl laml 0
let subst1 lam = substl [lam]

let substnl_decl laml k = map_rel_declaration (substnl laml k)
let substl_decl laml = substnl_decl laml 0
let subst1_decl lam = substl_decl [lam]

let substnl_named_decl laml k = map_named_declaration (substnl laml k)
let substl_named_decl laml = substnl_named_decl laml 0
let subst1_named_decl lam = substl_named_decl [lam]

(* (thin_val sigma) removes identity substitutions from sigma *)

let rec thin_val = function
  | [] -> []
  | (id, c) :: tl ->
    match Constr.kind c with
    | Constr.Var v ->
      if Id.equal id v then thin_val tl
      else (id, make_substituend c) :: (thin_val tl)
    | _ -> (id, make_substituend c) :: (thin_val tl)

let rec find_var id = function
| [] -> raise Not_found
| (idc, c) :: subst ->
  if Id.equal id idc then c
  else find_var id subst

(* (replace_vars sigma M) applies substitution sigma to term M *)
let replace_vars var_alist =
  let var_alist = thin_val var_alist in
  let rec substrec n c = match Constr.kind c with
    | Constr.Var x ->
        (try lift_substituend n (find_var x var_alist)
         with Not_found -> c)
    | _ -> Constr.map_with_binders succ substrec n c
  in
  match var_alist with
  | [] -> (function x -> x)
  | _ -> substrec 0

(*
let repvarkey = Profile.declare_profile "replace_vars";;
let replace_vars vl c = Profile.profile2 repvarkey replace_vars vl c ;;
*)

(* (subst_var str t) substitute (VAR str) by (Rel 1) in t *)
let subst_var str = replace_vars [(str, Constr.mkRel 1)]

(* (subst_vars [id1;...;idn] t) substitute (VAR idj) by (Rel j) in t *)
let substn_vars p vars =
  let _,subst =
    List.fold_left (fun (n,l) var -> ((n+1),(var,Constr.mkRel n)::l)) (p,[]) vars
  in replace_vars (List.rev subst)

let subst_vars = substn_vars 1
