(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Genarg
open Names
open Tac2expr
open Tac2env

(** Utils *)

let change_kn_label kn id =
  let (mp, dp, _) = KerName.repr kn in
  KerName.make mp dp (Label.of_id id)

let paren p = hov 2 (str "(" ++ p ++ str ")")

(** Type printing *)

type typ_level =
| T5_l
| T5_r
| T2
| T1
| T0

let pr_typref kn =
  Libnames.pr_qualid (Tac2env.shortest_qualid_of_type kn)

let rec pr_glbtype_gen pr lvl c =
  let rec pr_glbtype lvl = function
  | GTypVar n -> str "'" ++ str (pr n)
  | GTypRef (kn, []) -> pr_typref kn
  | GTypRef (kn, [t]) ->
    let paren = match lvl with
    | T5_r | T5_l | T2 | T1 -> fun x -> x
    | T0 -> paren
    in
    paren (pr_glbtype lvl t ++ spc () ++ pr_typref kn)
  | GTypRef (kn, tl) ->
    let paren = match lvl with
    | T5_r | T5_l | T2 | T1 -> fun x -> x
    | T0 -> paren
    in
    paren (str "(" ++ prlist_with_sep (fun () -> str ", ") (pr_glbtype lvl) tl ++ str ")" ++ spc () ++ pr_typref kn)
  | GTypArrow (t1, t2) ->
    let paren = match lvl with
    | T5_r -> fun x -> x
    | T5_l | T2 | T1 | T0 -> paren
    in
    paren (pr_glbtype T5_l t1 ++ spc () ++ str "->" ++ spc () ++ pr_glbtype T5_r t2)
  | GTypTuple tl ->
    let paren = match lvl with
    | T5_r | T5_l -> fun x -> x
    | T2 | T1 | T0 -> paren
    in
    paren (prlist_with_sep (fun () -> str " * ") (pr_glbtype T2) tl)
  in
  hov 0 (pr_glbtype lvl c)

let pr_glbtype pr c = pr_glbtype_gen pr T5_r c

let int_name () =
  let vars = ref Int.Map.empty in
  fun n ->
    if Int.Map.mem n !vars then Int.Map.find n !vars
    else
      let num = Int.Map.cardinal !vars in
      let base = num mod 26 in
      let rem = num / 26 in
      let name = String.make 1 (Char.chr (97 + base)) in
      let suff = if Int.equal rem 0 then "" else string_of_int rem in
      let name = name ^ suff in
      let () = vars := Int.Map.add n name !vars in
      name

(** Term printing *)

let pr_constructor kn =
  Libnames.pr_qualid (Tac2env.shortest_qualid_of_ltac (TacConstructor kn))

let pr_projection kn =
  Libnames.pr_qualid (Tac2env.shortest_qualid_of_projection kn)

type exp_level =
| E5
| E4
| E3
| E2
| E1
| E0

let pr_atom = function
| AtmInt n -> int n
| AtmStr s -> qstring s

let pr_name = function
| Name id -> Id.print id
| Anonymous -> str "_"

let find_constructor n empty def =
  let rec find n = function
  | [] -> assert false
  | (id, []) :: rem ->
    if empty then
      if Int.equal n 0 then id
      else find (pred n) rem
    else find n rem
  | (id, _ :: _) :: rem ->
    if not empty then
      if Int.equal n 0 then id
      else find (pred n) rem
    else find n rem
  in
  find n def

let order_branches cbr nbr def =
  let rec order cidx nidx def = match def with
  | [] -> []
  | (id, []) :: rem ->
    let ans = order (succ cidx) nidx rem in
    (id, [], cbr.(cidx)) :: ans
  | (id, _ :: _) :: rem ->
    let ans = order cidx (succ nidx) rem in
    let (vars, e) = nbr.(nidx) in
    (id, Array.to_list vars, e) :: ans
  in
  order 0 0 def

let pr_glbexpr_gen lvl c =
  let rec pr_glbexpr lvl = function
  | GTacAtm atm -> pr_atom atm
  | GTacVar id -> Id.print id
  | GTacRef gr ->
    let qid = shortest_qualid_of_ltac (TacConstant gr) in
    Libnames.pr_qualid qid
  | GTacFun (nas, c) ->
    let nas = pr_sequence pr_name nas in
    let paren = match lvl with
    | E0 | E1 | E2 | E3 | E4 -> paren
    | E5 -> fun x -> x
    in
    paren (str "fun" ++ spc () ++ nas ++ spc () ++ str "=>" ++ spc () ++
      hov 0 (pr_glbexpr E5 c))
  | GTacApp (c, cl) ->
    let paren = match lvl with
    | E0 -> paren
    | E1 | E2 | E3 | E4 | E5 -> fun x -> x
    in
    paren (pr_glbexpr E1 c) ++ spc () ++ (pr_sequence (pr_glbexpr E0) cl)
  | GTacLet (mut, bnd, e) ->
    let paren = match lvl with
    | E0 | E1 | E2 | E3 | E4 -> paren
    | E5 -> fun x -> x
    in
    let mut = if mut then str "rec" ++ spc () else mt () in
    let pr_bnd (na, e) =
      pr_name na ++ spc () ++ str ":=" ++ spc () ++ hov 2 (pr_glbexpr E5 e) ++ spc ()
    in
    let bnd = prlist_with_sep (fun () -> str "with" ++ spc ()) pr_bnd bnd in
    paren (str "let" ++ spc () ++ mut ++ bnd ++ str "in" ++ spc () ++ pr_glbexpr E5 e)
  | GTacCst (GCaseTuple _, _, cl) ->
    let paren = match lvl with
    | E0 | E1 -> paren
    | E2 | E3 | E4 | E5 -> fun x -> x
    in
    paren (prlist_with_sep (fun () -> str "," ++ spc ()) (pr_glbexpr E1) cl)
  | GTacArr cl ->
    mt () (** FIXME when implemented *)
  | GTacCst (GCaseAlg tpe, n, cl) ->
    begin match Tac2env.interp_type tpe with
    | _, GTydAlg def ->
      let paren = match lvl with
      | E0 -> paren
      | E1 | E2 | E3 | E4 | E5 -> fun x -> x
      in
      let id = find_constructor n (List.is_empty cl) def in
      let kn = change_kn_label tpe id in
      let cl = match cl with
      | [] -> mt ()
      | _ -> spc () ++ pr_sequence (pr_glbexpr E0) cl
      in
      paren (pr_constructor kn ++ cl)
    | _, GTydRec def ->
      let args = List.combine def cl in
      let pr_arg ((id, _, _), arg) =
        let kn = change_kn_label tpe id in
        pr_projection kn ++ spc () ++ str ":=" ++ spc () ++ pr_glbexpr E1 arg
      in
      let args = prlist_with_sep (fun () -> str ";" ++ spc ()) pr_arg args in
      str "{" ++ spc () ++ args ++ spc () ++ str "}"
    | _, GTydDef _ -> assert false
    end
  | GTacCse (e, info, cst_br, ncst_br) ->
    let e = pr_glbexpr E5 e in
    let br = match info with
    | GCaseAlg kn ->
      let def = match Tac2env.interp_type kn with
      | _, GTydAlg def -> def
      | _, GTydDef _ | _, GTydRec _ -> assert false
      in
      let br = order_branches cst_br ncst_br def in
      let pr_branch (cstr, vars, p) =
        let cstr = change_kn_label kn cstr in
        let cstr = pr_constructor cstr in
        let vars = match vars with
        | [] -> mt ()
        | _ -> spc () ++ pr_sequence pr_name vars
        in
        hov 0 (str "|" ++ spc () ++ cstr ++ vars ++ spc () ++ str "=>" ++ spc () ++
          hov 2 (pr_glbexpr E5 p)) ++ spc ()
      in
      prlist pr_branch br
    | GCaseTuple n ->
      let (vars, p) = ncst_br.(0) in
      let p = pr_glbexpr E5 p in
      let vars = prvect_with_sep (fun () -> str "," ++ spc ()) pr_name vars in
      str "|" ++ spc () ++ paren vars ++ spc () ++ str "=>" ++ spc () ++ p
    in
    hov 0 (hov 0 (str "match" ++ spc () ++ e ++ spc () ++ str "with") ++ spc () ++ Pp.v 0 br ++ str "end")
  | GTacPrj (kn, e, n) ->
    let def = match Tac2env.interp_type kn with
    | _, GTydRec def -> def
    | _, GTydDef _ | _, GTydAlg _ -> assert false
    in
    let (proj, _, _) = List.nth def n in
    let proj = change_kn_label kn proj in
    let proj = pr_projection proj in
    let e = pr_glbexpr E0 e in
    e ++ str "." ++ paren proj
  | GTacSet (kn, e, n, r) ->
    let def = match Tac2env.interp_type kn with
    | _, GTydRec def -> def
    | _, GTydDef _ | _, GTydAlg _ -> assert false
    in
    let (proj, _, _) = List.nth def n in
    let proj = change_kn_label kn proj in
    let proj = pr_projection proj in
    let e = pr_glbexpr E0 e in
    let r = pr_glbexpr E1 r in
    e ++ str "." ++ paren proj ++ spc () ++ str ":=" ++ spc () ++ r
  | GTacExt arg ->
    let GenArg (Glbwit tag, arg) = arg in
    let name = match tag with
    | ExtraArg tag -> ArgT.repr tag
    | _ -> assert false
    in
    str name ++ str ":" ++ paren (Genprint.glb_print tag arg)
  | GTacPrm (prm, args) ->
    let args = match args with
    | [] -> mt ()
    | _ -> spc () ++ pr_sequence (pr_glbexpr E0) args
    in
    str "@external" ++ spc () ++ qstring prm.mltac_plugin ++ spc () ++
      qstring prm.mltac_tactic ++ args
  in
  hov 0 (pr_glbexpr lvl c)

let pr_glbexpr c =
  pr_glbexpr_gen E5 c
