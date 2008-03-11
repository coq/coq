
open Format
open Util
open Pp
open Term
open Tacmach
open Tactics
open Tacticals
open Names
open Nameops
open Termops
open Coqlib
open Hipattern
open Libnames
open Declarations

(* 1. gappa syntax trees and output *)

module Constant = struct

  type t = { mantissa : int; base : int; exp : int }

  let create (b, m, e) =
    if b <> 2 && b <> 10 then invalid_arg "Constant.create";
    { mantissa = m; base = b; exp = e }

  let of_int x = 
    { mantissa = x; base = 1; exp = 0 }

  let mult x y =
    if x.base = 1 then { y with mantissa = x.mantissa * y.mantissa }
    else invalid_arg "Constant.mult"

  let print fmt x = match x.base with
    | 1 -> fprintf fmt "%d" x.mantissa
    | 2 -> fprintf fmt "%db%d" x.mantissa x.exp
    | 10 -> fprintf fmt "%de%d" x.mantissa x.exp
    | _ -> assert false

end

type binop = Bminus | Bplus | Bmult | Bdiv

type unop = Usqrt | Uabs | Uopp

type term =
  | Tconst of Constant.t
  | Tvar of string
  | Tbinop of binop * term * term
  | Tunop of unop * term

type pred =
  | Pin of term * Constant.t * Constant.t

let rec print_term fmt = function
  | Tconst c -> Constant.print fmt c
  | Tvar s -> pp_print_string fmt s
  | Tbinop (op, t1, t2) -> 
      let op = match op with 
	| Bplus -> "+" | Bminus -> "-" | Bmult -> "*" | Bdiv -> "/"
      in
      fprintf fmt "(%a %s %a)" print_term t1 op print_term t2
  | Tunop (Uabs, t) ->
      fprintf fmt "|%a|" print_term t
  | Tunop (Uopp | Usqrt as op, t) ->
      let s = match op with 
	| Uopp -> "-" | Usqrt -> "sqrt" | _ -> assert false 
      in
      fprintf fmt "(%s(%a))" s print_term t

let print_pred fmt = function
  | Pin (t, c1, c2) -> 
      fprintf fmt "%a in [%a, %a]" 
	print_term t Constant.print c1 Constant.print c2

let call_gappa hl p =
  let f = "test.gappa" in
  let c = open_out f in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[{ "; 
  List.iter (fun h -> fprintf fmt "%a ->@ " print_pred h) hl;
  fprintf fmt "%a }@]@." print_pred p;
  close_out c;
  let out = Sys.command (sprintf "gappa < %s" f) in
  msgnl (str ("gappa exit code is " ^ string_of_int out))

(* 2. coq -> gappa translation *)

exception NotGappa

let logic_dir = ["Coq";"Logic";"Decidable"]
let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "ZArith"; "BinInt"];
       ["Coq"; "Reals"; "Rdefinitions"]; 
       ["Coq"; "Reals"; "Raxioms";];
       ["Coq"; "Reals"; "Rbasic_fun";];
       ["Coq"; "Reals"; "R_sqrt";];
       ["Coq"; "Reals"; "Rfunctions";];
       ["Coq"; "dp"; "Gappa";];
    ]

let constant = gen_constant_in_modules "gappa" coq_modules

let coq_Rle = lazy (constant "Rle")
let coq_Rplus = lazy (constant "Rplus")
let coq_Rminus = lazy (constant "Rminus")
let coq_Rmult = lazy (constant "Rmult")
let coq_Rdiv = lazy (constant "Rdiv")
let coq_powerRZ = lazy (constant "powerRZ")
let coq_R1 = lazy (constant "R1")
let coq_Ropp = lazy (constant "Ropp")
let coq_Rabs = lazy (constant "Rabs")
let coq_sqrt = lazy (constant "sqrt")

let coq_F2R = lazy (constant "F2R")
let coq_Fzero = lazy (constant "Fzero")
let coq_Float = lazy (constant "Float")

let coq_true = lazy (constant "true")
let coq_false = lazy (constant "false")

let coq_Z0 = lazy (constant "Z0")
let coq_Zpos = lazy (constant "Zpos")
let coq_Zneg = lazy (constant "Zneg")
let coq_xH = lazy (constant "xH")
let coq_xI = lazy (constant "xI")
let coq_xO = lazy (constant "xO")
let coq_IZR = lazy (constant "IZR")

(* translates a closed Coq term p:positive into a FOL term of type int *)
let rec tr_positive p = match kind_of_term p with
  | Term.Construct _ when p = Lazy.force coq_xH ->
      1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xI ->
      2 * (tr_positive a) + 1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xO ->
      2 * (tr_positive a)
  | Term.Cast (p, _, _) ->
      tr_positive p
  | _ ->
      raise NotGappa

(* translates a closed Coq term t:Z into a term of type int *)
let rec tr_arith_constant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 ->
      0
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos ->
      tr_positive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg ->
      - (tr_positive a)
  | Term.Cast (t, _, _) ->
      tr_arith_constant t
  | _ -> 
      raise NotGappa

let decomp c = 
  let c, args = decompose_app c in
  kind_of_term c, args

let tr_bool c = match decompose_app c with
  | c, [] when c = Lazy.force coq_true -> true
  | c, [] when c = Lazy.force coq_false -> false
  | _ -> raise NotGappa

let tr_float c = match decompose_app c with
  | c, [] when c = Lazy.force coq_Fzero ->
      (2,0,0)
  | c, [b; s; m; e] when c = Lazy.force coq_Float ->
      let m = tr_positive m in
      let m' = if tr_bool s then - m else m in
      (tr_positive b, m', tr_arith_constant e)
  | _ ->
      raise NotGappa

let rec tr_term c0 = 
  let c, args = decompose_app c0 in
  match kind_of_term c, args with
    | Var id, [] ->
	Tvar (string_of_id id)
    | _, [a] when c = Lazy.force coq_F2R ->
	Tconst (Constant.create (tr_float a))
    | _, [a;b] when c = Lazy.force coq_Rplus ->
	Tbinop (Bplus, tr_term a, tr_term b)
    | _, [a;b] when c = Lazy.force coq_Rminus ->
	Tbinop (Bminus, tr_term a, tr_term b)
    | _, [a;b] when c = Lazy.force coq_Rmult ->
	Tbinop (Bmult, tr_term a, tr_term b)
    | _, [a;b] when c = Lazy.force coq_Rdiv ->
	Tbinop (Bmult, tr_term a, tr_term b)
    | _, [a] when c = Lazy.force coq_sqrt ->
	Tunop (Usqrt, tr_term a)
    | _, [a] when c = Lazy.force coq_Rabs ->
	Tunop (Uabs, tr_term a)
    | _, [a] when c = Lazy.force coq_Ropp ->
	Tunop (Uopp, tr_term a)
    | _ -> 
	msgnl (str "tr_term: " ++ Printer.pr_constr c0); raise NotGappa

let tr_rle c = 
  let c, args = decompose_app c in
  match kind_of_term c, args with
   | _, [a;b] when c = Lazy.force coq_Rle -> tr_term a, tr_term b
   | _ -> raise NotGappa

let tr_pred c =
  let c, args = decompose_app c in
  match kind_of_term c, args with
    | _, [a;b] when c = build_coq_and () ->
	begin match tr_rle a, tr_rle b with
	  | (Tconst c1, t1), (t2, Tconst c2) when t1 = t2 -> Pin (t1,c1,c2)
	  | _ -> raise NotGappa
	end
    | _ -> raise NotGappa

let tr_hyps =
  List.fold_left 
    (fun acc (_,h) -> try tr_pred h :: acc with NotGappa -> acc) []

let gappa gl =
  try
    let c = tr_pred (pf_concl gl) in
    call_gappa (tr_hyps (pf_hyps_types gl)) c;
    Tacticals.tclIDTAC gl
  with NotGappa ->
    error "not a gappa goal"
