
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
open Evarutil

(* 1. gappa syntax trees and output *)

module Constant = struct

  type t = { mantissa : int; base : int; exp : int }

  let create (b, m, e) =
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

let read_gappa_proof f =
  let buf = Buffer.create 1024 in
  Buffer.add_char buf '(';
  let cin = open_in f in
  let rec skip_space () =
    let c = input_char cin in if c = ' ' then skip_space () else c
  in
  while input_char cin <> '=' do () done;
  try
    while true do
      let c = skip_space () in
      if c = ':' then raise Exit;
      Buffer.add_char buf c;
      let s = input_line cin in
      Buffer.add_string buf s; 
      Buffer.add_char buf '\n';
    done;
    assert false
  with Exit ->
    Buffer.add_char buf ')';
    Buffer.contents buf

exception GappaFailed
exception GappaProofFailed

let call_gappa hl p =
  let gappa_in = "test.gappa" in
  let c = open_out gappa_in in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[{ "; 
  List.iter (fun h -> fprintf fmt "%a ->@ " print_pred h) hl;
  fprintf fmt "%a }@]@." print_pred p;
  close_out c;
  let gappa_out = "gappa.v" in
  let cmd = sprintf "gappa -Bcoq < %s > %s" gappa_in gappa_out in
  let out = Sys.command cmd in
  if out <> 0 then raise GappaFailed;
  let cmd = sprintf "sed -e '/^Lemma/ h ; s/Qed/Defined/ ; $ { p ; g ; s/Lemma \\([^ ]*\\).*/Eval compute in \\1./ }' -i %s" gappa_out
  in
  let _ = Sys.command cmd in
  let lambda = "test.lambda" in
  let cmd = 
    sprintf "%s/coqc %s > %s" Coq_config.bindir gappa_out lambda 
  in
  let out = Sys.command cmd in
  if out <> 0 then raise GappaProofFailed;
  read_gappa_proof lambda

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
       ["Gappa"; "Gappa_tactic";];
    ]

let constant = gen_constant_in_modules "gappa" coq_modules

let coq_Rle = lazy (constant "Rle")
let coq_R = lazy (constant "R")
(*
let coq_Rplus = lazy (constant "Rplus")
let coq_Rminus = lazy (constant "Rminus")
let coq_Rmult = lazy (constant "Rmult")
let coq_Rdiv = lazy (constant "Rdiv")
let coq_powerRZ = lazy (constant "powerRZ")
let coq_R1 = lazy (constant "R1")
let coq_Ropp = lazy (constant "Ropp")
let coq_Rabs = lazy (constant "Rabs")
let coq_sqrt = lazy (constant "sqrt")
*)

let coq_convert = lazy (constant "convert")
let coq_reUnknown = lazy (constant "reUnknown")
let coq_reFloat2 = lazy (constant "reFloat2")
let coq_reInteger = lazy (constant "reInteger")
let coq_reBinary = lazy (constant "reBinary")
let coq_reUnary = lazy (constant "reUnary")
let coq_boAdd = lazy (constant "boAdd")
let coq_boSub = lazy (constant "boSub")
let coq_boMul = lazy (constant "boMul")
let coq_boDiv = lazy (constant "boDiv")
let coq_uoAbs = lazy (constant "uoAbs")
let coq_uoNeg = lazy (constant "uoNeg")
let coq_uoSqrt = lazy (constant "uoSqrt")

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

let tr_float b m e =
  (b, tr_arith_constant m, tr_arith_constant e)

let tr_binop c = match decompose_app c with
  | c, [] when c = Lazy.force coq_boAdd -> Bplus
  | c, [] when c = Lazy.force coq_boSub -> Bminus
  | c, [] when c = Lazy.force coq_boMul -> Bmult
  | c, [] when c = Lazy.force coq_boDiv -> Bdiv
  | _ -> assert false

let tr_unop c = match decompose_app c with
  | c, [] when c = Lazy.force coq_uoNeg -> Uopp
  | c, [] when c = Lazy.force coq_uoSqrt -> Usqrt
  | c, [] when c = Lazy.force coq_uoAbs -> Uabs
  | _ -> raise NotGappa

let tr_var c = match decomp c with
  | Var x, [] -> string_of_id x
  | _ -> assert false

(* REexpr -> term *)
let rec tr_term c0 = 
  let c, args = decompose_app c0 in
  match kind_of_term c, args with
    | _, [a] when c = Lazy.force coq_reUnknown ->
	Tvar (tr_var a)
    | _, [a; b] when c = Lazy.force coq_reFloat2 ->
	Tconst (Constant.create (tr_float 2 a b))
    | _, [a] when c = Lazy.force coq_reInteger ->
	Tconst (Constant.create (1, tr_arith_constant a, 0))
    | _, [op;a;b] when c = Lazy.force coq_reBinary ->
	Tbinop (tr_binop op, tr_term a, tr_term b)
    | _, [op;a] when c = Lazy.force coq_reUnary ->
	Tunop (tr_unop op, tr_term a)
    | _ -> 
	msgnl (str "tr_term: " ++ Printer.pr_constr c0); 
	assert false

let tr_rle c = 
  let c, args = decompose_app c in
  match kind_of_term c, args with
    | _, [a;b] when c = Lazy.force coq_Rle ->  
	begin match decompose_app a, decompose_app b with
	  | (ac, [at]), (bc, [bt]) 
	    when ac = Lazy.force coq_convert && bc = Lazy.force coq_convert ->
	      at, bt
	  | _ ->
	      raise NotGappa
	end
    | _ -> 
	raise NotGappa

let tr_pred c =
  let c, args = decompose_app c in
  match kind_of_term c, args with
    | _, [a;b] when c = build_coq_and () ->
	begin match tr_rle a, tr_rle b with
	  | (c1, t1), (t2, c2) when t1 = t2 -> 
	      begin match tr_term c1, tr_term c2 with
		| Tconst c1, Tconst c2 ->
		    Pin (tr_term t1, c1, c2)
		| _ -> 
		    raise NotGappa
	      end
	  | _ -> 
	      raise NotGappa
	end
    | _ -> 
	raise NotGappa

let is_R c = match decompose_app c with
  | c, [] when c = Lazy.force coq_R -> true
  | _ -> false

let tr_hyps =
  List.fold_left 
    (fun acc (_,h) -> try tr_pred h :: acc with NotGappa -> acc) []

let constr_of_string gl s = 
  let parse_constr = Pcoq.parse_string Pcoq.Constr.constr in
  Constrintern.interp_constr (project gl) (pf_env gl) (parse_constr s)

let var_name = function
  | Name id -> 
      let s = string_of_id id in
      let s = String.sub s 1 (String.length s - 1) in
      mkVar (id_of_string s)
  | Anonymous -> 
      assert false

let build_proof_term c0 =
  let bl,c = decompose_lam c0 in
  List.fold_right 
    (fun (x,t) pf -> 
      mkApp (pf, [| if is_R t then var_name x else mk_new_meta () |]))
    bl c0

let gappa_internal gl =
  try
    let c = tr_pred (pf_concl gl) in
    let s = call_gappa (tr_hyps (pf_hyps_types gl)) c in
    msgnl (str s);
    let pf = constr_of_string gl s in
    let pf = build_proof_term pf in
    Tacticals.tclTHEN (Tactics.refine pf) Tactics.assumption gl
  with 
    | NotGappa -> error "not a gappa goal"
    | GappaFailed -> error "gappa failed"
    | GappaProofFailed -> error "incorrect gappa proof term"

(*
Local Variables: 
compile-command: "make -C ../.. bin/coqc.opt bin/coqide.opt contrib/dp/Gappa.vo"
End: 
*)

