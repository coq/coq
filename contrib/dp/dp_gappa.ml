
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

let debug = ref false

(* 1. gappa syntax trees and output *)

module Constant = struct

  open Bigint

  type t = { mantissa : bigint; base : int; exp : bigint }

  let create (b, m, e) =
    { mantissa = m; base = b; exp = e }

  let of_int x = 
    { mantissa = x; base = 1; exp = zero }

  let print fmt x = match x.base with
    | 1 -> fprintf fmt "%s" (to_string x.mantissa)
    | 2 -> fprintf fmt "%sb%s" (to_string x.mantissa) (to_string x.exp)
    | 10 -> fprintf fmt "%se%s" (to_string x.mantissa) (to_string x.exp)
    | _ -> assert false

end

type binop = Bminus | Bplus | Bmult | Bdiv

type unop = Usqrt | Uabs | Uopp

type rounding_mode = string

type term =
  | Tconst of Constant.t
  | Tvar of string
  | Tbinop of binop * term * term
  | Tunop of unop * term
  | Tround of rounding_mode * term

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
  | Tround (m, t) ->
      fprintf fmt "(%s(%a))" m print_term t

let print_pred fmt = function
  | Pin (t, c1, c2) -> 
      fprintf fmt "%a in [%a, %a]" 
	print_term t Constant.print c1 Constant.print c2

let temp_file f = if !debug then f else Filename.temp_file f ".v"
let remove_file f = if not !debug then try Sys.remove f with _ -> ()

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
    close_in cin;
    remove_file f;
    Buffer.add_char buf ')';
    Buffer.contents buf

exception GappaFailed
exception GappaProofFailed

let patch_gappa_proof fin fout =
  let cin = open_in fin in
  let cout = open_out fout in
  let fmt = formatter_of_out_channel cout in
  let last = ref "" in
  let defs = ref "" in
  try
    while true do
      let s = input_line cin in
      if s = "Qed." then
	fprintf fmt "Defined.@\n"
      else begin
	begin 
	  try Scanf.sscanf s "Lemma %s " 
	    (fun n -> defs := n ^ " " ^ !defs; last := n)
	  with Scanf.Scan_failure _ ->
	    try Scanf.sscanf s "Definition %s " 
	      (fun n -> defs := n ^ " " ^ !defs)
	    with Scanf.Scan_failure _ ->
	      ()
	end;
	fprintf fmt "%s@\n" s
      end
    done
  with End_of_file ->
    close_in cin;
    fprintf fmt "Definition proof := Eval cbv delta [%s] in %s.@." !defs !last;
    close_out cout
    
let call_gappa hl p =
  let gappa_in = temp_file "gappa_input" in
  let c = open_out gappa_in in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[{ "; 
  List.iter (fun h -> fprintf fmt "%a ->@ " print_pred h) hl;
  fprintf fmt "%a }@]@." print_pred p;
  close_out c;
  let gappa_out = temp_file "gappa_output" in
  let cmd = sprintf "gappa -Bcoq < %s > %s 2> /dev/null" gappa_in gappa_out in
  let out = Sys.command cmd in
  if out <> 0 then raise GappaFailed;
  remove_file gappa_in;
  let gappa_out2 = temp_file "gappa2" in
  patch_gappa_proof gappa_out gappa_out2;
  remove_file gappa_out;
  let cmd = (Filename.concat (Envars.coqbin ()) "coqc") ^ " " ^ gappa_out2 in
  let out = Sys.command cmd in
  if out <> 0 then raise GappaProofFailed;
  let gappa_out3 = temp_file "gappa3" in
  let c = open_out gappa_out3 in
  let gappa2 = Filename.chop_suffix (Filename.basename gappa_out2) ".v" in
  Printf.fprintf c 
    "Require \"%s\". Set Printing Depth 999999. Print %s.proof." 
    (Filename.chop_suffix gappa_out2 ".v") gappa2;
  close_out c;
  let lambda = temp_file "gappa_lambda" in
  let cmd = (Filename.concat (Envars.coqbin ()) "coqc") ^ " " ^ gappa_out3 ^ " > " ^ lambda in
  let out = Sys.command cmd in
  if out <> 0 then raise GappaProofFailed;
  remove_file gappa_out2; remove_file gappa_out3;
  remove_file (gappa_out2 ^ "o"); remove_file (gappa_out3 ^ "o");
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
       ["Gappa"; "Gappa_fixed";];
       ["Gappa"; "Gappa_float";];
       ["Gappa"; "Gappa_round_def";];
       ["Gappa"; "Gappa_pred_bnd";];  
       ["Gappa"; "Gappa_definitions";];
  ]

let constant = gen_constant_in_modules "gappa" coq_modules

let coq_refl_equal = lazy (constant "refl_equal")
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
let coq_reFloat10 = lazy (constant "reFloat10")
let coq_reInteger = lazy (constant "reInteger")
let coq_reBinary = lazy (constant "reBinary")
let coq_reUnary = lazy (constant "reUnary")
let coq_reRound = lazy (constant "reRound")
let coq_roundDN = lazy (constant "roundDN")
let coq_roundUP = lazy (constant "roundUP")
let coq_roundNE = lazy (constant "roundNE")
let coq_roundZR = lazy (constant "roundZR")
let coq_rounding_fixed = lazy (constant "rounding_fixed")
let coq_rounding_float = lazy (constant "rounding_float")
let coq_boAdd = lazy (constant "boAdd")
let coq_boSub = lazy (constant "boSub")
let coq_boMul = lazy (constant "boMul")
let coq_boDiv = lazy (constant "boDiv")
let coq_uoAbs = lazy (constant "uoAbs")
let coq_uoNeg = lazy (constant "uoNeg")
let coq_uoSqrt = lazy (constant "uoSqrt")
let coq_subset = lazy (constant "subset")
let coq_makepairF = lazy (constant "makepairF")

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
  | Term.Construct _ when t = Lazy.force coq_Z0 -> 0
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos -> tr_positive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg -> - (tr_positive a)
  | Term.Cast (t, _, _) -> tr_arith_constant t
  | _ -> raise NotGappa

(* translates a closed Coq term p:positive into a FOL term of type bigint *)
let rec tr_bigpositive p = match kind_of_term p with
  | Term.Construct _ when p = Lazy.force coq_xH -> 
      Bigint.one
  | Term.App (f, [|a|]) when f = Lazy.force coq_xI ->
      Bigint.add_1 (Bigint.mult_2 (tr_bigpositive a))
  | Term.App (f, [|a|]) when f = Lazy.force coq_xO ->
      (Bigint.mult_2 (tr_bigpositive a))
  | Term.Cast (p, _, _) ->
      tr_bigpositive p
  | _ ->
      raise NotGappa

(* translates a closed Coq term t:Z into a term of type bigint *)
let rec tr_arith_bigconstant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 -> Bigint.zero
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos -> tr_bigpositive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg -> 
      Bigint.neg (tr_bigpositive a)
  | Term.Cast (t, _, _) -> tr_arith_bigconstant t
  | _ -> raise NotGappa

let decomp c = 
  let c, args = decompose_app c in
  kind_of_term c, args

let tr_bool c = match decompose_app c with
  | c, [] when c = Lazy.force coq_true -> true
  | c, [] when c = Lazy.force coq_false -> false
  | _ -> raise NotGappa

let tr_float b m e =
  (b, tr_arith_bigconstant m, tr_arith_bigconstant e)

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

let tr_mode c = match decompose_app c with
  | c, [] when c = Lazy.force coq_roundDN -> "dn"
  | c, [] when c = Lazy.force coq_roundNE -> "ne"
  | c, [] when c = Lazy.force coq_roundUP -> "up"
  | c, [] when c = Lazy.force coq_roundZR -> "zr"
  | _ -> raise NotGappa

let tr_rounding_mode c = match decompose_app c with
  | c, [a;b] when c = Lazy.force coq_rounding_fixed ->
      let a = tr_mode a in
      let b = tr_arith_constant b in
      sprintf "fixed<%d,%s>" b a
  | c, [a;p;e] when c = Lazy.force coq_rounding_float ->
      let a = tr_mode a in
      let p = tr_positive p in
      let e = tr_arith_constant e in
      sprintf "float<%d,%d,%s>" p (-e) a
  | _ ->
      raise NotGappa

(* REexpr -> term *)
let rec tr_term c0 = 
  let c, args = decompose_app c0 in
  match kind_of_term c, args with
    | _, [a] when c = Lazy.force coq_reUnknown ->
	Tvar (tr_var a)
    | _, [a; b] when c = Lazy.force coq_reFloat2 ->
	Tconst (Constant.create (tr_float 2 a b))
    | _, [a; b] when c = Lazy.force coq_reFloat10 ->
	Tconst (Constant.create (tr_float 10 a b))
    | _, [a] when c = Lazy.force coq_reInteger ->
	Tconst (Constant.create (1, tr_arith_bigconstant a, Bigint.zero))
    | _, [op;a;b] when c = Lazy.force coq_reBinary ->
	Tbinop (tr_binop op, tr_term a, tr_term b)
    | _, [op;a] when c = Lazy.force coq_reUnary ->
	Tunop (tr_unop op, tr_term a)
    | _, [op;a] when c = Lazy.force coq_reRound ->
	Tround (tr_rounding_mode op, tr_term a)
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
    let pf = constr_of_string gl s in
    let pf = build_proof_term pf in
    Tacticals.tclTHEN (Tacmach.refine_no_check pf) Tactics.assumption gl
  with 
    | NotGappa -> error "not a gappa goal"
    | GappaFailed -> error "gappa failed"
    | GappaProofFailed -> error "incorrect gappa proof term"

let gappa_prepare =
  let id = Ident (dummy_loc, id_of_string "gappa_prepare") in
  lazy (Tacinterp.interp (Tacexpr.TacArg (Tacexpr.Reference id)))

let gappa gl =
  Coqlib.check_required_library ["Gappa"; "Gappa_tactic"];
  Tacticals.tclTHEN (Lazy.force gappa_prepare) gappa_internal gl

(*
Local Variables: 
compile-command: "make -C ../.. bin/coqc.opt bin/coqide.opt"
End: 
*)

