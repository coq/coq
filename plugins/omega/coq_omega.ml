(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(**************************************************************************)
(*                                                                        *)
(* Omega: a solver of quantifier-free problems in Presburger Arithmetic   *)
(*                                                                        *)
(* Pierre Crégut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

open CErrors
open Util
open Names
open Constr
open Nameops
open EConstr
open Tacticals.New
open Tacmach.New
open Tactics
open Logic
open Libnames
open Globnames
open Nametab
open Contradiction
open Tactypes
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration
module OmegaSolver = Omega.MakeOmegaSolver (Bigint)
open OmegaSolver

(* Added by JCF, 09/03/98 *)

let elim_id id = simplest_elim (mkVar id)

let resolve_id id = apply (mkVar id)

let display_time_flag = ref false
let display_system_flag = ref false
let display_action_flag = ref false
let old_style_flag = ref false
let letin_flag = ref true

(* Should we reset all variable labels between two runs of omega ? *)

let reset_flag = ref true

(* Coq < 8.5 was not performing such resets, hence omega was slightly
   non-deterministic: successive runs of omega on the same problem may
   lead to distinct proof-terms.
   At the very least, these terms differed on the inner
   variable names, but they could even be non-convertible :
   the OmegaSolver relies on Hashtbl.iter, it can hence find a different
   solution when variable indices differ. *)

let read f () = !f
let write f x = f:=x

open Goptions

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "Omega system time displaying flag";
      optkey   = ["Omega";"System"];
      optread  = read display_system_flag;
      optwrite = write display_system_flag }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "Omega action display flag";
      optkey   = ["Omega";"Action"];
      optread  = read display_action_flag;
      optwrite = write display_action_flag }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "Omega old style flag";
      optkey   = ["Omega";"OldStyle"];
      optread  = read old_style_flag;
      optwrite = write old_style_flag }

let _ =
  declare_bool_option
    { optdepr  = true;
      optname  = "Omega automatic reset of generated names";
      optkey   = ["Stable";"Omega"];
      optread  = read reset_flag;
      optwrite = write reset_flag }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "Omega takes advantage of context variables with body";
      optkey   = ["Omega";"UseLocalDefs"];
      optread  = read letin_flag;
      optwrite = write letin_flag }

let intref, reset_all_references =
  let refs = ref [] in
  (fun n -> let r = ref n in refs := (r,n) :: !refs; r),
  (fun () -> List.iter (fun (r,n) -> r:=n) !refs)

let new_identifier =
  let cpt = intref 0 in
  (fun () -> let s = "Omega" ^ string_of_int !cpt in incr cpt; Id.of_string s)

let new_identifier_state =
  let cpt = intref 0 in
  (fun () -> let s = make_ident "State" (Some !cpt) in incr cpt; s)

let new_identifier_var =
  let cpt = intref 0 in
  (fun () -> let s = "Zvar" ^ string_of_int !cpt in incr cpt; Id.of_string s)

let new_id =
  let cpt = intref 0 in fun () -> incr cpt; !cpt

let new_var_num =
  let cpt = intref 1000 in (fun () -> incr cpt; !cpt)

let new_var =
  let cpt = intref 0 in fun () -> incr cpt; Nameops.make_ident "WW" (Some !cpt)

let display_var i = Printf.sprintf "X%d" i

let intern_id,unintern_id,reset_intern_tables =
  let cpt = ref 0 in
  let table = Hashtbl.create 7 and co_table = Hashtbl.create 7 in
  (fun (name : Id.t) ->
     try Hashtbl.find table name with Not_found ->
       let idx = !cpt in
       Hashtbl.add table name idx;
       Hashtbl.add co_table idx name;
       incr cpt; idx),
  (fun idx ->
     try Hashtbl.find co_table idx with Not_found ->
       let v = new_var () in
       Hashtbl.add table v idx; Hashtbl.add co_table idx v; v),
  (fun () -> cpt := 0; Hashtbl.clear table)

let mk_then tacs = tclTHENLIST tacs

let exists_tac c = constructor_tac false (Some 1) 1 (ImplicitBindings [c])

let generalize_tac t = generalize t
let elim t = simplest_elim t
let unfold s = Tactics.unfold_in_concl [Locus.AllOccurrences, Lazy.force s]
let pf_nf gl c = pf_apply Tacred.simpl gl c

let rev_assoc k =
  let rec loop = function
    | [] -> raise Not_found
    | (v,k')::_ when Int.equal k k' -> v
    | _ :: l -> loop l
  in
  loop

let tag_hypothesis,tag_of_hyp, hyp_of_tag, clear_tags =
  let l = ref ([]:(Id.t * int) list) in
  (fun h id -> l := (h,id):: !l),
  (fun h -> try Id.List.assoc h !l with Not_found -> failwith "tag_hypothesis"),
  (fun h -> try rev_assoc h !l with Not_found -> failwith "tag_hypothesis"),
  (fun () -> l := [])

let hide_constr,find_constr,clear_constr_tables,dump_tables =
  let l = ref ([]:(constr * (Id.t * Id.t * bool)) list) in
  (fun h id eg b -> l := (h,(id,eg,b)):: !l),
  (fun sigma h ->
    try List.assoc_f (eq_constr_nounivs sigma) h !l with Not_found -> failwith "find_contr"),
  (fun () -> l := []),
  (fun () -> !l)

let reset_all () =
  if !reset_flag then begin
    reset_all_references ();
    reset_intern_tables ();
    clear_tags ();
    clear_constr_tables ()
  end

(* Lazy evaluation is used for Coq constants, because this code
 is evaluated before the compiled modules are loaded.
 To use the constant Zplus, one must type "Lazy.force coq_Zplus"
 This is the right way to access to Coq constants in tactics ML code *)

open Coqlib

let logic_dir = ["Coq";"Logic";"Decidable"]
let coq_modules =
  init_modules @arith_modules @ [logic_dir] @ zarith_base_modules
    @ [["Coq"; "omega"; "OmegaLemmas"]]

let gen_constant_in_modules n m s = EConstr.of_constr (UnivGen.constr_of_global @@ gen_reference_in_modules n m s)
let init_constant = gen_constant_in_modules "Omega" init_modules
let constant = gen_constant_in_modules "Omega" coq_modules

let z_constant = gen_constant_in_modules "Omega" [["Coq";"ZArith"]]
let zbase_constant =
  gen_constant_in_modules "Omega" [["Coq";"ZArith";"BinInt"]]


(* Zarith *)
let coq_xH = lazy (constant "xH")
let coq_xO = lazy (constant "xO")
let coq_xI = lazy (constant "xI")
let coq_Z0 = lazy (constant "Z0")
let coq_Zpos = lazy (constant "Zpos")
let coq_Zneg = lazy (constant "Zneg")
let coq_Z = lazy (constant "Z")
let coq_comparison = lazy (constant "comparison")
let coq_Gt = lazy (constant "Gt")
let coq_Zplus = lazy (zbase_constant "Z.add")
let coq_Zmult = lazy (zbase_constant "Z.mul")
let coq_Zopp = lazy (zbase_constant "Z.opp")
let coq_Zminus = lazy (zbase_constant "Z.sub")
let coq_Zsucc = lazy (zbase_constant "Z.succ")
let coq_Zpred = lazy (zbase_constant "Z.pred")
let coq_Z_of_nat = lazy (zbase_constant "Z.of_nat")
let coq_inj_plus = lazy (z_constant "Nat2Z.inj_add")
let coq_inj_mult = lazy (z_constant "Nat2Z.inj_mul")
let coq_inj_minus1 = lazy (z_constant "Nat2Z.inj_sub")
let coq_inj_minus2 = lazy (constant "inj_minus2")
let coq_inj_S = lazy (z_constant "Nat2Z.inj_succ")
let coq_inj_le = lazy (z_constant "Znat.inj_le")
let coq_inj_lt = lazy (z_constant "Znat.inj_lt")
let coq_inj_ge = lazy (z_constant "Znat.inj_ge")
let coq_inj_gt = lazy (z_constant "Znat.inj_gt")
let coq_inj_neq = lazy (z_constant "inj_neq")
let coq_inj_eq = lazy (z_constant "inj_eq")
let coq_fast_Zplus_assoc_reverse = lazy (constant "fast_Zplus_assoc_reverse")
let coq_fast_Zplus_assoc = lazy (constant "fast_Zplus_assoc")
let coq_fast_Zmult_assoc_reverse = lazy (constant "fast_Zmult_assoc_reverse")
let coq_fast_Zplus_permute = lazy (constant "fast_Zplus_permute")
let coq_fast_Zplus_comm = lazy (constant "fast_Zplus_comm")
let coq_fast_Zmult_comm = lazy (constant "fast_Zmult_comm")
let coq_Zmult_le_approx = lazy (constant "Zmult_le_approx")
let coq_OMEGA1 = lazy (constant "OMEGA1")
let coq_OMEGA2 = lazy (constant "OMEGA2")
let coq_OMEGA3 = lazy (constant "OMEGA3")
let coq_OMEGA4 = lazy (constant "OMEGA4")
let coq_OMEGA5 = lazy (constant "OMEGA5")
let coq_OMEGA6 = lazy (constant "OMEGA6")
let coq_OMEGA7 = lazy (constant "OMEGA7")
let coq_OMEGA8 = lazy (constant "OMEGA8")
let coq_OMEGA9 = lazy (constant "OMEGA9")
let coq_fast_OMEGA10 = lazy (constant "fast_OMEGA10")
let coq_fast_OMEGA11 = lazy (constant "fast_OMEGA11")
let coq_fast_OMEGA12 = lazy (constant "fast_OMEGA12")
let coq_fast_OMEGA13 = lazy (constant "fast_OMEGA13")
let coq_fast_OMEGA14 = lazy (constant "fast_OMEGA14")
let coq_fast_OMEGA15 = lazy (constant "fast_OMEGA15")
let coq_fast_OMEGA16 = lazy (constant "fast_OMEGA16")
let coq_OMEGA17 = lazy (constant "OMEGA17")
let coq_OMEGA18 = lazy (constant "OMEGA18")
let coq_OMEGA19 = lazy (constant "OMEGA19")
let coq_OMEGA20 = lazy (constant "OMEGA20")
let coq_fast_Zred_factor0 = lazy (constant "fast_Zred_factor0")
let coq_fast_Zred_factor1 = lazy (constant "fast_Zred_factor1")
let coq_fast_Zred_factor2 = lazy (constant "fast_Zred_factor2")
let coq_fast_Zred_factor3 = lazy (constant "fast_Zred_factor3")
let coq_fast_Zred_factor4 = lazy (constant "fast_Zred_factor4")
let coq_fast_Zred_factor5 = lazy (constant "fast_Zred_factor5")
let coq_fast_Zred_factor6 = lazy (constant "fast_Zred_factor6")
let coq_fast_Zmult_plus_distr_l = lazy (constant "fast_Zmult_plus_distr_l")
let coq_fast_Zmult_opp_comm =  lazy (constant "fast_Zmult_opp_comm")
let coq_fast_Zopp_plus_distr =   lazy (constant "fast_Zopp_plus_distr")
let coq_fast_Zopp_mult_distr_r = lazy (constant "fast_Zopp_mult_distr_r")
let coq_fast_Zopp_eq_mult_neg_1 =  lazy (constant "fast_Zopp_eq_mult_neg_1")
let coq_fast_Zopp_involutive = lazy (constant "fast_Zopp_involutive")
let coq_Zegal_left = lazy (constant "Zegal_left")
let coq_Zne_left = lazy (constant "Zne_left")
let coq_Zlt_left = lazy (constant "Zlt_left")
let coq_Zge_left = lazy (constant "Zge_left")
let coq_Zgt_left = lazy (constant "Zgt_left")
let coq_Zle_left = lazy (constant "Zle_left")
let coq_new_var = lazy (constant "new_var")
let coq_intro_Z = lazy (constant "intro_Z")

let coq_dec_eq = lazy (zbase_constant "Z.eq_decidable")
let coq_dec_Zne = lazy (constant "dec_Zne")
let coq_dec_Zle = lazy (zbase_constant "Z.le_decidable")
let coq_dec_Zlt = lazy (zbase_constant "Z.lt_decidable")
let coq_dec_Zgt = lazy (constant "dec_Zgt")
let coq_dec_Zge = lazy (constant "dec_Zge")

let coq_not_Zeq = lazy (constant "not_Zeq")
let coq_not_Zne = lazy (constant "not_Zne")
let coq_Znot_le_gt = lazy (constant "Znot_le_gt")
let coq_Znot_lt_ge = lazy (constant "Znot_lt_ge")
let coq_Znot_ge_lt = lazy (constant "Znot_ge_lt")
let coq_Znot_gt_le = lazy (constant "Znot_gt_le")
let coq_neq = lazy (constant "neq")
let coq_Zne = lazy (constant "Zne")
let coq_Zle = lazy (zbase_constant "Z.le")
let coq_Zgt = lazy (zbase_constant "Z.gt")
let coq_Zge = lazy (zbase_constant "Z.ge")
let coq_Zlt = lazy (zbase_constant "Z.lt")

(* Peano/Datatypes *)
let coq_le = lazy (init_constant "le")
let coq_lt = lazy (init_constant "lt")
let coq_ge = lazy (init_constant "ge")
let coq_gt = lazy (init_constant "gt")
let coq_minus = lazy (init_constant "Nat.sub")
let coq_plus = lazy (init_constant "Nat.add")
let coq_mult = lazy (init_constant "Nat.mul")
let coq_pred = lazy (init_constant "Nat.pred")
let coq_nat = lazy (init_constant "nat")
let coq_S = lazy (init_constant "S")
let coq_O = lazy (init_constant "O")

(* Compare_dec/Peano_dec/Minus *)
let coq_pred_of_minus = lazy (constant "pred_of_minus")
let coq_le_gt_dec = lazy (constant "le_gt_dec")
let coq_dec_eq_nat = lazy (constant "dec_eq_nat")
let coq_dec_le = lazy (constant "dec_le")
let coq_dec_lt = lazy (constant "dec_lt")
let coq_dec_ge = lazy (constant "dec_ge")
let coq_dec_gt = lazy (constant "dec_gt")
let coq_not_eq = lazy (constant "not_eq")
let coq_not_le = lazy (constant "not_le")
let coq_not_lt = lazy (constant "not_lt")
let coq_not_ge = lazy (constant "not_ge")
let coq_not_gt = lazy (constant "not_gt")

(* Logic/Decidable *)
let coq_eq_ind_r = lazy (constant "eq_ind_r")

let coq_dec_or = lazy (constant "dec_or")
let coq_dec_and = lazy (constant "dec_and")
let coq_dec_imp = lazy (constant "dec_imp")
let coq_dec_iff = lazy (constant "dec_iff")
let coq_dec_not = lazy (constant "dec_not")
let coq_dec_False = lazy (constant "dec_False")
let coq_dec_not_not = lazy (constant "dec_not_not")
let coq_dec_True = lazy (constant "dec_True")

let coq_not_or = lazy (constant "not_or")
let coq_not_and = lazy (constant "not_and")
let coq_not_imp = lazy (constant "not_imp")
let coq_not_iff = lazy (constant "not_iff")
let coq_not_not = lazy (constant "not_not")
let coq_imp_simp = lazy (constant "imp_simp")
let coq_iff = lazy (constant "iff")
let coq_not = lazy (init_constant "not")
let coq_and = lazy (init_constant "and")
let coq_or = lazy (init_constant "or")
let coq_eq = lazy (init_constant "eq")
let coq_ex = lazy (init_constant "ex")
let coq_False = lazy (init_constant "False")
let coq_True = lazy (init_constant "True")

(* uses build_coq_and, build_coq_not, build_coq_or, build_coq_ex *)

(* For unfold *)
let evaluable_ref_of_constr s c =
  let env = Global.env () in
  let evd = Evd.from_env env in
  match EConstr.kind evd (Lazy.force c) with
  | Const (kn,u) when Tacred.is_evaluable env (EvalConstRef kn) ->
      EvalConstRef kn
  | _ -> anomaly ~label:"Coq_omega" (Pp.str (s^" is not an evaluable constant."))

let sp_Zsucc =     lazy (evaluable_ref_of_constr "Z.succ" coq_Zsucc)
let sp_Zpred =     lazy (evaluable_ref_of_constr "Z.pred" coq_Zpred)
let sp_Zminus = lazy (evaluable_ref_of_constr "Z.sub" coq_Zminus)
let sp_Zle = lazy (evaluable_ref_of_constr "Z.le" coq_Zle)
let sp_Zgt = lazy (evaluable_ref_of_constr "Z.gt" coq_Zgt)
let sp_Zge = lazy (evaluable_ref_of_constr "Z.ge" coq_Zge)
let sp_Zlt = lazy (evaluable_ref_of_constr "Z.lt" coq_Zlt)
let sp_not = lazy (evaluable_ref_of_constr "not" coq_not)

let mk_var v = mkVar (Id.of_string v)
let mk_plus t1 t2 = mkApp (Lazy.force coq_Zplus, [| t1; t2 |])
let mk_times t1 t2 = mkApp (Lazy.force coq_Zmult, [| t1; t2 |])
let mk_minus t1 t2 = mkApp (Lazy.force coq_Zminus, [| t1;t2 |])
let mk_gen_eq ty t1 t2 = mkApp (Lazy.force coq_eq, [| ty; t1; t2 |])
let mk_eq t1 t2 = mk_gen_eq (Lazy.force coq_Z) t1 t2
let mk_le t1 t2 = mkApp (Lazy.force coq_Zle, [| t1; t2 |])
let mk_gt t1 t2 = mkApp (Lazy.force coq_Zgt, [| t1; t2 |])
let mk_inv t = mkApp (Lazy.force coq_Zopp, [| t |])
let mk_and t1 t2 =  mkApp (Lazy.force coq_and, [| t1; t2 |])
let mk_or t1 t2 =  mkApp (Lazy.force coq_or, [| t1; t2 |])
let mk_not t = mkApp (Lazy.force coq_not, [| t |])
let mk_eq_rel t1 t2 = mk_gen_eq (Lazy.force coq_comparison) t1 t2
let mk_inj t = mkApp (Lazy.force coq_Z_of_nat, [| t |])

let mk_integer n =
  let rec loop n =
    if n =? one then Lazy.force coq_xH else
    mkApp((if n mod two =? zero then Lazy.force coq_xO else Lazy.force coq_xI),
		[| loop (n/two) |])
  in
  if n =? zero then Lazy.force coq_Z0
  else mkApp ((if n >? zero then Lazy.force coq_Zpos else Lazy.force coq_Zneg),
		 [| loop (abs n) |])

type omega_constant =
  | Zplus | Zmult | Zminus | Zsucc | Zopp | Zpred
  | Plus | Mult | Minus | Pred | S | O
  | Zpos | Zneg | Z0 | Z_of_nat
  | Eq | Neq
  | Zne | Zle | Zlt | Zge | Zgt
  | Z | Nat
  | And | Or | False | True | Not | Iff
  | Le | Lt | Ge | Gt
  | Other of string

type omega_proposition =
  | Keq of constr * constr * constr
  | Kn

type result =
  | Kvar of Id.t
  | Kapp of omega_constant * constr list
  | Kimp of constr * constr
  | Kufo

(* Nota: Kimp correspond to a binder (Prod), but hopefully we won't
   have to bother with term lifting: Kimp will correspond to anonymous
   product, for which (Rel 1) doesn't occur in the right term.
   Moreover, we'll work on fully introduced goals, hence no Rel's in
   the term parts that we manipulate, but rather Var's.
   Said otherwise: all constr manipulated here are closed *)

let destructurate_prop sigma t =
  let eq_constr c1 c2 = eq_constr sigma c1 c2 in
  let c, args = decompose_app sigma t in
  match EConstr.kind sigma c, args with
    | _, [_;_;_] when eq_constr (Lazy.force coq_eq) c -> Kapp (Eq,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_neq) -> Kapp (Neq,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_Zne) -> Kapp (Zne,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_Zle) -> Kapp (Zle,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_Zlt) -> Kapp (Zlt,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_Zge) -> Kapp (Zge,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_Zgt) -> Kapp (Zgt,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_and) -> Kapp (And,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_or) -> Kapp (Or,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_iff) -> Kapp (Iff, args)
    | _, [_] when eq_constr c (Lazy.force coq_not) -> Kapp (Not,args)
    | _, [] when eq_constr c (Lazy.force coq_False) -> Kapp (False,args)
    | _, [] when eq_constr c (Lazy.force coq_True) -> Kapp (True,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_le) -> Kapp (Le,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_lt) -> Kapp (Lt,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_ge) -> Kapp (Ge,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_gt) -> Kapp (Gt,args)
    | Const (sp,_), args ->
	Kapp (Other (string_of_path (path_of_global (ConstRef sp))),args)
    | Construct (csp,_) , args ->
	Kapp (Other (string_of_path (path_of_global (ConstructRef csp))), args)
    | Ind (isp,_), args ->
	Kapp (Other (string_of_path (path_of_global (IndRef isp))),args)
    | Var id,[] -> Kvar id
    | Prod (Anonymous,typ,body), [] -> Kimp(typ,body)
    | Prod (Name _,_,_),[] -> CErrors.user_err Pp.(str "Omega: Not a quantifier-free goal")
    | _ -> Kufo

let nf = Tacred.simpl

let destructurate_type env sigma t =
  let is_conv = Reductionops.is_conv env sigma in
  let c, args = decompose_app sigma (nf env sigma t) in
  match EConstr.kind sigma c, args with
    | _, [] when is_conv c (Lazy.force coq_Z) -> Kapp (Z,args)
    | _, [] when is_conv c (Lazy.force coq_nat) -> Kapp (Nat,args)
    | _ -> Kufo

let destructurate_term sigma t =
  let eq_constr c1 c2 = eq_constr sigma c1 c2 in
  let c, args = decompose_app sigma t in
  match EConstr.kind sigma c, args with
    | _, [_;_] when eq_constr c (Lazy.force coq_Zplus) -> Kapp (Zplus,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_Zmult) -> Kapp (Zmult,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_Zminus) -> Kapp (Zminus,args)
    | _, [_] when eq_constr c (Lazy.force coq_Zsucc) -> Kapp (Zsucc,args)
    | _, [_] when eq_constr c (Lazy.force coq_Zpred) -> Kapp (Zpred,args)
    | _, [_] when eq_constr c (Lazy.force coq_Zopp) -> Kapp (Zopp,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_plus) -> Kapp (Plus,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_mult) -> Kapp (Mult,args)
    | _, [_;_] when eq_constr c (Lazy.force coq_minus) -> Kapp (Minus,args)
    | _, [_] when eq_constr c (Lazy.force coq_pred) -> Kapp (Pred,args)
    | _, [_] when eq_constr c (Lazy.force coq_S) -> Kapp (S,args)
    | _, [] when eq_constr c (Lazy.force coq_O) -> Kapp (O,args)
    | _, [_] when eq_constr c (Lazy.force coq_Zpos) -> Kapp (Zneg,args)
    | _, [_] when eq_constr c (Lazy.force coq_Zneg) -> Kapp (Zpos,args)
    | _, [] when eq_constr c (Lazy.force coq_Z0) -> Kapp (Z0,args)
    | _, [_] when eq_constr c (Lazy.force coq_Z_of_nat) -> Kapp (Z_of_nat,args)
    | Var id,[] -> Kvar id
    | _ -> Kufo

let recognize_number sigma t =
  let eq_constr c1 c2 = eq_constr sigma c1 c2 in
  let rec loop t =
    match decompose_app sigma t with
      | f, [t] when eq_constr f (Lazy.force coq_xI) -> one + two * loop t
      | f, [t] when eq_constr f (Lazy.force coq_xO) -> two * loop t
      | f, [] when eq_constr f (Lazy.force coq_xH) -> one
      | _ -> failwith "not a number"
  in
  match decompose_app sigma t with
    | f, [t] when eq_constr f (Lazy.force coq_Zpos) -> loop t
    | f, [t] when eq_constr f (Lazy.force coq_Zneg) -> neg (loop t)
    | f, [] when eq_constr f (Lazy.force coq_Z0) -> zero
    | _ -> failwith "not a number"

type constr_path =
  | P_APP of int
  (* Abstraction and product *)
  | P_BODY
  | P_TYPE
  (* Case *)
  | P_BRANCH of int
  | P_ARITY
  | P_ARG

let context sigma operation path (t : constr) =
  let rec loop i p0 t =
    match (p0,EConstr.kind sigma t) with
      | (p, Cast (c,k,t)) -> mkCast (loop i p c,k,t)
      | ([], _) -> operation i t
      | ((P_APP n :: p),  App (f,v)) ->
	  let v' = Array.copy v in
	  v'.(pred n) <- loop i p v'.(pred n); mkApp (f, v')
      | ((P_BRANCH n :: p), Case (ci,q,c,v)) ->
	  (* avant, y avait mkApp... anyway, BRANCH seems nowhere used *)
	  let v' = Array.copy v in
	  v'.(n) <- loop i p v'.(n); (mkCase (ci,q,c,v'))
      | ((P_ARITY :: p),  App (f,l)) ->
	  mkApp (loop i p f,l)
      | ((P_ARG :: p),  App (f,v)) ->
	  let v' = Array.copy v in
	  v'.(0) <- loop i p v'.(0); mkApp (f,v')
      | (p, Fix ((_,n as ln),(tys,lna,v))) ->
	  let l = Array.length v in
	  let v' = Array.copy v in
	  v'.(n)<- loop (Pervasives.(+) i l) p v.(n); (mkFix (ln,(tys,lna,v')))
      | ((P_BODY :: p), Prod (n,t,c)) ->
	  (mkProd (n,t,loop (succ i) p c))
      | ((P_BODY :: p), Lambda (n,t,c)) ->
	  (mkLambda (n,t,loop (succ i) p c))
      | ((P_BODY :: p), LetIn (n,b,t,c)) ->
	  (mkLetIn (n,b,t,loop (succ i) p c))
      | ((P_TYPE :: p), Prod (n,t,c)) ->
	  (mkProd (n,loop i p t,c))
      | ((P_TYPE :: p), Lambda (n,t,c)) ->
	  (mkLambda (n,loop i p t,c))
      | ((P_TYPE :: p), LetIn (n,b,t,c)) ->
	  (mkLetIn (n,b,loop i p t,c))
      | (p, _) ->
	  failwith ("abstract_path " ^ string_of_int(List.length p))
  in
  loop 1 path t

let occurrence sigma path (t : constr) =
  let rec loop p0 t = match (p0,EConstr.kind sigma t) with
    | (p, Cast (c,_,_)) -> loop p c
    | ([], _) -> t
    | ((P_APP n :: p),  App (f,v)) -> loop p v.(pred n)
    | ((P_BRANCH n :: p), Case (_,_,_,v)) -> loop p v.(n)
    | ((P_ARITY :: p),  App (f,_)) -> loop p f
    | ((P_ARG :: p),  App (f,v)) -> loop p v.(0)
    | (p, Fix((_,n) ,(_,_,v))) -> loop p v.(n)
    | ((P_BODY :: p), Prod (n,t,c)) -> loop p c
    | ((P_BODY :: p), Lambda (n,t,c)) -> loop p c
    | ((P_BODY :: p), LetIn (n,b,t,c)) -> loop p c
    | ((P_TYPE :: p), Prod (n,term,c)) -> loop p term
    | ((P_TYPE :: p), Lambda (n,term,c)) -> loop p term
    | ((P_TYPE :: p), LetIn (n,b,term,c)) -> loop p term
    | (p, _) ->
	failwith ("occurrence " ^ string_of_int(List.length p))
  in
  loop path t

let abstract_path sigma typ path t =
  let term_occur = ref (mkRel 0) in
  let abstract = context sigma (fun i t -> term_occur:= t; mkRel i) path t in
  mkLambda (Name (Id.of_string "x"), typ, abstract), !term_occur

let focused_simpl path =
  let open Tacmach.New in
  Proofview.Goal.nf_enter begin fun gl ->
  let newc = context (project gl) (fun i t -> pf_nf gl t) (List.rev path) (pf_concl gl) in
  convert_concl_no_check newc DEFAULTcast
  end

let focused_simpl path = focused_simpl path

type oformula =
  | Oplus of oformula * oformula
  | Oinv of  oformula
  | Otimes of oformula * oformula
  | Oatom of Id.t
  | Oz of bigint
  | Oufo of constr

let rec oprint = function
  | Oplus(t1,t2) ->
      print_string "("; oprint t1; print_string "+";
      oprint t2; print_string ")"
  | Oinv t -> print_string "~"; oprint t
  | Otimes (t1,t2) ->
      print_string "("; oprint t1; print_string "*";
      oprint t2; print_string ")"
  | Oatom s -> print_string (Id.to_string s)
  | Oz i -> print_string (string_of_bigint i)
  | Oufo f -> print_string "?"

let rec weight = function
  | Oatom c -> intern_id c
  | Oz _ -> -1
  | Oinv c -> weight c
  | Otimes(c,_) -> weight c
  | Oplus _ -> failwith "weight"
  | Oufo _ -> -1

let rec val_of = function
  | Oatom c -> mkVar c
  | Oz c -> mk_integer c
  | Oinv c -> mkApp (Lazy.force coq_Zopp, [| val_of c |])
  | Otimes (t1,t2) -> mkApp (Lazy.force coq_Zmult, [| val_of t1; val_of t2 |])
  | Oplus(t1,t2) -> mkApp (Lazy.force coq_Zplus, [| val_of t1; val_of t2 |])
  | Oufo c -> c

let compile name kind =
  let rec loop accu = function
    | Oplus(Otimes(Oatom v,Oz n),r) -> loop ({v=intern_id v; c=n} :: accu) r
    | Oz n ->
	let id = new_id () in
	tag_hypothesis name id;
	{kind = kind; body = List.rev accu; constant = n; id = id}
    | _ -> anomaly (Pp.str "compile_equation.")
  in
  loop []

let decompile af =
  let rec loop = function
    | ({v=v; c=n}::r) -> Oplus(Otimes(Oatom (unintern_id v),Oz n),loop r)
    | [] -> Oz af.constant
  in
  loop af.body

(** Backward compat to emulate the old Refine: normalize the goal conclusion *)
let new_hole env sigma c =
  let c = Reductionops.nf_betaiota env sigma c in
  Evarutil.new_evar env sigma c

let clever_rewrite_base_poly typ p result theorem =
  let open Tacmach.New in
  Proofview.Goal.nf_enter begin fun gl ->
  let full = pf_concl gl in
  let env = pf_env gl in
  let (abstracted,occ) = abstract_path (project gl) typ (List.rev p) full in
  Refine.refine ~typecheck:false begin fun sigma ->
  let t =
    applist
      (mkLambda
	 (Name (Id.of_string "P"),
	  mkArrow typ mkProp,
          mkLambda
	    (Name (Id.of_string "H"),
	     applist (mkRel 1,[result]),
	     mkApp (Lazy.force coq_eq_ind_r,
		       [| typ; result; mkRel 2; mkRel 1; occ; theorem |]))),
       [abstracted])
  in
  let argt = mkApp (abstracted, [|result|]) in
  let (sigma, hole) = new_hole env sigma argt in
  (sigma, applist (t, [hole]))
  end
  end

let clever_rewrite_base p result theorem =
  clever_rewrite_base_poly (Lazy.force coq_Z) p result theorem

let clever_rewrite_base_nat p result theorem =
  clever_rewrite_base_poly (Lazy.force coq_nat) p result theorem

let clever_rewrite_gen p result (t,args) =
  let theorem = applist(t, args) in
  clever_rewrite_base p result theorem

let clever_rewrite_gen_nat p result (t,args) =
  let theorem = applist(t, args) in
  clever_rewrite_base_nat p result theorem

(** Solve using the term the term [t _] *)
let refine_app gl t =
  let open Tacmach.New in
  Refine.refine ~typecheck:false begin fun sigma ->
  let env = pf_env gl in
  let ht = match EConstr.kind sigma (pf_get_type_of gl t) with
  | Prod (_, t, _) -> t
  | _ -> assert false
  in
  let (sigma, hole) = new_hole env sigma ht in
  (sigma, applist (t, [hole]))
  end

let clever_rewrite p vpath t =
  let open Tacmach.New in
  Proofview.Goal.nf_enter begin fun gl ->
  let full = pf_concl gl in
  let (abstracted,occ) = abstract_path (project gl) (Lazy.force coq_Z) (List.rev p) full in
  let vargs = List.map (fun p -> occurrence (project gl) p occ) vpath in
  let t' = applist(t, (vargs @ [abstracted])) in
  refine_app gl t'
  end

(** simpl_coeffs :
    The subterm at location [path_init] in the current goal should
    look like [(v1*c1 + (v2*c2 + ... (vn*cn + k)))], and we reduce
    via "simpl" each [ci] and the final constant [k].
    The path [path_k] gives the location of constant [k].
    Earlier, the whole was a mere call to [focused_simpl],
    leading to reduction inside the atoms [vi], which is bad,
    for instance when the atom is an evaluable definition
    (see #4132). *)

let simpl_coeffs path_init path_k =
  Proofview.Goal.enter begin fun gl ->
  let sigma = project gl in
  let rec loop n t =
    if Int.equal n 0 then pf_nf gl t
    else
      (* t should be of the form ((v * c) + ...) *)
      match EConstr.kind sigma t with
      | App(f,[|t1;t2|]) ->
         (match EConstr.kind sigma t1 with
          | App (g,[|v;c|]) ->
             let c' = pf_nf gl c in
             let t2' = loop (pred n) t2 in
             mkApp (f,[|mkApp (g,[|v;c'|]);t2'|])
          | _ -> assert false)
      | _ -> assert false
  in
  let n = Pervasives.(-) (List.length path_k) (List.length path_init) in
  let newc = context sigma (fun _ t -> loop n t) (List.rev path_init) (pf_concl gl)
  in
  convert_concl_no_check newc DEFAULTcast
  end

let rec shuffle p (t1,t2) =
  match t1,t2 with
    | Oplus(l1,r1), Oplus(l2,r2) ->
	if weight l1 > weight l2 then
          let (tac,t') = shuffle (P_APP 2 :: p) (r1,t2) in
          (clever_rewrite p [[P_APP 1;P_APP 1];
			     [P_APP 1; P_APP 2];[P_APP 2]]
             (Lazy.force coq_fast_Zplus_assoc_reverse)
           :: tac,
           Oplus(l1,t'))
	else
	  let (tac,t') = shuffle (P_APP 2 :: p) (t1,r2) in
          (clever_rewrite p [[P_APP 1];[P_APP 2;P_APP 1];[P_APP 2;P_APP 2]]
             (Lazy.force coq_fast_Zplus_permute)
           :: tac,
           Oplus(l2,t'))
    | Oplus(l1,r1), t2 ->
	if weight l1 > weight t2 then
          let (tac,t') = shuffle (P_APP 2 :: p) (r1,t2) in
          clever_rewrite p [[P_APP 1;P_APP 1]; [P_APP 1; P_APP 2];[P_APP 2]]
            (Lazy.force coq_fast_Zplus_assoc_reverse)
          :: tac,
          Oplus(l1, t')
	else
          [clever_rewrite p [[P_APP 1];[P_APP 2]]
	     (Lazy.force coq_fast_Zplus_comm)],
          Oplus(t2,t1)
    | t1,Oplus(l2,r2) ->
	if weight l2 > weight t1 then
          let (tac,t') = shuffle (P_APP 2 :: p) (t1,r2) in
          clever_rewrite p [[P_APP 1];[P_APP 2;P_APP 1];[P_APP 2;P_APP 2]]
            (Lazy.force coq_fast_Zplus_permute)
          :: tac,
          Oplus(l2,t')
	else [],Oplus(t1,t2)
    | Oz t1,Oz t2 ->
	[focused_simpl p], Oz(Bigint.add t1 t2)
    | t1,t2 ->
	if weight t1 < weight t2 then
          [clever_rewrite p [[P_APP 1];[P_APP 2]]
	     (Lazy.force coq_fast_Zplus_comm)],
	  Oplus(t2,t1)
	else [],Oplus(t1,t2)

let shuffle_mult p_init k1 e1 k2 e2 =
  let rec loop p = function
    | (({c=c1;v=v1}::l1) as l1'),(({c=c2;v=v2}::l2) as l2') ->
	if Int.equal v1 v2 then
          let tac =
            clever_rewrite p [[P_APP 1; P_APP 1; P_APP 1; P_APP 1];
                              [P_APP 1; P_APP 1; P_APP 1; P_APP 2];
                              [P_APP 2; P_APP 1; P_APP 1; P_APP 2];
                              [P_APP 1; P_APP 1; P_APP 2];
                              [P_APP 2; P_APP 1; P_APP 2];
                              [P_APP 1; P_APP 2];
                              [P_APP 2; P_APP 2]]
              (Lazy.force coq_fast_OMEGA10)
	  in
          if Bigint.add (Bigint.mult k1 c1) (Bigint.mult k2 c2) =? zero then
            let tac' =
	      clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 2]]
                (Lazy.force coq_fast_Zred_factor5) in
	    tac :: focused_simpl (P_APP 2::P_APP 1:: p) :: tac' ::
	    loop p (l1,l2)
          else tac :: loop (P_APP 2 :: p) (l1,l2)
	else if v1 > v2 then
          clever_rewrite p [[P_APP 1; P_APP 1; P_APP 1; P_APP 1];
                            [P_APP 1; P_APP 1; P_APP 1; P_APP 2];
                            [P_APP 1; P_APP 1; P_APP 2];
                            [P_APP 2];
                            [P_APP 1; P_APP 2]]
            (Lazy.force coq_fast_OMEGA11) ::
          loop (P_APP 2 :: p) (l1,l2')
	else
          clever_rewrite p [[P_APP 2; P_APP 1; P_APP 1; P_APP 1];
                            [P_APP 2; P_APP 1; P_APP 1; P_APP 2];
                            [P_APP 1];
                            [P_APP 2; P_APP 1; P_APP 2];
                            [P_APP 2; P_APP 2]]
            (Lazy.force coq_fast_OMEGA12) ::
          loop (P_APP 2 :: p) (l1',l2)
    | ({c=c1;v=v1}::l1), [] ->
        clever_rewrite p [[P_APP 1; P_APP 1; P_APP 1; P_APP 1];
                          [P_APP 1; P_APP 1; P_APP 1; P_APP 2];
                          [P_APP 1; P_APP 1; P_APP 2];
                          [P_APP 2];
                          [P_APP 1; P_APP 2]]
          (Lazy.force coq_fast_OMEGA11) ::
        loop (P_APP 2 :: p) (l1,[])
    | [],({c=c2;v=v2}::l2) ->
        clever_rewrite p  [[P_APP 2; P_APP 1; P_APP 1; P_APP 1];
                           [P_APP 2; P_APP 1; P_APP 1; P_APP 2];
                           [P_APP 1];
                           [P_APP 2; P_APP 1; P_APP 2];
                           [P_APP 2; P_APP 2]]
          (Lazy.force coq_fast_OMEGA12) ::
        loop (P_APP 2 :: p) ([],l2)
    | [],[] -> [simpl_coeffs p_init p]
  in
  loop p_init (e1,e2)

let shuffle_mult_right p_init e1 k2 e2 =
  let rec loop p = function
    | (({c=c1;v=v1}::l1) as l1'),(({c=c2;v=v2}::l2) as l2') ->
	if Int.equal v1 v2 then
          let tac =
            clever_rewrite p
              [[P_APP 1; P_APP 1; P_APP 1];
               [P_APP 1; P_APP 1; P_APP 2];
               [P_APP 2; P_APP 1; P_APP 1; P_APP 2];
               [P_APP 1; P_APP 2];
               [P_APP 2; P_APP 1; P_APP 2];
               [P_APP 2; P_APP 2]]
              (Lazy.force coq_fast_OMEGA15)
	  in
          if Bigint.add c1 (Bigint.mult k2 c2) =? zero then
            let tac' =
              clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 2]]
                (Lazy.force coq_fast_Zred_factor5)
	    in
            tac :: focused_simpl (P_APP 2::P_APP 1:: p) :: tac' ::
            loop p (l1,l2)
          else tac :: loop (P_APP 2 :: p) (l1,l2)
	else if v1 > v2 then
          clever_rewrite p [[P_APP 1;P_APP 1]; [P_APP 1; P_APP 2];[P_APP 2]]
            (Lazy.force coq_fast_Zplus_assoc_reverse) ::
          loop (P_APP 2 :: p) (l1,l2')
	else
          clever_rewrite p [[P_APP 2; P_APP 1; P_APP 1; P_APP 1];
                            [P_APP 2; P_APP 1; P_APP 1; P_APP 2];
                            [P_APP 1];
                            [P_APP 2; P_APP 1; P_APP 2];
                            [P_APP 2; P_APP 2]]
            (Lazy.force coq_fast_OMEGA12) ::
          loop (P_APP 2 :: p) (l1',l2)
    | ({c=c1;v=v1}::l1), [] ->
        clever_rewrite p [[P_APP 1;P_APP 1]; [P_APP 1; P_APP 2];[P_APP 2]]
          (Lazy.force coq_fast_Zplus_assoc_reverse) ::
        loop (P_APP 2 :: p) (l1,[])
    | [],({c=c2;v=v2}::l2) ->
        clever_rewrite p [[P_APP 2; P_APP 1; P_APP 1; P_APP 1];
                          [P_APP 2; P_APP 1; P_APP 1; P_APP 2];
                          [P_APP 1];
                          [P_APP 2; P_APP 1; P_APP 2];
                          [P_APP 2; P_APP 2]]
          (Lazy.force coq_fast_OMEGA12) ::
        loop (P_APP 2 :: p) ([],l2)
    | [],[] -> [simpl_coeffs p_init p]
  in
  loop p_init (e1,e2)

let rec shuffle_cancel p = function
  | [] -> [focused_simpl p]
  | ({c=c1}::l1) ->
      let tac =
	clever_rewrite p [[P_APP 1; P_APP 1; P_APP 1];[P_APP 1; P_APP 2];
                          [P_APP 2; P_APP 2];
                          [P_APP 1; P_APP 1; P_APP 2; P_APP 1]]
          (if c1 >? zero then
	     (Lazy.force coq_fast_OMEGA13)
	   else
	     (Lazy.force coq_fast_OMEGA14))
      in
      tac :: shuffle_cancel p l1

let rec scalar p n = function
  | Oplus(t1,t2) ->
      let tac1,t1' = scalar (P_APP 1 :: p) n t1 and
        tac2,t2' = scalar (P_APP 2 :: p) n t2 in
      clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 1;P_APP 2];[P_APP 2]]
        (Lazy.force coq_fast_Zmult_plus_distr_l) ::
      (tac1 @ tac2), Oplus(t1',t2')
  | Oinv t ->
      [clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 2]]
	 (Lazy.force coq_fast_Zmult_opp_comm);
       focused_simpl (P_APP 2 :: p)], Otimes(t,Oz(neg n))
  | Otimes(t1,Oz x) ->
      [clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 1;P_APP 2];[P_APP 2]]
         (Lazy.force coq_fast_Zmult_assoc_reverse);
       focused_simpl (P_APP 2 :: p)],
      Otimes(t1,Oz (n*x))
  | Otimes(t1,t2) -> CErrors.user_err Pp.(str "Omega: Can't solve a goal with non-linear products")
  | (Oatom _ as t) -> [], Otimes(t,Oz n)
  | Oz i -> [focused_simpl p],Oz(n*i)
  | Oufo c -> [], Oufo (mkApp (Lazy.force coq_Zmult, [| mk_integer n; c |]))

let scalar_norm p_init =
  let rec loop p = function
    | [] -> [simpl_coeffs p_init p]
    | (_::l) ->
	clever_rewrite p
          [[P_APP 1; P_APP 1; P_APP 1];[P_APP 1; P_APP 1; P_APP 2];
           [P_APP 1; P_APP 2];[P_APP 2]]
          (Lazy.force coq_fast_OMEGA16) :: loop (P_APP 2 :: p) l
  in
  loop p_init

let norm_add p_init =
  let rec loop p = function
    | [] -> [simpl_coeffs p_init p]
    | _:: l ->
	clever_rewrite p [[P_APP 1;P_APP 1]; [P_APP 1; P_APP 2];[P_APP 2]]
          (Lazy.force coq_fast_Zplus_assoc_reverse) ::
	loop (P_APP 2 :: p) l
  in
  loop p_init

let scalar_norm_add p_init =
  let rec loop p = function
    | [] -> [simpl_coeffs p_init p]
    | _ :: l ->
	clever_rewrite p
          [[P_APP 1; P_APP 1; P_APP 1; P_APP 1];
           [P_APP 1; P_APP 1; P_APP 1; P_APP 2];
           [P_APP 1; P_APP 1; P_APP 2]; [P_APP 2]; [P_APP 1; P_APP 2]]
          (Lazy.force coq_fast_OMEGA11) :: loop (P_APP 2 :: p) l
  in
  loop p_init

let rec negate p = function
  | Oplus(t1,t2) ->
      let tac1,t1' = negate (P_APP 1 :: p) t1 and
        tac2,t2' = negate (P_APP 2 :: p) t2 in
      clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 1;P_APP 2]]
        (Lazy.force coq_fast_Zopp_plus_distr) ::
      (tac1 @ tac2),
      Oplus(t1',t2')
  | Oinv t ->
      [clever_rewrite p [[P_APP 1;P_APP 1]] (Lazy.force coq_fast_Zopp_involutive)], t
  | Otimes(t1,Oz x) ->
      [clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 1;P_APP 2]]
         (Lazy.force coq_fast_Zopp_mult_distr_r);
       focused_simpl (P_APP 2 :: p)], Otimes(t1,Oz (neg x))
  | Otimes(t1,t2) -> CErrors.user_err Pp.(str "Omega: Can't solve a goal with non-linear products")
  | (Oatom _ as t) ->
      let r = Otimes(t,Oz(negone)) in
      [clever_rewrite p [[P_APP 1]] (Lazy.force coq_fast_Zopp_eq_mult_neg_1)], r
  | Oz i -> [focused_simpl p],Oz(neg i)
  | Oufo c -> [], Oufo (mkApp (Lazy.force coq_Zopp, [| c |]))

let rec transform sigma p t =
  let default isnat t' =
    try
      let v,th,_ = find_constr sigma t' in
      [clever_rewrite_base p (mkVar v) (mkVar th)], Oatom v
    with e when CErrors.noncritical e ->
      let v = new_identifier_var ()
      and th = new_identifier () in
      hide_constr t' v th isnat;
      [clever_rewrite_base p (mkVar v) (mkVar th)], Oatom v
  in
  try match destructurate_term sigma t with
    | Kapp(Zplus,[t1;t2]) ->
	let tac1,t1' = transform sigma (P_APP 1 :: p) t1
	and tac2,t2' = transform sigma (P_APP 2 :: p) t2 in
	let tac,t' = shuffle p (t1',t2') in
	tac1 @ tac2 @ tac, t'
    | Kapp(Zminus,[t1;t2]) ->
	let tac,t =
	  transform sigma p
	    (mkApp (Lazy.force coq_Zplus,
		     [| t1; (mkApp (Lazy.force coq_Zopp, [| t2 |])) |])) in
	unfold sp_Zminus :: tac,t
    | Kapp(Zsucc,[t1]) ->
	let tac,t = transform sigma p (mkApp (Lazy.force coq_Zplus,
					 [| t1; mk_integer one |])) in
	unfold sp_Zsucc :: tac,t
    | Kapp(Zpred,[t1]) ->
	let tac,t = transform sigma p (mkApp (Lazy.force coq_Zplus,
					 [| t1; mk_integer negone |])) in
	unfold sp_Zpred :: tac,t
   | Kapp(Zmult,[t1;t2]) ->
       let tac1,t1' = transform sigma (P_APP 1 :: p) t1
       and tac2,t2' = transform sigma (P_APP 2 :: p) t2 in
       begin match t1',t2' with
         | (_,Oz n) -> let tac,t' = scalar p n t1' in tac1 @ tac2 @ tac,t'
         | (Oz n,_) ->
             let sym =
	       clever_rewrite p [[P_APP 1];[P_APP 2]]
		 (Lazy.force coq_fast_Zmult_comm) in
             let tac,t' = scalar p n t2' in tac1 @ tac2 @ (sym :: tac),t'
         | _ -> default false t
       end
   | Kapp((Zpos|Zneg|Z0),_) ->
       (try ([],Oz(recognize_number sigma t))
        with e when CErrors.noncritical e -> default false t)
   | Kvar s -> [],Oatom s
   | Kapp(Zopp,[t]) ->
       let tac,t' = transform sigma (P_APP 1 :: p) t in
       let tac',t'' = negate p t' in
       tac @ tac', t''
   | Kapp(Z_of_nat,[t']) -> default true t'
   | _ -> default false t
  with e when catchable_exception e -> default false t

let shrink_pair p f1 f2 =
  match f1,f2 with
    | Oatom v,Oatom _ ->
	let r = Otimes(Oatom v,Oz two) in
	clever_rewrite p [[P_APP 1]] (Lazy.force coq_fast_Zred_factor1), r
    | Oatom v, Otimes(_,c2) ->
	let r = Otimes(Oatom v,Oplus(c2,Oz one)) in
	clever_rewrite p [[P_APP 1];[P_APP 2;P_APP 2]]
	  (Lazy.force coq_fast_Zred_factor2), r
    | Otimes (v1,c1),Oatom v ->
	let r = Otimes(Oatom v,Oplus(c1,Oz one)) in
	clever_rewrite p [[P_APP 2];[P_APP 1;P_APP 2]]
          (Lazy.force coq_fast_Zred_factor3), r
    | Otimes (Oatom v,c1),Otimes (v2,c2) ->
	let r = Otimes(Oatom v,Oplus(c1,c2)) in
	clever_rewrite p
          [[P_APP 1;P_APP 1];[P_APP 1;P_APP 2];[P_APP 2;P_APP 2]]
          (Lazy.force coq_fast_Zred_factor4),r
    | t1,t2 ->
	begin
	  oprint t1; print_newline (); oprint t2; print_newline ();
	  flush Pervasives.stdout; CErrors.user_err Pp.(str "shrink.1")
	end

let reduce_factor p = function
  | Oatom v ->
      let r = Otimes(Oatom v,Oz one) in
      [clever_rewrite p [[]] (Lazy.force coq_fast_Zred_factor0)],r
  | Otimes(Oatom v,Oz n) as f -> [],f
  | Otimes(Oatom v,c) ->
      let rec compute = function
        | Oz n -> n
	| Oplus(t1,t2) -> Bigint.add (compute t1) (compute t2)
	| _ -> CErrors.user_err Pp.(str "condense.1")
      in
      [focused_simpl (P_APP 2 :: p)], Otimes(Oatom v,Oz(compute c))
  | t -> oprint t; CErrors.user_err Pp.(str "reduce_factor.1")

let rec condense p = function
  | Oplus(f1,(Oplus(f2,r) as t)) ->
      if Int.equal (weight f1) (weight f2) then begin
	let shrink_tac,t = shrink_pair (P_APP 1 :: p) f1 f2 in
	let assoc_tac =
          clever_rewrite p
            [[P_APP 1];[P_APP 2;P_APP 1];[P_APP 2;P_APP 2]]
            (Lazy.force coq_fast_Zplus_assoc) in
	let tac_list,t' = condense p (Oplus(t,r)) in
	(assoc_tac :: shrink_tac :: tac_list), t'
      end else begin
	let tac,f = reduce_factor (P_APP 1 :: p) f1 in
	let tac',t' = condense (P_APP 2 :: p) t in
	(tac @ tac'), Oplus(f,t')
      end
  | Oplus(f1,Oz n) ->
      let tac,f1' = reduce_factor (P_APP 1 :: p) f1 in tac,Oplus(f1',Oz n)
  | Oplus(f1,f2) ->
      if Int.equal (weight f1) (weight f2) then begin
	let tac_shrink,t = shrink_pair p f1 f2 in
	let tac,t' = condense p t in
	tac_shrink :: tac,t'
      end else begin
	let tac,f = reduce_factor (P_APP 1 :: p) f1 in
	let tac',t' = condense (P_APP 2 :: p) f2 in
	(tac @ tac'),Oplus(f,t')
      end
  | Oz _ as t -> [],t
  | t ->
      let tac,t' = reduce_factor p t in
      let final = Oplus(t',Oz zero) in
      let tac' = clever_rewrite p [[]] (Lazy.force coq_fast_Zred_factor6) in
      tac @ [tac'], final

let rec clear_zero p = function
  | Oplus(Otimes(Oatom v,Oz n),r) when n =? zero ->
      let tac =
	clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 2]]
	  (Lazy.force coq_fast_Zred_factor5) in
      let tac',t = clear_zero p r in
      tac :: tac',t
  | Oplus(f,r) ->
      let tac,t = clear_zero (P_APP 2 :: p) r in tac,Oplus(f,t)
  | t -> [],t

let replay_history tactic_normalisation =
  let aux  = Id.of_string "auxiliary" in
  let aux1 = Id.of_string "auxiliary_1" in
  let aux2 = Id.of_string "auxiliary_2" in
  let izero = mk_integer zero in
  let rec loop t : unit Proofview.tactic =
    match t with
      | HYP e :: l ->
	  begin
	    try
	      tclTHEN
		(Id.List.assoc (hyp_of_tag e.id) tactic_normalisation)
		(loop l)
	    with Not_found -> loop l end
      | NEGATE_CONTRADICT (e2,e1,b) :: l ->
	  let eq1 = decompile e1
	  and eq2 = decompile e2 in
	  let id1 = hyp_of_tag e1.id
	  and id2 = hyp_of_tag e2.id in
	  let k = if b then negone else one in
	  let p_initial = [P_APP 1;P_TYPE] in
	  let tac= shuffle_mult_right p_initial e1.body k e2.body in
	  tclTHENLIST [
	    generalize_tac
	      [mkApp (Lazy.force coq_OMEGA17, [|
		val_of eq1;
		val_of eq2;
		mk_integer k;
		mkVar id1; mkVar id2 |])];
	    mk_then tac;
	    (intros_using [aux]);
	    resolve_id aux;
            reflexivity
          ]
      | CONTRADICTION (e1,e2) :: l ->
	  let eq1 = decompile e1
	  and eq2 = decompile e2 in
	  let p_initial = [P_APP 2;P_TYPE] in
	  let tac = shuffle_cancel p_initial e1.body in
	  let solve_le =
            let not_sup_sup = mkApp (Lazy.force coq_eq,
				     [|
					Lazy.force coq_comparison;
					Lazy.force coq_Gt;
					Lazy.force coq_Gt |])
	    in
            tclTHENS
	      (tclTHENLIST [
		unfold sp_Zle;
		simpl_in_concl;
		intro;
		(absurd not_sup_sup) ])
	      [ assumption ; reflexivity ]
	  in
	  let theorem =
            mkApp (Lazy.force coq_OMEGA2, [|
		      val_of eq1; val_of eq2;
		      mkVar (hyp_of_tag e1.id);
		      mkVar (hyp_of_tag e2.id) |])
	  in
	  Proofview.tclTHEN (tclTHEN (generalize_tac [theorem]) (mk_then tac)) solve_le
      | DIVIDE_AND_APPROX (e1,e2,k,d) :: l ->
	  let id = hyp_of_tag e1.id in
	  let eq1 = val_of(decompile e1)
	  and eq2 = val_of(decompile e2) in
	  let kk = mk_integer k
	  and dd = mk_integer d in
	  let rhs = mk_plus (mk_times eq2 kk) dd in
	  let state_eg = mk_eq eq1 rhs in
	  let tac = scalar_norm_add [P_APP 3] e2.body in
	  tclTHENS
	    (cut state_eg)
	    [ tclTHENS
	        (tclTHENLIST [
		  (intros_using [aux]);
		  (generalize_tac
		    [mkApp (Lazy.force coq_OMEGA1,
		      [| eq1; rhs; mkVar aux; mkVar id |])]);
		  (clear [aux;id]);
		  (intros_using [id]);
		  (cut (mk_gt kk dd)) ])
	        [ tclTHENS
		    (cut (mk_gt kk izero))
		    [ tclTHENLIST [
		        (intros_using [aux1; aux2]);
		        (generalize_tac
			  [mkApp (Lazy.force coq_Zmult_le_approx,
			    [| kk;eq2;dd;mkVar aux1;mkVar aux2; mkVar id |])]);
		        (clear [aux1;aux2;id]);
		        (intros_using [id]);
		        (loop l) ];
		      tclTHENLIST [
			(unfold sp_Zgt);
			simpl_in_concl;
			reflexivity ] ];
		  tclTHENLIST [ unfold sp_Zgt; simpl_in_concl; reflexivity ]
                ];
	      tclTHEN (mk_then tac) reflexivity ]

      | NOT_EXACT_DIVIDE (e1,k) :: l ->
	  let c = floor_div e1.constant k in
	  let d = Bigint.sub e1.constant (Bigint.mult c k) in
	  let e2 =  {id=e1.id; kind=EQUA;constant = c;
                     body = map_eq_linear (fun c -> c / k) e1.body } in
	  let eq2 = val_of(decompile e2) in
	  let kk = mk_integer k
	  and dd = mk_integer d in
	  let tac = scalar_norm_add [P_APP 2] e2.body in
	  tclTHENS
	    (cut (mk_gt dd izero))
	    [ tclTHENS (cut (mk_gt kk dd))
		[tclTHENLIST [
		  (intros_using [aux2;aux1]);
		  (generalize_tac
		    [mkApp (Lazy.force coq_OMEGA4,
                      [| dd;kk;eq2;mkVar aux1; mkVar aux2 |])]);
		  (clear [aux1;aux2]);
		  unfold sp_not;
		  (intros_using [aux]);
		  resolve_id aux;
		  mk_then tac;
		  assumption ] ;
		 tclTHENLIST [
		   unfold sp_Zgt;
		   simpl_in_concl;
		   reflexivity ] ];
              tclTHENLIST [
		unfold sp_Zgt;
                simpl_in_concl;
		reflexivity ] ]
      | EXACT_DIVIDE (e1,k) :: l ->
	  let id = hyp_of_tag e1.id in
	  let e2 =  map_eq_afine (fun c -> c / k) e1 in
	  let eq1 = val_of(decompile e1)
	  and eq2 = val_of(decompile e2) in
	  let kk = mk_integer k in
	  let state_eq = mk_eq eq1 (mk_times eq2 kk) in
	  if e1.kind == DISE then
            let tac = scalar_norm [P_APP 3] e2.body in
            tclTHENS
	      (cut state_eq)
	      [tclTHENLIST [
		(intros_using [aux1]);
		(generalize_tac
		  [mkApp (Lazy.force coq_OMEGA18,
                    [| eq1;eq2;kk;mkVar aux1; mkVar id |])]);
		(clear [aux1;id]);
		(intros_using [id]);
		(loop l) ];
	       tclTHEN (mk_then tac) reflexivity ]
	  else
            let tac = scalar_norm [P_APP 3] e2.body in
            tclTHENS (cut state_eq)
	      [
		tclTHENS
		 (cut (mk_gt kk izero))
		 [tclTHENLIST [
		   (intros_using [aux2;aux1]);
		   (generalize_tac
		     [mkApp (Lazy.force coq_OMEGA3,
		       [| eq1; eq2; kk; mkVar aux2; mkVar aux1;mkVar id|])]);
		   (clear [aux1;aux2;id]);
		   (intros_using [id]);
		   (loop l) ];
		  tclTHENLIST [
		    unfold sp_Zgt;
                    simpl_in_concl;
		    reflexivity ] ];
		tclTHEN (mk_then tac) reflexivity ]
      | (MERGE_EQ(e3,e1,e2)) :: l ->
	  let id = new_identifier () in
	  tag_hypothesis id e3;
	  let id1 = hyp_of_tag e1.id
	  and id2 = hyp_of_tag e2 in
	  let eq1 = val_of(decompile e1)
	  and eq2 = val_of (decompile (negate_eq e1)) in
	  let tac =
	    clever_rewrite [P_APP 3] [[P_APP 1]]
	      (Lazy.force coq_fast_Zopp_eq_mult_neg_1) ::
            scalar_norm [P_APP 3] e1.body
	  in
	  tclTHENS
	    (cut (mk_eq eq1 (mk_inv eq2)))
	    [tclTHENLIST [
	      (intros_using [aux]);
	      (generalize_tac [mkApp (Lazy.force coq_OMEGA8,
	        [| eq1;eq2;mkVar id1;mkVar id2; mkVar aux|])]);
	      (clear [id1;id2;aux]);
	      (intros_using [id]);
	      (loop l) ];
            tclTHEN (mk_then tac) reflexivity]

      | STATE {st_new_eq=e;st_def=def;st_orig=orig;st_coef=m;st_var=v} :: l ->
	  let id = new_identifier ()
	  and id2 = hyp_of_tag orig.id in
	  tag_hypothesis id e.id;
	  let eq1 = val_of(decompile def)
	  and eq2 = val_of(decompile orig) in
	  let vid = unintern_id v in
	  let theorem =
            mkApp (Lazy.force coq_ex, [|
		      Lazy.force coq_Z;
		      mkLambda
			(Name vid,
			 Lazy.force coq_Z,
			 mk_eq (mkRel 1) eq1) |])
	  in
	  let mm = mk_integer m in
	  let p_initial = [P_APP 2;P_TYPE] in
	  let tac =
            clever_rewrite (P_APP 1 :: P_APP 1 :: P_APP 2 :: p_initial)
              [[P_APP 1]] (Lazy.force coq_fast_Zopp_eq_mult_neg_1) ::
            shuffle_mult_right p_initial
              orig.body m ({c= negone;v= v}::def.body) in
	  tclTHENS
	    (cut theorem)
	    [tclTHENLIST [
	      (intros_using [aux]);
	      (elim_id aux);
	      (clear [aux]);
	      (intros_using [vid; aux]);
	      (generalize_tac
		[mkApp (Lazy.force coq_OMEGA9,
		  [| mkVar vid;eq2;eq1;mm; mkVar id2;mkVar aux |])]);
	      mk_then tac;
	      (clear [aux]);
	      (intros_using [id]);
	      (loop l) ];
            tclTHEN (exists_tac eq1) reflexivity ]
      | SPLIT_INEQ(e,(e1,act1),(e2,act2)) :: l ->
	  let id1 = new_identifier ()
	  and id2 = new_identifier () in
	  tag_hypothesis id1 e1; tag_hypothesis id2 e2;
	  let id = hyp_of_tag e.id in
	  let tac1 = norm_add [P_APP 2;P_TYPE] e.body in
	  let tac2 = scalar_norm_add [P_APP 2;P_TYPE] e.body in
	  let eq = val_of(decompile e) in
	  tclTHENS
	    (simplest_elim (applist (Lazy.force coq_OMEGA19, [eq; mkVar id])))
	    [tclTHENLIST [ mk_then tac1; (intros_using [id1]); (loop act1) ];
             tclTHENLIST [ mk_then tac2; (intros_using [id2]); (loop act2) ]]
      | SUM(e3,(k1,e1),(k2,e2)) :: l ->
	  let id = new_identifier () in
	  tag_hypothesis id e3;
	  let id1 = hyp_of_tag e1.id
	  and id2 = hyp_of_tag e2.id in
	  let eq1 = val_of(decompile e1)
	  and eq2 = val_of(decompile e2) in
	  if k1 =? one && e2.kind == EQUA then
            let tac_thm =
              match e1.kind with
		| EQUA -> Lazy.force coq_OMEGA5
		| INEQ -> Lazy.force coq_OMEGA6
		| DISE -> Lazy.force coq_OMEGA20
	    in
            let kk = mk_integer k2 in
            let p_initial =
              if e1.kind == DISE then [P_APP 1; P_TYPE] else [P_APP 2; P_TYPE] in
            let tac = shuffle_mult_right p_initial e1.body k2 e2.body in
            tclTHENLIST [
	      (generalize_tac
                [mkApp (tac_thm, [| eq1; eq2; kk; mkVar id1; mkVar id2 |])]);
	      mk_then tac;
	      (intros_using [id]);
	      (loop l)
            ]
	  else
            let kk1 = mk_integer k1
	    and kk2 = mk_integer k2 in
	    let p_initial = [P_APP 2;P_TYPE] in
	    let tac= shuffle_mult p_initial k1 e1.body k2 e2.body in
            tclTHENS (cut (mk_gt kk1 izero))
	      [tclTHENS
		 (cut (mk_gt kk2 izero))
		 [tclTHENLIST [
		   (intros_using [aux2;aux1]);
		   (generalize_tac
		     [mkApp (Lazy.force coq_OMEGA7, [|
		       eq1;eq2;kk1;kk2;
		       mkVar aux1;mkVar aux2;
		       mkVar id1;mkVar id2 |])]);
		   (clear [aux1;aux2]);
		   mk_then tac;
		   (intros_using [id]);
		   (loop l) ];
		 tclTHENLIST [
		   unfold sp_Zgt;
                   simpl_in_concl;
		   reflexivity ] ];
	      tclTHENLIST [
		unfold sp_Zgt;
                simpl_in_concl;
		reflexivity ] ]
      | CONSTANT_NOT_NUL(e,k) :: l ->
	  tclTHEN ((generalize_tac [mkVar (hyp_of_tag e)])) Equality.discrConcl
      | CONSTANT_NUL(e) :: l ->
	  tclTHEN (resolve_id (hyp_of_tag e)) reflexivity
      | CONSTANT_NEG(e,k) :: l ->
	  tclTHENLIST [
	    (generalize_tac [mkVar (hyp_of_tag e)]);
            unfold sp_Zle;
	    simpl_in_concl;
	    unfold sp_not;
	    (intros_using [aux]);
	    resolve_id aux;
	    reflexivity
          ]
      | _ -> Proofview.tclUNIT ()
  in
  loop

let normalize sigma p_initial t =
  let (tac,t') = transform sigma p_initial t in
  let (tac',t'') = condense p_initial t' in
  let (tac'',t''') = clear_zero p_initial t'' in
  tac @ tac' @ tac'' , t'''

let normalize_equation sigma id flag theorem pos t t1 t2 (tactic,defs) =
  let p_initial = [P_APP pos ;P_TYPE] in
  let (tac,t') = normalize sigma p_initial t in
  let shift_left =
    tclTHEN
      (generalize_tac [mkApp (theorem, [| t1; t2; mkVar id |]) ])
      (tclTRY (clear [id]))
  in
  if not (List.is_empty tac) then
    let id' = new_identifier () in
    ((id',(tclTHENLIST [ shift_left; mk_then tac; (intros_using [id']) ]))
          :: tactic,
     compile id' flag t' :: defs)
  else
    (tactic,defs)

let destructure_omega env sigma tac_def (id,c) =
  if String.equal (atompart_of_id id) "State" then
    tac_def
  else
    try match destructurate_prop sigma c with
      | Kapp(Eq,[typ;t1;t2])
        when begin match destructurate_type env sigma typ with Kapp(Z,[]) -> true | _ -> false end ->
	  let t = mk_plus t1 (mk_inv t2) in
	  normalize_equation sigma
	    id EQUA (Lazy.force coq_Zegal_left) 2 t t1 t2 tac_def
      | Kapp(Zne,[t1;t2]) ->
	  let t = mk_plus t1 (mk_inv t2) in
	  normalize_equation sigma
	    id DISE (Lazy.force coq_Zne_left) 1 t t1 t2 tac_def
      | Kapp(Zle,[t1;t2]) ->
	  let t = mk_plus t2 (mk_inv t1) in
	  normalize_equation sigma
	    id INEQ (Lazy.force coq_Zle_left) 2 t t1 t2 tac_def
      | Kapp(Zlt,[t1;t2]) ->
	  let t = mk_plus (mk_plus t2 (mk_integer negone)) (mk_inv t1) in
	  normalize_equation sigma
	    id INEQ (Lazy.force coq_Zlt_left) 2 t t1 t2 tac_def
      | Kapp(Zge,[t1;t2]) ->
	  let t = mk_plus t1 (mk_inv t2) in
	  normalize_equation sigma
	    id INEQ (Lazy.force coq_Zge_left) 2 t t1 t2 tac_def
      | Kapp(Zgt,[t1;t2]) ->
	  let t = mk_plus (mk_plus t1 (mk_integer negone)) (mk_inv t2) in
	  normalize_equation sigma
	    id INEQ (Lazy.force coq_Zgt_left) 2 t t1 t2 tac_def
      | _ -> tac_def
    with e when catchable_exception e -> tac_def

let reintroduce id =
  (* [id] cannot be cleared if dependent: protect it by a try *)
  tclTHEN (tclTRY (clear [id])) (intro_using id)


open Proofview.Notations

let coq_omega =
  Proofview.Goal.enter begin fun gl ->
  clear_constr_tables ();
  let hyps_types = Tacmach.New.pf_hyps_types gl in
  let destructure_omega = Tacmach.New.pf_apply destructure_omega gl in
  let tactic_normalisation, system =
    List.fold_left destructure_omega ([],[]) hyps_types in
  let prelude,sys =
    List.fold_left
      (fun (tac,sys) (t,(v,th,b)) ->
	 if b then
           let id = new_identifier () in
           let i = new_id () in
           tag_hypothesis id i;
           (tclTHENLIST [
	     (simplest_elim (applist (Lazy.force coq_intro_Z, [t])));
	     (intros_using [v; id]);
	     (elim_id id);
	     (clear [id]);
	     (intros_using [th;id]);
	     tac ]),
           {kind = INEQ;
	    body = [{v=intern_id v; c=one}];
            constant = zero; id = i} :: sys
	 else
           (tclTHENLIST [
	     (simplest_elim (applist (Lazy.force coq_new_var, [t])));
	     (intros_using [v;th]);
	     tac ]),
           sys)
      (Proofview.tclUNIT (),[]) (dump_tables ())
  in
  let system = system @ sys in
  if !display_system_flag then display_system display_var system;
  if !old_style_flag then begin
    try
      let _ = simplify (new_id,new_var_num,display_var) false system in
      Proofview.tclUNIT ()
    with UNSOLVABLE ->
      let _,path = depend [] [] (history ()) in
      if !display_action_flag then display_action display_var path;
      (tclTHEN prelude (replay_history tactic_normalisation path))
  end else begin
    try
      let path = simplify_strong (new_id,new_var_num,display_var) system in
      if !display_action_flag then display_action display_var path;
      tclTHEN prelude (replay_history tactic_normalisation path)
    with NO_CONTRADICTION -> tclZEROMSG (Pp.str"Omega can't solve this system")
  end
  end

let coq_omega = coq_omega

let nat_inject =
  Proofview.Goal.enter begin fun gl ->
  let is_conv = Tacmach.New.pf_apply Reductionops.is_conv gl in
  let rec explore p t : unit Proofview.tactic =
    Proofview.tclEVARMAP >>= fun sigma ->
    try match destructurate_term sigma t with
      | Kapp(Plus,[t1;t2]) ->
          tclTHENLIST [
	    (clever_rewrite_gen p (mk_plus (mk_inj t1) (mk_inj t2))
              ((Lazy.force coq_inj_plus),[t1;t2]));
	    (explore (P_APP 1 :: p) t1);
	    (explore (P_APP 2 :: p) t2)
          ]
      | Kapp(Mult,[t1;t2]) ->
          tclTHENLIST [
	    (clever_rewrite_gen p (mk_times (mk_inj t1) (mk_inj t2))
              ((Lazy.force coq_inj_mult),[t1;t2]));
	    (explore (P_APP 1 :: p) t1);
	    (explore (P_APP 2 :: p) t2)
          ]
      | Kapp(Minus,[t1;t2]) ->
          let id = new_identifier () in
          tclTHENS
            (tclTHEN
	       (simplest_elim (applist (Lazy.force coq_le_gt_dec, [t2;t1])))
	       (intros_using [id]))
	    [
	      tclTHENLIST [
	        (clever_rewrite_gen p
		  (mk_minus (mk_inj t1) (mk_inj t2))
                  ((Lazy.force coq_inj_minus1),[t1;t2;mkVar id]));
		(loop [id,mkApp (Lazy.force coq_le, [| t2;t1 |])]);
		(explore (P_APP 1 :: p) t1);
		(explore (P_APP 2 :: p) t2) ];
	      (tclTHEN
		 (clever_rewrite_gen p (mk_integer zero)
                    ((Lazy.force coq_inj_minus2),[t1;t2;mkVar id]))
		 (loop [id,mkApp (Lazy.force coq_gt, [| t2;t1 |])]))
	    ]
      | Kapp(S,[t']) ->
          let rec is_number t =
            try match destructurate_term sigma t with
		Kapp(S,[t]) -> is_number t
              | Kapp(O,[]) -> true
              | _ -> false
            with e when catchable_exception e -> false
	  in
          let rec loop p t : unit Proofview.tactic =
            try match destructurate_term sigma t with
		Kapp(S,[t]) ->
                  (tclTHEN
                     (clever_rewrite_gen p
			(mkApp (Lazy.force coq_Zsucc, [| mk_inj t |]))
			((Lazy.force coq_inj_S),[t]))
		     (loop (P_APP 1 :: p) t))
              | _ -> explore p t
            with e when catchable_exception e -> explore p t
	  in
          if is_number t' then focused_simpl p else loop p t
      | Kapp(Pred,[t]) ->
          let t_minus_one =
	    mkApp (Lazy.force coq_minus, [| t;
		      mkApp (Lazy.force coq_S, [| Lazy.force coq_O |]) |]) in
          tclTHEN
            (clever_rewrite_gen_nat (P_APP 1 :: p) t_minus_one
               ((Lazy.force coq_pred_of_minus),[t]))
            (explore p t_minus_one)
      | Kapp(O,[]) -> focused_simpl p
      | _ -> Proofview.tclUNIT ()
    with e when catchable_exception e -> Proofview.tclUNIT ()

  and loop = function
    | [] -> Proofview.tclUNIT ()
    | (i,t)::lit ->
        Proofview.tclEVARMAP >>= fun sigma ->
	  begin try match destructurate_prop sigma t with
              Kapp(Le,[t1;t2]) ->
		tclTHENLIST [
		  (generalize_tac
		    [mkApp (Lazy.force coq_inj_le, [| t1;t2;mkVar i |]) ]);
		  (explore [P_APP 1; P_TYPE] t1);
		  (explore [P_APP 2; P_TYPE] t2);
		  (reintroduce i);
		  (loop lit)
                ]
            | Kapp(Lt,[t1;t2]) ->
		tclTHENLIST [
		  (generalize_tac
		    [mkApp (Lazy.force coq_inj_lt, [| t1;t2;mkVar i |]) ]);
		  (explore [P_APP 1; P_TYPE] t1);
		  (explore [P_APP 2; P_TYPE] t2);
		  (reintroduce i);
		  (loop lit)
                ]
            | Kapp(Ge,[t1;t2]) ->
		tclTHENLIST [
		  (generalize_tac
		    [mkApp (Lazy.force coq_inj_ge, [| t1;t2;mkVar i |]) ]);
		  (explore [P_APP 1; P_TYPE] t1);
		  (explore [P_APP 2; P_TYPE] t2);
		  (reintroduce i);
		  (loop lit)
                ]
            | Kapp(Gt,[t1;t2]) ->
		tclTHENLIST [
		  (generalize_tac
                    [mkApp (Lazy.force coq_inj_gt, [| t1;t2;mkVar i |]) ]);
		  (explore [P_APP 1; P_TYPE] t1);
		  (explore [P_APP 2; P_TYPE] t2);
		  (reintroduce i);
		  (loop lit)
                ]
            | Kapp(Neq,[t1;t2]) ->
		tclTHENLIST [
		  (generalize_tac
		    [mkApp (Lazy.force coq_inj_neq, [| t1;t2;mkVar i |]) ]);
		  (explore [P_APP 1; P_TYPE] t1);
		  (explore [P_APP 2; P_TYPE] t2);
		  (reintroduce i);
		  (loop lit)
                ]
            | Kapp(Eq,[typ;t1;t2]) ->
		if is_conv typ (Lazy.force coq_nat) then
                  tclTHENLIST [
		    (generalize_tac
		      [mkApp (Lazy.force coq_inj_eq, [| t1;t2;mkVar i |]) ]);
		    (explore [P_APP 2; P_TYPE] t1);
		    (explore [P_APP 3; P_TYPE] t2);
		    (reintroduce i);
		    (loop lit)
                  ]
		else loop lit
	    | _ -> loop lit
	  with e when catchable_exception e -> loop lit end
  in
  let hyps_types = Tacmach.New.pf_hyps_types gl in
  loop (List.rev hyps_types)
  end

let dec_binop = function
  | Zne -> coq_dec_Zne
  | Zle -> coq_dec_Zle
  | Zlt -> coq_dec_Zlt
  | Zge -> coq_dec_Zge
  | Zgt -> coq_dec_Zgt
  | Le -> coq_dec_le
  | Lt -> coq_dec_lt
  | Ge -> coq_dec_ge
  | Gt -> coq_dec_gt
  | _ -> raise Not_found

let not_binop = function
  | Zne -> coq_not_Zne
  | Zle -> coq_Znot_le_gt
  | Zlt -> coq_Znot_lt_ge
  | Zge -> coq_Znot_ge_lt
  | Zgt -> coq_Znot_gt_le
  | Le -> coq_not_le
  | Lt -> coq_not_lt
  | Ge -> coq_not_ge
  | Gt -> coq_not_gt
  | _ -> raise Not_found

(** A decidability check : for some [t], could we build a term
    of type [decidable t] (i.e. [t\/~t]) ? Otherwise, we raise
    [Undecidable]. Note that a successful check implies that
    [t] has type Prop.
*)

exception Undecidable

let rec decidability env sigma t =
  match destructurate_prop sigma t with
    | Kapp(Or,[t1;t2]) ->
	mkApp (Lazy.force coq_dec_or, [| t1; t2;
                  decidability env sigma t1; decidability env sigma t2 |])
    | Kapp(And,[t1;t2]) ->
	mkApp (Lazy.force coq_dec_and, [| t1; t2;
                  decidability env sigma t1; decidability env sigma t2 |])
    | Kapp(Iff,[t1;t2]) ->
	mkApp (Lazy.force coq_dec_iff, [| t1; t2;
                  decidability env sigma t1; decidability env sigma t2 |])
    | Kimp(t1,t2) ->
        (* This is the only situation where it's not obvious that [t]
	   is in Prop. The recursive call on [t2] will ensure that. *)
        mkApp (Lazy.force coq_dec_imp,
                 [| t1; t2; decidability env sigma t1; decidability env sigma t2 |])
    | Kapp(Not,[t1]) ->
        mkApp (Lazy.force coq_dec_not, [| t1; decidability env sigma t1 |])
    | Kapp(Eq,[typ;t1;t2]) ->
        begin match destructurate_type env sigma typ with
          | Kapp(Z,[]) ->  mkApp (Lazy.force coq_dec_eq, [| t1;t2 |])
          | Kapp(Nat,[]) ->  mkApp (Lazy.force coq_dec_eq_nat, [| t1;t2 |])
          | _ -> raise Undecidable
	end
    | Kapp(op,[t1;t2]) ->
        (try mkApp (Lazy.force (dec_binop op), [| t1; t2 |])
	 with Not_found -> raise Undecidable)
    | Kapp(False,[]) -> Lazy.force coq_dec_False
    | Kapp(True,[]) -> Lazy.force coq_dec_True
    | _ -> raise Undecidable

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)

let onClearedName id tac =
  (* We cannot ensure that hyps can be cleared (because of dependencies), *)
  (* so renaming may be necessary *)
  tclTHEN
    (tclTRY (clear [id]))
    (Proofview.Goal.nf_enter begin fun gl ->
     let id = fresh_id Id.Set.empty id gl in
     tclTHEN (introduction id) (tac id)
    end)

let onClearedName2 id tac =
  tclTHEN
    (tclTRY (clear [id]))
    (Proofview.Goal.nf_enter begin fun gl ->
     let id1 = fresh_id Id.Set.empty (add_suffix id "_left") gl in
     let id2 = fresh_id Id.Set.empty (add_suffix id "_right") gl in
      tclTHENLIST [ introduction id1; introduction id2; tac id1 id2 ]
    end)

let destructure_hyps =
  Proofview.Goal.enter begin fun gl ->
  let type_of = Tacmach.New.pf_unsafe_type_of gl in
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let decidability = decidability env sigma in
  let rec loop = function
    | [] -> (tclTHEN nat_inject coq_omega)
    | LocalDef (i,body,typ) :: lit when !letin_flag ->
       Proofview.tclEVARMAP >>= fun sigma ->
       begin
         try
           match destructurate_type env sigma typ with
           | Kapp(Nat,_) | Kapp(Z,_) ->
              let hid = fresh_id Id.Set.empty (add_suffix i "_eqn") gl in
              let hty = mk_gen_eq typ (mkVar i) body in
              tclTHEN
                (assert_by (Name hid) hty reflexivity)
                (loop (LocalAssum (hid, hty) :: lit))
           | _ -> loop lit
         with e when catchable_exception e -> loop lit
       end
    | decl :: lit -> (* variable without body (or !letin_flag isn't set) *)
       let i = NamedDecl.get_id decl in
       Proofview.tclEVARMAP >>= fun sigma ->
	  begin try match destructurate_prop sigma (NamedDecl.get_type decl) with
	  | Kapp(False,[]) -> elim_id i
          | Kapp((Zle|Zge|Zgt|Zlt|Zne),[t1;t2]) -> loop lit
          | Kapp(Or,[t1;t2]) ->
              (tclTHENS
                 (elim_id i)
                 [ onClearedName i (fun i -> (loop (LocalAssum (i,t1)::lit)));
                   onClearedName i (fun i -> (loop (LocalAssum (i,t2)::lit))) ])
          | Kapp(And,[t1;t2]) ->
              tclTHEN
		(elim_id i)
		(onClearedName2 i (fun i1 i2 ->
		  loop (LocalAssum (i1,t1) :: LocalAssum (i2,t2) :: lit)))
          | Kapp(Iff,[t1;t2]) ->
	      tclTHEN
		(elim_id i)
		(onClearedName2 i (fun i1 i2 ->
		  loop (LocalAssum (i1,mkArrow t1 t2) :: LocalAssum (i2,mkArrow t2 t1) :: lit)))
          | Kimp(t1,t2) ->
	      (* t1 and t2 might be in Type rather than Prop.
		 For t1, the decidability check will ensure being Prop. *)
              if Termops.is_Prop sigma (type_of t2)
              then
		let d1 = decidability t1 in
		tclTHENLIST [
		  (generalize_tac [mkApp (Lazy.force coq_imp_simp,
                                                               [| t1; t2; d1; mkVar i|])]);
		  (onClearedName i (fun i ->
		    (loop (LocalAssum (i,mk_or (mk_not t1) t2) :: lit))))
                ]
              else
		loop lit
          | Kapp(Not,[t]) ->
              begin match destructurate_prop sigma t with
		Kapp(Or,[t1;t2]) ->
                  tclTHENLIST [
		    (generalize_tac
                                            [mkApp (Lazy.force coq_not_or,[| t1; t2; mkVar i |])]);
		    (onClearedName i (fun i ->
                      (loop (LocalAssum (i,mk_and (mk_not t1) (mk_not t2)) :: lit))))
                  ]
	      | Kapp(And,[t1;t2]) ->
		  let d1 = decidability t1 in
                  tclTHENLIST [
		    (generalize_tac
		                            [mkApp (Lazy.force coq_not_and,
				                    [| t1; t2; d1; mkVar i |])]);
		    (onClearedName i (fun i ->
                      (loop (LocalAssum (i,mk_or (mk_not t1) (mk_not t2)) :: lit))))
                  ]
	      | Kapp(Iff,[t1;t2]) ->
		  let d1 = decidability t1 in
		  let d2 = decidability t2 in
                  tclTHENLIST [
		    (generalize_tac
		                            [mkApp (Lazy.force coq_not_iff,
				                    [| t1; t2; d1; d2; mkVar i |])]);
		    (onClearedName i (fun i ->
                      (loop (LocalAssum (i, mk_or (mk_and t1 (mk_not t2))
				                  (mk_and (mk_not t1) t2)) :: lit))))
                  ]
	      | Kimp(t1,t2) ->
		    (* t2 must be in Prop otherwise ~(t1->t2) wouldn't be ok.
		       For t1, being decidable implies being Prop. *)
		  let d1 = decidability t1 in
                  tclTHENLIST [
		    (generalize_tac
		                            [mkApp (Lazy.force coq_not_imp,
				                    [| t1; t2; d1; mkVar i |])]);
		    (onClearedName i (fun i ->
                      (loop (LocalAssum (i,mk_and t1 (mk_not t2)) :: lit))))
                  ]
	      | Kapp(Not,[t]) ->
		  let d = decidability t in
                  tclTHENLIST [
		    (generalize_tac
			                    [mkApp (Lazy.force coq_not_not, [| t; d; mkVar i |])]);
		    (onClearedName i (fun i -> (loop (LocalAssum (i,t) :: lit))))
                  ]
	      | Kapp(op,[t1;t2]) ->
		  (try
		     let thm = not_binop op in
                     tclTHENLIST [
		       (generalize_tac
			                       [mkApp (Lazy.force thm, [| t1;t2;mkVar i|])]);
		       (onClearedName i (fun _ -> loop lit))
                     ]
		   with Not_found -> loop lit)
	      | Kapp(Eq,[typ;t1;t2]) ->
                  if !old_style_flag then begin
                    match destructurate_type env sigma typ with
		    | Kapp(Nat,_) ->
                        tclTHENLIST [
			  (simplest_elim
			     (mkApp
                                (Lazy.force coq_not_eq, [|t1;t2;mkVar i|])));
			  (onClearedName i (fun _ -> loop lit))
                        ]
		    | Kapp(Z,_) ->
                        tclTHENLIST [
			  (simplest_elim
			     (mkApp
				(Lazy.force coq_not_Zeq, [|t1;t2;mkVar i|])));
			  (onClearedName i (fun _ -> loop lit))
                        ]
		    | _ -> loop lit
                  end else begin
                    match destructurate_type env sigma typ with
		    | Kapp(Nat,_) ->
                        (tclTHEN
			   (convert_hyp_no_check (NamedDecl.set_type (mkApp (Lazy.force coq_neq, [| t1;t2|]))
                                                                     decl))
			   (loop lit))
		    | Kapp(Z,_) ->
                        (tclTHEN
			   (convert_hyp_no_check (NamedDecl.set_type (mkApp (Lazy.force coq_Zne, [| t1;t2|]))
                                                                     decl))
			   (loop lit))
		    | _ -> loop lit
                  end
	      | _ -> loop lit
              end
          | _ -> loop lit
	    with
	    | Undecidable -> loop lit
	    | e when catchable_exception e -> loop lit
	  end
    in
    let hyps = Proofview.Goal.hyps gl in
    loop hyps
  end

let destructure_goal =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let decidability = decidability env sigma in
    let rec loop t =
      Proofview.tclEVARMAP >>= fun sigma ->
      let prop () = Proofview.tclUNIT (destructurate_prop sigma t) in
      Proofview.V82.wrap_exceptions prop >>= fun prop ->
      match prop with
      | Kapp(Not,[t]) ->
          (tclTHEN
	     (tclTHEN (unfold sp_not) intro)
	     destructure_hyps)
      | Kimp(a,b) -> (tclTHEN intro (loop b))
      | Kapp(False,[]) -> destructure_hyps
      | _ ->
	  let goal_tac =
	    try
	      let dec = decidability t in
	      tclTHEN
                (Proofview.Goal.nf_enter begin fun gl ->
		                         refine_app gl (mkApp (Lazy.force coq_dec_not_not, [| t; dec |]))
		                         end)
	        intro
	    with Undecidable -> Tactics.elim_type (Lazy.force coq_False)
	    | e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
	  in
	  tclTHEN goal_tac destructure_hyps
    in
    (loop concl)
  end

let destructure_goal = destructure_goal

let omega_solver =
  Proofview.tclUNIT () >>= fun () -> (* delay for [check_required_library] *)
  Coqlib.check_required_library ["Coq";"omega";"Omega"];
  reset_all ();
  destructure_goal
