(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(**************************************************************************)
(*                                                                        *)
(* Omega: a solver of quantifier-free problems in Presburger Arithmetic   *)
(*                                                                        *)
(* Pierre Cr�gut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(* $Id$ *)

open Util
open Pp
open Reduction
open Proof_type
open Ast
open Identifier
open Names
open Term
open Environ
open Sign
open Inductive
open Tacmach
open Evar_refiner
open Tactics
open Clenv
open Logic
open Omega

(* Added by JCF, 09/03/98 *)

let elim_id id gl = simplest_elim (pf_global gl id) gl
let resolve_id id gl = apply (pf_global gl id) gl

let timing timer_name f arg = f arg

let display_time_flag = ref false
let display_system_flag = ref false
let display_action_flag = ref false
let old_style_flag = ref false

let all_time        = timing "Omega     "
let solver_time     = timing "Solver    "
let exact_time      = timing "Rewrites  "
let elim_time       = timing "Elim      "
let simpl_time      = timing "Simpl     "
let generalize_time = timing "Generalize"

let new_identifier = 
  let cpt = ref 0 in 
  (fun () -> let s = "Omega" ^ string_of_int !cpt in incr cpt; id_of_string s)

let new_identifier_state = 
  let cpt = ref 0 in 
  (fun () -> let s = make_ident "State" (Some !cpt) in incr cpt; s)

let new_identifier_var = 
  let cpt = ref 0 in 
  (fun () -> let s = "Zvar" ^ string_of_int !cpt in incr cpt; id_of_string s)

let rec mk_then = 
  function [t] -> t | (t::l) -> (tclTHEN (t) (mk_then l)) | [] -> tclIDTAC

let collect_com lbind = 
  map_succeed (function (Com,c)->c | _ -> failwith "Com") lbind

(*** EST-CE QUE CES FONCTIONS NE SONT PAS AILLEURS DANS LE CODE ?? *)

let make_clenv_binding_apply wc (c,t) lbind = 
  let largs = collect_com lbind in 
  let lcomargs = List.length largs in 
  if lcomargs = List.length lbind then 
    let clause = mk_clenv_from wc (c,t) in
    clenv_constrain_missing_args largs clause
  else if lcomargs = 0 then 
    let clause = mk_clenv_rename_from wc (c,t) in
    clenv_match_args lbind clause
  else 
    errorlabstrm "make_clenv_bindings"
      [<'sTR "Cannot mix bindings and free associations">]

let resolve_with_bindings_tac  (c,lbind) gl = 
  let (wc,kONT) = startWalk gl in
  let t = w_hnf_constr wc (w_type_of wc c) in 
  let clause = make_clenv_binding_apply wc (c,t) lbind in 
  res_pf kONT clause gl

let reduce_to_mind gl t = 
  let rec elimrec t l =
    let c, args = whd_stack t in
    match kind_of_term c, args with
    | (IsMutInd _,_) -> (c,Environ.it_mkProd_or_LetIn t l)
    | (IsConst _,_) -> 
	(try 
	   let t' = pf_nf_betaiota gl (pf_one_step_reduce gl t) in elimrec t' l
         with e when catchable_exception e -> 
	   errorlabstrm "tactics__reduce_to_mind"
             [< 'sTR"Not an inductive product" >])
    | (IsMutCase _,_) ->
	(try 
	   let t' = pf_nf_betaiota gl (pf_one_step_reduce gl t) in elimrec t' l
         with e when catchable_exception e -> 
	   errorlabstrm "tactics__reduce_to_mind"
             [< 'sTR"Not an inductive product" >])
    | (IsCast (c,_),[]) -> elimrec c l
    | (IsProd (n,ty,t'),[]) -> 
	let ty' = Retyping.get_assumption_of (Global.env()) Evd.empty ty in
	elimrec t' ((n,None,ty')::l)
    | (IsLetIn (n,b,ty,t'),[]) ->
	let ty' = Retyping.get_assumption_of (Global.env()) Evd.empty ty in
	elimrec t' ((n,Some b,ty')::l)
    | _ -> error "Not an inductive product"
  in 
  elimrec t []

let constructor_tac nconstropt i lbind gl = 
  let cl = pf_concl gl in
  let (mind, redcl) = reduce_to_mind gl cl in
  let ((x0,x1),args) as mindspec= destMutInd mind in
  let nconstr = Global.mind_nconstr mindspec
  and sigma = project gl in
  (match nconstropt with 
     | Some expnconstr -> 
	 if expnconstr <> nconstr then
           error "Not the expected number of constructors"
     | _ -> ());
  if i > nconstr then error "Not enough Constructors";
  let c = mkMutConstruct (((x0,x1),i),args) in 
  let resolve_tac = resolve_with_bindings_tac (c,lbind) in
  (tclTHEN (tclTHEN (change_in_concl redcl) intros) resolve_tac) gl

let exists_tac c= constructor_tac (Some 1) 1 [Com,c]
		    
let generalize_tac t = generalize_time (generalize t)
let elim t = elim_time (simplest_elim t)
let exact t = exact_time (Tactics.refine t)

let unfold s = Tactics.unfold_in_concl [[], Lazy.force s]
 
(*** fin de EST-CE QUE CES FONCTIONS NE SONT PAS AILLEURS DANS LE CODE ?? *)
(****************************************************************)

let rev_assoc k =
  let rec loop = function
    | [] -> raise Not_found | (v,k')::_ when k = k' -> v | _ :: l -> loop l 
  in
  loop

let tag_hypothesis,tag_of_hyp, hyp_of_tag =
  let l = ref ([]:(identifier * int) list) in
  (fun h id -> l := (h,id):: !l),
  (fun h -> try List.assoc h !l with Not_found -> failwith "tag_hypothesis"),
  (fun h -> try rev_assoc h !l with Not_found -> failwith "tag_hypothesis")

let hide_constr,find_constr,clear_tables,dump_tables =
  let l = ref ([]:(constr * (identifier * identifier * bool)) list) in
  (fun h id eg b -> l := (h,(id,eg,b)):: !l),
  (fun h -> try List.assoc h !l with Not_found -> failwith "find_contr"),
  (fun () -> l := []),
  (fun () -> !l)

let get_applist = whd_stack

exception Destruct

let dest_const_apply t = 
  let f,args = get_applist t in
  let ref = 
  match kind_of_term f with 
    | IsConst (sp,_)         ->	ConstRef sp
    | IsMutConstruct (csp,_) -> ConstructRef csp
    | IsMutInd (isp,_)       -> IndRef isp
    | _ -> raise Destruct
  in
  Nametab.get_ident ref, args

type result = 
  | Kvar of string
  | Kapp of string * constr list
  | Kimp of constr * constr
  | Kufo

let destructurate t =
  let c, args = get_applist t in
  match kind_of_term c, args with
    | IsConst (sp,_), args ->
	Kapp (string_of_id (basename (Global.sp_of_global (ConstRef sp))),args)
    | IsMutConstruct (csp,_) , args ->
	Kapp (string_of_id (basename (Global.sp_of_global (ConstructRef csp))),
			    args)
    | IsMutInd (isp,_), args ->
	Kapp (string_of_id (basename (Global.sp_of_global (IndRef isp))),args)
    | IsVar id,[] -> Kvar(string_of_id id)
    | IsProd (Anonymous,typ,body), [] -> Kimp(typ,body)
    | IsProd (Name _,_,_),[] -> error "Omega: Not a quantifier-free goal"
    | _ -> Kufo

let recognize_number t =
  let rec loop t =
    let f,l = dest_const_apply t in
    match string_of_id f,l with
      | "xI",[t] -> 1 + 2 * loop t
      | "xO",[t] -> 2 * loop t 
      | "xH",[] -> 1
      | _ -> failwith "not a number" 
  in
  let f,l = dest_const_apply t in
  match string_of_id f,l with
    | "POS",[t] -> loop t | "NEG",[t] -> - (loop t) | "ZERO",[] -> 0
    | _ -> failwith "not a number"
	  
(* Lazy evaluation is used for Coq constants, because this code
 is evaluated before the compiled modules are loaded.
 To use the constant Zplus, one must type "Lazy.force coq_Zplus"
 This is the right way to access to Coq constants in tactics ML code *)

let constant dir s =
  let dir = make_dirpath (List.map id_of_string ("Coq"::dir)) in
  let id = id_of_string s in
  try 
    Declare.global_reference_in_absolute_module dir id
  with Not_found ->
    anomaly ("Coq_omega: cannot find "^
	     (Nametab.string_of_qualid (Nametab.make_qualid dir id)))

let arith_constant dir = constant ("Arith"::dir)
let zarith_constant dir = constant ("ZArith"::dir)
let logic_constant dir = constant ("Logic"::dir)

(* fast_integer *)
let coq_xH = lazy (zarith_constant ["fast_integer"] "xH")
let coq_xO = lazy (zarith_constant ["fast_integer"] "xO")
let coq_xI = lazy (zarith_constant ["fast_integer"] "xI")
let coq_ZERO = lazy (zarith_constant ["fast_integer"] "ZERO")
let coq_POS = lazy (zarith_constant ["fast_integer"] "POS")
let coq_NEG = lazy (zarith_constant ["fast_integer"]  "NEG")
let coq_Z = lazy (zarith_constant ["fast_integer"] "Z")
let coq_relation = lazy (zarith_constant ["fast_integer"] "relation")
let coq_SUPERIEUR = lazy (zarith_constant ["fast_integer"] "SUPERIEUR")
let coq_INFEEIEUR = lazy (zarith_constant ["fast_integer"] "INFERIEUR")
let coq_EGAL = lazy (zarith_constant ["fast_integer"] "EGAL")
let coq_Zplus = lazy (zarith_constant ["fast_integer"] "Zplus")
let coq_Zmult = lazy (zarith_constant ["fast_integer"] "Zmult")
let coq_Zopp = lazy (zarith_constant ["fast_integer"] "Zopp")

(* zarith_aux *)
let coq_Zminus = lazy (zarith_constant ["zarith_aux"] "Zminus")
let coq_Zs = lazy (zarith_constant ["zarith_aux"] "Zs")
let coq_Zgt = lazy (zarith_constant ["zarith_aux"] "Zgt")
let coq_Zle = lazy (zarith_constant ["zarith_aux"] "Zle")
let coq_inject_nat = lazy (zarith_constant ["zarith_aux"] "inject_nat")

(* auxiliary *)
let coq_inj_plus = lazy (zarith_constant ["auxiliary"] "inj_plus")
let coq_inj_mult = lazy (zarith_constant ["auxiliary"] "inj_mult")
let coq_inj_minus1 = lazy (zarith_constant ["auxiliary"] "inj_minus1")
let coq_inj_minus2 = lazy (zarith_constant ["auxiliary"] "inj_minus2")
let coq_inj_S = lazy (zarith_constant ["auxiliary"] "inj_S")
let coq_inj_le = lazy (zarith_constant ["auxiliary"] "inj_le")
let coq_inj_lt = lazy (zarith_constant ["auxiliary"] "inj_lt")
let coq_inj_ge = lazy (zarith_constant ["auxiliary"] "inj_ge")
let coq_inj_gt = lazy (zarith_constant ["auxiliary"] "inj_gt")
let coq_inj_neq = lazy (zarith_constant ["auxiliary"] "inj_neq")
let coq_inj_eq = lazy (zarith_constant ["auxiliary"] "inj_eq")
let coq_pred_of_minus = lazy (arith_constant ["Minus"] "pred_of_minus")
let coq_fast_Zplus_assoc_r = lazy (zarith_constant ["auxiliary"] "fast_Zplus_assoc_r")
let coq_fast_Zplus_assoc_l = lazy (zarith_constant ["auxiliary"] "fast_Zplus_assoc_l")
let coq_fast_Zmult_assoc_r = lazy (zarith_constant ["auxiliary"] "fast_Zmult_assoc_r")
let coq_fast_Zplus_permute = lazy (zarith_constant ["auxiliary"] "fast_Zplus_permute")
let coq_fast_Zplus_sym = lazy (zarith_constant ["auxiliary"] "fast_Zplus_sym")
let coq_fast_Zmult_sym = lazy (zarith_constant ["auxiliary"] "fast_Zmult_sym")
let coq_Zmult_le_approx = lazy (zarith_constant ["auxiliary"] "Zmult_le_approx")
let coq_OMEGA1 = lazy (zarith_constant ["auxiliary"] "OMEGA1")
let coq_OMEGA2 = lazy (zarith_constant ["auxiliary"] "OMEGA2")
let coq_OMEGA3 = lazy (zarith_constant ["auxiliary"] "OMEGA3")
let coq_OMEGA4 = lazy (zarith_constant ["auxiliary"] "OMEGA4")
let coq_OMEGA5 = lazy (zarith_constant ["auxiliary"] "OMEGA5")
let coq_OMEGA6 = lazy (zarith_constant ["auxiliary"] "OMEGA6")
let coq_OMEGA7 = lazy (zarith_constant ["auxiliary"] "OMEGA7")
let coq_OMEGA8 = lazy (zarith_constant ["auxiliary"] "OMEGA8")
let coq_OMEGA9 = lazy (zarith_constant ["auxiliary"] "OMEGA9")
let coq_fast_OMEGA10 = lazy (zarith_constant ["auxiliary"] "fast_OMEGA10")
let coq_fast_OMEGA11 = lazy (zarith_constant ["auxiliary"] "fast_OMEGA11")
let coq_fast_OMEGA12 = lazy (zarith_constant ["auxiliary"] "fast_OMEGA12")
let coq_fast_OMEGA13 = lazy (zarith_constant ["auxiliary"] "fast_OMEGA13")
let coq_fast_OMEGA14 = lazy (zarith_constant ["auxiliary"] "fast_OMEGA14")
let coq_fast_OMEGA15 = lazy (zarith_constant ["auxiliary"] "fast_OMEGA15")
let coq_fast_OMEGA16 = lazy (zarith_constant ["auxiliary"] "fast_OMEGA16")
let coq_OMEGA17 = lazy (zarith_constant ["auxiliary"] "OMEGA17")
let coq_OMEGA18 = lazy (zarith_constant ["auxiliary"] "OMEGA18")
let coq_OMEGA19 = lazy (zarith_constant ["auxiliary"] "OMEGA19")
let coq_OMEGA20 = lazy (zarith_constant ["auxiliary"] "OMEGA20")
let coq_fast_Zred_factor0 = lazy (zarith_constant ["auxiliary"] "fast_Zred_factor0")
let coq_fast_Zred_factor1 = lazy (zarith_constant ["auxiliary"] "fast_Zred_factor1")
let coq_fast_Zred_factor2 = lazy (zarith_constant ["auxiliary"] "fast_Zred_factor2")
let coq_fast_Zred_factor3 = lazy (zarith_constant ["auxiliary"] "fast_Zred_factor3")
let coq_fast_Zred_factor4 = lazy (zarith_constant ["auxiliary"] "fast_Zred_factor4")
let coq_fast_Zred_factor5 = lazy (zarith_constant ["auxiliary"] "fast_Zred_factor5")
let coq_fast_Zred_factor6 = lazy (zarith_constant ["auxiliary"] "fast_Zred_factor6")
let coq_fast_Zmult_plus_distr =
  lazy (zarith_constant ["auxiliary"] "fast_Zmult_plus_distr")
let coq_fast_Zmult_Zopp_left = 
  lazy (zarith_constant ["auxiliary"] "fast_Zmult_Zopp_left")
let coq_fast_Zopp_Zplus = lazy (zarith_constant ["auxiliary"] "fast_Zopp_Zplus")
let coq_fast_Zopp_Zmult_r = lazy (zarith_constant ["auxiliary"] "fast_Zopp_Zmult_r")
let coq_fast_Zopp_one = lazy (zarith_constant ["auxiliary"] "fast_Zopp_one")
let coq_fast_Zopp_Zopp = lazy (zarith_constant ["auxiliary"] "fast_Zopp_Zopp")
let coq_Zegal_left = lazy (zarith_constant ["auxiliary"] "Zegal_left")
let coq_Zne_left = lazy (zarith_constant ["auxiliary"] "Zne_left")
let coq_Zlt_left = lazy (zarith_constant ["auxiliary"] "Zlt_left")
let coq_Zge_left = lazy (zarith_constant ["auxiliary"] "Zge_left")
let coq_Zgt_left = lazy (zarith_constant ["auxiliary"] "Zgt_left")
let coq_Zle_left = lazy (zarith_constant ["auxiliary"] "Zle_left")
let coq_new_var = lazy (zarith_constant ["auxiliary"] "new_var")
let coq_intro_Z = lazy (zarith_constant ["auxiliary"] "intro_Z")

let coq_dec_eq = lazy (zarith_constant ["auxiliary"] "dec_eq")
let coq_dec_Zne = lazy (zarith_constant ["auxiliary"] "dec_Zne")
let coq_dec_Zle = lazy (zarith_constant ["auxiliary"] "dec_Zle")
let coq_dec_Zlt = lazy (zarith_constant ["auxiliary"] "dec_Zlt")
let coq_dec_Zgt = lazy (zarith_constant ["auxiliary"] "dec_Zgt")
let coq_dec_Zge = lazy (zarith_constant ["auxiliary"] "dec_Zge")

let coq_not_Zeq = lazy (zarith_constant ["auxiliary"] "not_Zeq")
let coq_not_Zle = lazy (zarith_constant ["auxiliary"] "not_Zle")
let coq_not_Zlt = lazy (zarith_constant ["auxiliary"] "not_Zlt")
let coq_not_Zge = lazy (zarith_constant ["auxiliary"] "not_Zge")
let coq_not_Zgt = lazy (zarith_constant ["auxiliary"] "not_Zgt")
let coq_neq = lazy (zarith_constant ["auxiliary"] "neq")
let coq_Zne = lazy (zarith_constant ["auxiliary"] "Zne")

(* Peano *)
let coq_le = lazy (constant ["Init";"Peano"] "le")
let coq_gt = lazy (constant ["Init";"Peano"] "gt")

(* Datatypes *)
let coq_nat = lazy (constant ["Init";"Datatypes"] "nat")
let coq_S = lazy (constant ["Init";"Datatypes"] "S")
let coq_O = lazy (constant ["Init";"Datatypes"] "O")

(* Minus *)
let coq_minus = lazy (constant ["Arith";"Minus"] "minus")

(* Compare_dec *)
let coq_le_gt_dec = lazy (constant ["Arith";"Compare_dec"] "le_gt_dec")
let coq_dec_eq_nat = lazy (constant ["Arith";"Peano_dec"] "dec_eq_nat")
let coq_dec_le = lazy (constant ["Arith";"Compare_dec"] "dec_le")
let coq_dec_lt = lazy (constant ["Arith";"Compare_dec"] "dec_lt")
let coq_dec_ge = lazy (constant ["Arith";"Compare_dec"] "dec_ge")
let coq_dec_gt = lazy (constant ["Arith";"Compare_dec"] "dec_gt")
let coq_not_eq = lazy (constant ["Arith";"Compare_dec"] "not_eq")
let coq_not_le = lazy (constant ["Arith";"Compare_dec"] "not_le")
let coq_not_lt = lazy (constant ["Arith";"Compare_dec"] "not_lt")
let coq_not_ge = lazy (constant ["Arith";"Compare_dec"] "not_ge")
let coq_not_gt = lazy (constant ["Arith";"Compare_dec"] "not_gt")

(* Logic *)
open Coqlib
let build_coq_eq = build_coq_eq_data.eq
let coq_eq_ind_r = lazy (constant ["Init"; "Logic"] "eq_ind_r")

let coq_dec_or = lazy (logic_constant ["Decidable"] "dec_or")
let coq_dec_and = lazy (logic_constant ["Decidable"] "dec_and")
let coq_dec_imp = lazy (logic_constant ["Decidable"] "dec_imp")
let coq_dec_not = lazy (logic_constant ["Decidable"] "dec_not")
let coq_dec_False = lazy (logic_constant ["Decidable"] "dec_False")
let coq_dec_not_not = lazy (logic_constant ["Decidable"] "dec_not_not")
let coq_dec_True = lazy (logic_constant ["Decidable"] "dec_True")

let coq_not_or = lazy (logic_constant ["Decidable"] "not_or")
let coq_not_and = lazy (logic_constant ["Decidable"] "not_and")
let coq_not_imp = lazy (logic_constant ["Decidable"] "not_imp")
let coq_not_not = lazy (logic_constant ["Decidable"] "not_not")
let coq_imp_simp = lazy (logic_constant ["Decidable"] "imp_simp")

(* uses build_coq_and, build_coq_not, build_coq_or, build_coq_ex *)


(* Section paths for unfold *)
open Closure
let make_coq_path dir s =
  let dir = make_dirpath (List.map id_of_string ("Coq"::dir)) in
  let id = id_of_string s in
  let ref = 
    try Nametab.locate_in_absolute_module dir id 
    with Not_found ->
      anomaly("Coq_omega: cannot find "^
	      (Nametab.string_of_qualid(Nametab.make_qualid dir id)))
  in
  match ref with
    | ConstRef sp -> EvalConstRef sp
    | _ -> anomaly ("Coq_omega: "^
		    (Nametab.string_of_qualid (Nametab.make_qualid dir id))^
		    " is not a constant")

let sp_Zs = lazy (make_coq_path ["ZArith";"zarith_aux"] "Zs")
let sp_Zminus = lazy (make_coq_path ["ZArith";"zarith_aux"] "Zminus")
let sp_Zle = lazy (make_coq_path ["ZArith";"zarith_aux"] "Zle")
let sp_Zgt = lazy (make_coq_path ["ZArith";"zarith_aux"] "Zgt")
let sp_Zge = lazy (make_coq_path ["ZArith";"zarith_aux"] "Zge")
let sp_Zlt = lazy (make_coq_path ["ZArith";"zarith_aux"] "Zlt")
let sp_not = lazy (make_coq_path ["Init";"Logic"] "not")

let mk_var v = mkVar (id_of_string v)
let mk_plus t1 t2 = mkApp (Lazy.force coq_Zplus, [| t1; t2 |])
let mk_times t1 t2 = mkApp (Lazy.force coq_Zmult, [| t1; t2 |])
let mk_minus t1 t2 = mkApp (Lazy.force coq_Zminus, [| t1;t2 |])
let mk_eq t1 t2 = mkApp (build_coq_eq (), [| Lazy.force coq_Z; t1; t2 |])
let mk_le t1 t2 = mkApp (Lazy.force coq_Zle, [| t1; t2 |])
let mk_gt t1 t2 = mkApp (Lazy.force coq_Zgt, [| t1; t2 |])
let mk_inv t = mkApp (Lazy.force coq_Zopp, [| t |])
let mk_and t1 t2 =  mkApp (build_coq_and (), [| t1; t2 |])
let mk_or t1 t2 =  mkApp (build_coq_or (), [| t1; t2 |])
let mk_not t = mkApp (build_coq_not (), [| t |])
let mk_eq_rel t1 t2 = mkApp (build_coq_eq (),
			      [| Lazy.force coq_relation; t1; t2 |])
let mk_inj t = mkApp (Lazy.force coq_inject_nat, [| t |])

let mk_integer n =
  let rec loop n = 
    if n=1 then Lazy.force coq_xH else 
      mkApp ((if n mod 2 = 0 then Lazy.force coq_xO else Lazy.force coq_xI),
		[| loop (n/2) |])
  in
  if n = 0 then Lazy.force coq_ZERO 
  else mkApp ((if n > 0 then Lazy.force coq_POS else Lazy.force coq_NEG),
		 [| loop (abs n) |])
    
type constr_path =
  | P_APP of int
  (* Abstraction and product *)
  | P_BODY 
  | P_TYPE
  (* Mutcase *)
  | P_BRANCH of int
  | P_ARITY
  | P_ARG

let context operation path (t : constr) =
  let rec loop i p0 t = 
    match (p0,kind_of_term t) with 
      | (p, IsCast (c,t)) -> mkCast (loop i p c,t)
      | ([], _) -> operation i t
      | ((P_APP n :: p),  IsApp (f,v)) ->
(*	  let f,l = get_applist t in   NECESSAIRE ??
	  let v' = Array.of_list (f::l) in  *)
	  let v' = Array.copy v in
	  v'.(n-1) <- loop i p v'.(n-1); mkApp (f, v')
      | ((P_BRANCH n :: p), IsMutCase (ci,q,c,v)) ->
	  (* avant, y avait mkApp... anyway, BRANCH seems nowhere used *)
	  let v' = Array.copy v in
	  v'.(n) <- loop i p v'.(n); (mkMutCase (ci,q,c,v'))
      | ((P_ARITY :: p),  IsApp (f,l)) ->
	  appvect (loop i p f,l)
      | ((P_ARG :: p),  IsApp (f,v)) ->
	  let v' = Array.copy v in
	  v'.(0) <- loop i p v'.(0); mkApp (f,v')
      | (p, IsFix ((_,n as ln),(tys,lna,v))) ->
	  let l = Array.length v in
	  let v' = Array.copy v in
	  v'.(n) <- loop (i+l) p v.(n); (mkFix (ln,(tys,lna,v')))
      | ((P_BODY :: p), IsProd (n,t,c)) ->
	  (mkProd (n,t,loop (i+1) p c))
      | ((P_BODY :: p), IsLambda (n,t,c)) ->
	  (mkLambda (n,t,loop (i+1) p c))
      | ((P_BODY :: p), IsLetIn (n,b,t,c)) ->
	  (mkLetIn (n,b,t,loop (i+1) p c))
      | ((P_TYPE :: p), IsProd (n,t,c)) ->
	  (mkProd (n,loop i p t,c))
      | ((P_TYPE :: p), IsLambda (n,t,c)) ->
	  (mkLambda (n,loop i p t,c))
      | ((P_TYPE :: p), IsLetIn (n,b,t,c)) ->
	  (mkLetIn (n,b,loop i p t,c))
      | (p, _) -> 
	  pPNL [<Printer.prterm t>];
	  failwith ("abstract_path " ^ string_of_int(List.length p)) 
  in
  loop 1 path t

let occurence path (t : constr) =
  let rec loop p0 t = match (p0,kind_of_term t) with
    | (p, IsCast (c,t)) -> loop p c
    | ([], _) -> t
    | ((P_APP n :: p),  IsApp (f,v)) -> loop p v.(n-1)
    | ((P_BRANCH n :: p), IsMutCase (_,_,_,v)) -> loop p v.(n)
    | ((P_ARITY :: p),  IsApp (f,_)) -> loop p f
    | ((P_ARG :: p),  IsApp (f,v)) -> loop p v.(0)
    | (p, IsFix((_,n) ,(_,_,v))) -> loop p v.(n)
    | ((P_BODY :: p), IsProd (n,t,c)) -> loop p c
    | ((P_BODY :: p), IsLambda (n,t,c)) -> loop p c
    | ((P_BODY :: p), IsLetIn (n,b,t,c)) -> loop p c
    | ((P_TYPE :: p), IsProd (n,term,c)) -> loop p term
    | ((P_TYPE :: p), IsLambda (n,term,c)) -> loop p term
    | ((P_TYPE :: p), IsLetIn (n,b,term,c)) -> loop p term
    | (p, _) -> 
	pPNL [<Printer.prterm t>];
	failwith ("occurence " ^ string_of_int(List.length p)) 
  in
  loop path t

let abstract_path typ path t =
  let term_occur = ref (mkRel 0) in
  let abstract = context (fun i t -> term_occur:= t; mkRel i) path t in
  mkLambda (Name (id_of_string "x"), typ, abstract), !term_occur

let focused_simpl path gl =
  let newc = context (fun i t -> pf_nf gl t) (List.rev path) (pf_concl gl) in
  convert_concl newc gl

let focused_simpl path = simpl_time (focused_simpl path)

type oformula =
  | Oplus of oformula * oformula
  | Oinv of  oformula
  | Otimes of oformula * oformula
  | Oatom of  string
  | Oz of int
  | Oufo of constr

let rec oprint = function 
  | Oplus(t1,t2) -> 
      print_string "("; oprint t1; print_string "+"; 
      oprint t2; print_string ")"
  | Oinv t -> print_string "~"; oprint t
  | Otimes (t1,t2) -> 
      print_string "("; oprint t1; print_string "*"; 
      oprint t2; print_string ")"
  | Oatom s -> print_string s
  | Oz i -> print_int i
  | Oufo f -> print_string "?"

let rec weight = function
  | Oatom c -> intern_id c
  | Oz _ -> -1
  | Oinv c -> weight c
  | Otimes(c,_) -> weight c
  | Oplus _ -> failwith "weight"
  | Oufo _ -> -1

let rec val_of = function
  | Oatom c -> (mkVar (id_of_string c))
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
    | _ -> anomaly "compile_equation" 
  in
  loop []

let rec decompile af = 
  let rec loop = function
    | ({v=v; c=n}::r) -> Oplus(Otimes(Oatom (unintern_id v),Oz n),loop r) 
    | [] -> Oz af.constant 
  in
  loop af.body

let mkNewMeta () = mkMeta (Clenv.new_meta())

let clever_rewrite_base_poly typ p result theorem gl = 
  let full = pf_concl gl in
  let (abstracted,occ) = abstract_path typ (List.rev p) full in
  let t = 
    applist
      (mkLambda
	 (Name (id_of_string "P"), 
	  mkArrow typ mkProp,
          mkLambda
	    (Name (id_of_string "H"),
	     applist (mkRel 1,[result]),
	     mkApp (Lazy.force coq_eq_ind_r, 
		       [| typ; result; mkRel 2; mkRel 1; occ; theorem |]))),
       [abstracted]) 
  in
  exact (applist(t,[mkNewMeta()])) gl

let clever_rewrite_base p result theorem gl = 
  clever_rewrite_base_poly (Lazy.force coq_Z) p result theorem gl

let clever_rewrite_base_nat p result theorem gl = 
  clever_rewrite_base_poly (Lazy.force coq_nat) p result theorem gl

let clever_rewrite_gen p result (t,args) = 
  let theorem = applist(t, args) in 
  clever_rewrite_base p result theorem

let clever_rewrite_gen_nat p result (t,args) = 
  let theorem = applist(t, args) in 
  clever_rewrite_base_nat p result theorem

let clever_rewrite p vpath t gl = 
  let full = pf_concl gl in
  let (abstracted,occ) = abstract_path (Lazy.force coq_Z) (List.rev p) full in
  let vargs = List.map (fun p -> occurence p occ) vpath in
  let t' = applist(t, (vargs @ [abstracted])) in
  exact (applist(t',[mkNewMeta()])) gl
    
let rec shuffle p (t1,t2) = 
  match t1,t2 with
    | Oplus(l1,r1), Oplus(l2,r2) ->
	if weight l1 > weight l2 then 
          let (tac,t') = shuffle (P_APP 2 :: p) (r1,t2) in
          (clever_rewrite p [[P_APP 1;P_APP 1]; 
			     [P_APP 1; P_APP 2];[P_APP 2]]
             (Lazy.force coq_fast_Zplus_assoc_r)
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
            (Lazy.force coq_fast_Zplus_assoc_r)
          :: tac, 
          Oplus(l1, t')
	else 
          [clever_rewrite p [[P_APP 1];[P_APP 2]] 
	     (Lazy.force coq_fast_Zplus_sym)],
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
	[focused_simpl p], Oz(t1+t2)
    | t1,t2 ->
	if weight t1 < weight t2 then
          [clever_rewrite p [[P_APP 1];[P_APP 2]] 
	     (Lazy.force coq_fast_Zplus_sym)],
	  Oplus(t2,t1)
	else [],Oplus(t1,t2)
	  
let rec shuffle_mult p_init k1 e1 k2 e2 =
  let rec loop p = function
    | (({c=c1;v=v1}::l1) as l1'),(({c=c2;v=v2}::l2) as l2') ->
	if v1 = v2 then
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
          if k1*c1 + k2 * c2 = 0 then 
            let tac' = 
	      clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 2]]
                (Lazy.force coq_fast_Zred_factor5) in
	    tac :: focused_simpl (P_APP 1::P_APP 2:: p) :: tac' :: 
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
    | [],[] -> [focused_simpl p_init] 
  in
  loop p_init (e1,e2)
    
let rec shuffle_mult_right p_init e1 k2 e2 =
  let rec loop p = function
    | (({c=c1;v=v1}::l1) as l1'),(({c=c2;v=v2}::l2) as l2') ->
	if v1 = v2 then
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
          if c1 + k2 * c2 = 0 then 
            let tac' = 
              clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 2]]
                (Lazy.force coq_fast_Zred_factor5) 
	    in
            tac :: focused_simpl (P_APP 1::P_APP 2:: p) :: tac' :: 
            loop p (l1,l2)
          else tac :: loop (P_APP 2 :: p) (l1,l2)
	else if v1 > v2 then
          clever_rewrite p [[P_APP 1;P_APP 1]; [P_APP 1; P_APP 2];[P_APP 2]]
            (Lazy.force coq_fast_Zplus_assoc_r) ::
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
          (Lazy.force coq_fast_Zplus_assoc_r) ::
        loop (P_APP 2 :: p) (l1,[])
    | [],({c=c2;v=v2}::l2) -> 
        clever_rewrite p [[P_APP 2; P_APP 1; P_APP 1; P_APP 1];
                          [P_APP 2; P_APP 1; P_APP 1; P_APP 2];
                          [P_APP 1];
                          [P_APP 2; P_APP 1; P_APP 2];
                          [P_APP 2; P_APP 2]]
          (Lazy.force coq_fast_OMEGA12) ::
        loop (P_APP 2 :: p) ([],l2)
    | [],[] -> [focused_simpl p_init] 
  in
  loop p_init (e1,e2)

let rec shuffle_cancel p = function 
  | [] -> [focused_simpl p]
  | ({c=c1}::l1) ->
      let tac = 
	clever_rewrite p [[P_APP 1; P_APP 1; P_APP 1];[P_APP 1; P_APP 2];
                          [P_APP 2; P_APP 2]; 
                          [P_APP 1; P_APP 1; P_APP 2; P_APP 1]]
          (if c1 > 0 then 
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
        (Lazy.force coq_fast_Zmult_plus_distr) :: 
      (tac1 @ tac2), Oplus(t1',t2')
  | Oinv t ->
      [clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 2]] 
	 (Lazy.force coq_fast_Zmult_Zopp_left);
       focused_simpl (P_APP 2 :: p)], Otimes(t,Oz(-n))
  | Otimes(t1,Oz x) -> 
      [clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 1;P_APP 2];[P_APP 2]]
         (Lazy.force coq_fast_Zmult_assoc_r);
       focused_simpl (P_APP 2 :: p)], 
      Otimes(t1,Oz (n*x))
  | Otimes(t1,t2) -> error "Omega: Can't solve a goal with non-linear products"
  | (Oatom _ as t) -> [], Otimes(t,Oz n)
  | Oz i -> [focused_simpl p],Oz(n*i)
  | Oufo c -> [], Oufo (mkApp (Lazy.force coq_Zmult, [| mk_integer n |]))
      
let rec scalar_norm p_init = 
  let rec loop p = function
    | [] -> [focused_simpl p_init]
    | (_::l) -> 
	clever_rewrite p
          [[P_APP 1; P_APP 1; P_APP 1];[P_APP 1; P_APP 1; P_APP 2];
           [P_APP 1; P_APP 2];[P_APP 2]]
          (Lazy.force coq_fast_OMEGA16) :: loop (P_APP 2 :: p) l 
  in
  loop p_init

let rec norm_add p_init =
  let rec loop p = function
    | [] -> [focused_simpl p_init]
    | _:: l -> 
	clever_rewrite p [[P_APP 1;P_APP 1]; [P_APP 1; P_APP 2];[P_APP 2]]
          (Lazy.force coq_fast_Zplus_assoc_r) ::
	loop (P_APP 2 :: p) l 
  in
  loop p_init

let rec scalar_norm_add p_init =
  let rec loop p = function
    | [] -> [focused_simpl p_init]
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
        (Lazy.force coq_fast_Zopp_Zplus) :: 
      (tac1 @ tac2),
      Oplus(t1',t2')
  | Oinv t ->
      [clever_rewrite p [[P_APP 1;P_APP 1]] (Lazy.force coq_fast_Zopp_Zopp)], t
  | Otimes(t1,Oz x) -> 
      [clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 1;P_APP 2]]
         (Lazy.force coq_fast_Zopp_Zmult_r);
       focused_simpl (P_APP 2 :: p)], Otimes(t1,Oz (-x))
  | Otimes(t1,t2) -> error "Omega: Can't solve a goal with non-linear products"
  | (Oatom _ as t) ->
      let r = Otimes(t,Oz(-1)) in
      [clever_rewrite p [[P_APP 1]] (Lazy.force coq_fast_Zopp_one)], r
  | Oz i -> [focused_simpl p],Oz(-i)
  | Oufo c -> [], Oufo (mkApp (Lazy.force coq_Zopp, [| c |]))
      
let rec transform p t = 
  let default () =
    try 
      let v,th,_ = find_constr t in
      [clever_rewrite_base p (mkVar v) (mkVar th)], Oatom (string_of_id v)
    with _ -> 
      let v = new_identifier_var ()
      and th = new_identifier () in
      hide_constr t v th false;
      [clever_rewrite_base p (mkVar v) (mkVar th)], Oatom (string_of_id v) 
  in
  try match destructurate t with
    | Kapp("Zplus",[t1;t2]) ->
	let tac1,t1' = transform (P_APP 1 :: p) t1 
	and tac2,t2' = transform (P_APP 2 :: p) t2 in
	let tac,t' = shuffle p (t1',t2') in
	tac1 @ tac2 @ tac, t'
    | Kapp("Zminus",[t1;t2]) ->
	let tac,t = 
	  transform p
	    (mkApp (Lazy.force coq_Zplus,
		     [| t1; (mkApp (Lazy.force coq_Zopp, [| t2 |])) |])) in
	unfold sp_Zminus :: tac,t
    | Kapp("Zs",[t1]) ->
	let tac,t = transform p (mkApp (Lazy.force coq_Zplus,
					 [| t1; mk_integer 1 |])) in
	unfold sp_Zs :: tac,t
   | Kapp("Zmult",[t1;t2]) ->
       let tac1,t1' = transform (P_APP 1 :: p) t1 
       and tac2,t2' = transform (P_APP 2 :: p) t2 in
       begin match t1',t2' with
         | (_,Oz n) -> let tac,t' = scalar p n t1' in tac1 @ tac2 @ tac,t'
         | (Oz n,_) ->
             let sym = 
	       clever_rewrite p [[P_APP 1];[P_APP 2]] 
		 (Lazy.force coq_fast_Zmult_sym) in
             let tac,t' = scalar p n t2' in tac1 @ tac2 @ (sym :: tac),t'
         | _ -> default ()
       end
   | Kapp(("POS"|"NEG"|"ZERO"),_) -> 
       (try ([],Oz(recognize_number t)) with _ -> default ())
   | Kvar s -> [],Oatom s
   | Kapp("Zopp",[t]) ->
       let tac,t' = transform (P_APP 1 :: p) t in
       let tac',t'' = negate p t' in
       tac @ tac', t''
   | Kapp("inject_nat",[t']) ->
       begin try 
         let v,th,_ = find_constr t' in 
         [clever_rewrite_base p (mkVar v) (mkVar th)],Oatom(string_of_id v)
       with _ -> 
         let v = new_identifier_var () and th = new_identifier () in
         hide_constr t' v th true;
         [clever_rewrite_base p (mkVar v) (mkVar th)], Oatom (string_of_id v)
       end
   | _ -> default ()
  with e when catchable_exception e -> default ()
      
let shrink_pair p f1 f2 =
  match f1,f2 with
    | Oatom v,Oatom _ -> 
	let r = Otimes(Oatom v,Oz 2) in
	clever_rewrite p [[P_APP 1]] (Lazy.force coq_fast_Zred_factor1), r
    | Oatom v, Otimes(_,c2) -> 
	let r = Otimes(Oatom v,Oplus(c2,Oz 1)) in
	clever_rewrite p [[P_APP 1];[P_APP 2;P_APP 2]] 
	  (Lazy.force coq_fast_Zred_factor2), r
    | Otimes (v1,c1),Oatom v -> 
	let r = Otimes(Oatom v,Oplus(c1,Oz 1)) in
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
	  flush Pervasives.stdout; error "shrink.1"
	end

let reduce_factor p = function
  | Oatom v ->
      let r = Otimes(Oatom v,Oz 1) in
      [clever_rewrite p [[]] (Lazy.force coq_fast_Zred_factor0)],r
  | Otimes(Oatom v,Oz n) as f -> [],f
  | Otimes(Oatom v,c) ->
      let rec compute = function
        | Oz n -> n
	| Oplus(t1,t2) -> compute t1 + compute t2 
	| _ -> error "condense.1" 
      in
      [focused_simpl (P_APP 2 :: p)], Otimes(Oatom v,Oz(compute c))
  | t -> oprint t; error "reduce_factor.1"

let rec condense p = function
  | Oplus(f1,(Oplus(f2,r) as t)) ->
      if weight f1 = weight f2 then begin
	let shrink_tac,t = shrink_pair (P_APP 1 :: p) f1 f2 in
	let assoc_tac = 
          clever_rewrite p 
            [[P_APP 1];[P_APP 2;P_APP 1];[P_APP 2;P_APP 2]]
            (Lazy.force coq_fast_Zplus_assoc_l) in
	let tac_list,t' = condense p (Oplus(t,r)) in
	(assoc_tac :: shrink_tac :: tac_list), t'
      end else begin
	let tac,f = reduce_factor (P_APP 1 :: p) f1 in
	let tac',t' = condense (P_APP 2 :: p) t in 
	(tac @ tac'), Oplus(f,t') 
      end
  | Oplus(f1,Oz n) as t -> 
      let tac,f1' = reduce_factor (P_APP 1 :: p) f1 in tac,Oplus(f1',Oz n)
  | Oplus(f1,f2) -> 
      if weight f1 = weight f2 then begin
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
      let final = Oplus(t',Oz 0) in
      let tac' = clever_rewrite p [[]] (Lazy.force coq_fast_Zred_factor6) in
      tac @ [tac'], final

let rec clear_zero p = function
  | Oplus(Otimes(Oatom v,Oz 0),r) ->
      let tac =
	clever_rewrite p [[P_APP 1;P_APP 1];[P_APP 2]] 
	  (Lazy.force coq_fast_Zred_factor5) in
      let tac',t = clear_zero p r in
      tac :: tac',t
  | Oplus(f,r) -> 
      let tac,t = clear_zero (P_APP 2 :: p) r in tac,Oplus(f,t)
  | t -> [],t

let replay_history tactic_normalisation = 
  let aux  = id_of_string "auxiliary" in
  let aux1 = id_of_string "auxiliary_1" in
  let aux2 = id_of_string "auxiliary_2" in
  let zero = mk_integer 0 in
  let rec loop t =
    match t with
      | HYP e :: l -> 
	  begin 
	    try 
	      tclTHEN 
		(List.assoc (hyp_of_tag e.id) tactic_normalisation) 
		(loop l)
	    with Not_found -> loop l end
      | NEGATE_CONTRADICT (e2,e1,b) :: l ->
	  let eq1 = decompile e1 
	  and eq2 = decompile e2 in 
	  let id1 = hyp_of_tag e1.id 
	  and id2 = hyp_of_tag e2.id in
	  let k = if b then (-1) else 1 in
	  let p_initial = [P_APP 1;P_TYPE] in
	  let tac= shuffle_mult_right p_initial e1.body k e2.body in
	  tclTHEN 
	    (tclTHEN 
	       (tclTHEN 
		  (tclTHEN 
		     (generalize_tac 
			[mkApp (Lazy.force coq_OMEGA17, [| 
				   val_of eq1;
				   val_of eq2;
				   mk_integer k; 
				   mkVar id1; mkVar id2 |])])
		     (mk_then tac)) 
		  (intros_using [aux]))
	       (resolve_id aux))
            reflexivity
      | CONTRADICTION (e1,e2) :: l -> 
	  let eq1 = decompile e1 
	  and eq2 = decompile e2 in 
	  let p_initial = [P_APP 2;P_TYPE] in
	  let tac = shuffle_cancel p_initial e1.body in
	  let solve_le =
            let superieur = Lazy.force coq_SUPERIEUR in
            let not_sup_sup = mkApp (build_coq_eq (), [| 
					Lazy.force coq_relation; 
					Lazy.force coq_SUPERIEUR;
					Lazy.force coq_SUPERIEUR |])
	    in
            tclTHENS 
	      (tclTHEN 
		 (tclTHEN 
		    (tclTHEN 
		       (unfold sp_Zle) 
		       (simpl_in_concl)) 
		    intro)
		 (absurd not_sup_sup))
	      [ assumption ; reflexivity ] 
	  in
	  let theorem =
            mkApp (Lazy.force coq_OMEGA2, [| 
		      val_of eq1; val_of eq2; 
		      mkVar (hyp_of_tag e1.id);
		      mkVar (hyp_of_tag e2.id) |])
	  in
	  tclTHEN (tclTHEN (generalize_tac [theorem]) (mk_then tac)) (solve_le)
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
		(tclTHEN 
		   (tclTHEN 
		      (tclTHEN
			 (tclTHEN 
			    (intros_using [aux])
			    (generalize_tac 
			       [mkApp (Lazy.force coq_OMEGA1,
					[| eq1; rhs; mkVar aux; mkVar id |])]))
			 (clear [aux;id])) 
		      (intros_using [id]))
		   (cut (mk_gt kk dd)))
		[ tclTHENS 
		    (cut (mk_gt kk zero)) 
		    [ tclTHEN 
			(tclTHEN 
			   (tclTHEN
			      (tclTHEN 
				 (intros_using [aux1; aux2])
				 (generalize_tac 
				    [mkApp (Lazy.force coq_Zmult_le_approx, [|
				       kk;eq2;dd;mkVar aux1;mkVar aux2; 
				       mkVar id |])]))
			      (clear [aux1;aux2;id])) 
			   (intros_using [id])) 
			(loop l);
		      tclTHEN 
			(tclTHEN 
			   (unfold sp_Zgt) 
			   (simpl_in_concl))
			reflexivity ];
		  tclTHEN 
		    (tclTHEN (unfold sp_Zgt) simpl_in_concl) reflexivity ];
	      tclTHEN (mk_then tac) reflexivity]
	    
      | NOT_EXACT_DIVIDE (e1,k) :: l ->
	  let id = hyp_of_tag e1.id in
	  let c = floor_div e1.constant k in
	  let d = e1.constant - c * k in
	  let e2 =  {id=e1.id; kind=EQUA;constant = c; 
                     body = map_eq_linear (fun c -> c / k) e1.body } in
	  let eq1 = val_of(decompile e1) 
	  and eq2 = val_of(decompile e2) in
	  let kk = mk_integer k 
	  and dd = mk_integer d in
	  let rhs = mk_plus (mk_times eq2 kk) dd in
	  let state_eq = mk_eq eq1 rhs in
	  let tac = scalar_norm_add [P_APP 2] e2.body in
	  tclTHENS 
	    (cut (mk_gt dd zero)) 
	    [ tclTHENS (cut (mk_gt kk dd)) 
		[tclTHEN 
		   (tclTHEN 
		      (tclTHEN
			 (tclTHEN 
			    (tclTHEN 
			       (tclTHEN
				  (tclTHEN 
				     (intros_using [aux2;aux1])
				     (generalize_tac 
					[mkApp (Lazy.force coq_OMEGA4, [|
						   dd;kk;eq2;mkVar aux1; 
						   mkVar aux2 |])]))
				  (clear [aux1;aux2])) 
			       (unfold sp_not)) 
			    (intros_using [aux])) 
			 (resolve_id aux))
		      (mk_then tac))
		   assumption;
		 tclTHEN 
		   (tclTHEN 
		      (unfold sp_Zgt) 
		      simpl_in_concl) 
		   reflexivity ];
              tclTHEN 
		(tclTHEN 
		   (unfold sp_Zgt) simpl_in_concl)
		reflexivity ]
      | EXACT_DIVIDE (e1,k) :: l ->
	  let id = hyp_of_tag e1.id in
	  let e2 =  map_eq_afine (fun c -> c / k) e1 in
	  let eq1 = val_of(decompile e1) 
	  and eq2 = val_of(decompile e2) in
	  let kk = mk_integer k in
	  let state_eq = mk_eq eq1 (mk_times eq2 kk) in
	  if e1.kind = DISE then
            let tac = scalar_norm [P_APP 1] e2.body in
            tclTHENS 
	      (cut state_eq) 
	      [tclTHEN 
		 (tclTHEN 
		    (tclTHEN
		       (tclTHEN 
			  (intros_using [aux1])
			  (generalize_tac 
			     [mkApp (Lazy.force coq_OMEGA18, [| 
				eq1;eq2;kk;mkVar aux1; mkVar id |])]))
		       (clear [aux1;id]))
		    (intros_using [id])) 
		 (loop l);
	       tclTHEN (mk_then tac) reflexivity ]
	  else
            let tac = scalar_norm [P_APP 3] e2.body in
            tclTHENS (cut state_eq) 
	      [
		tclTHENS 
		 (cut (mk_gt kk zero)) 
		 [tclTHEN 
		    (tclTHEN 
		       (tclTHEN
			  (tclTHEN 
			     (intros_using [aux2;aux1])
			     (generalize_tac 
				[mkApp (Lazy.force coq_OMEGA3, [| 
					   eq1; eq2; kk; mkVar aux2; 
					   mkVar aux1;mkVar id|])]))
			  (clear [aux1;aux2;id]))
		       (intros_using [id]))
		    (loop l);
		  tclTHEN 
		    (tclTHEN (unfold sp_Zgt) simpl_in_concl) 
		    reflexivity ];
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
	      (Lazy.force coq_fast_Zopp_one) ::
            scalar_norm [P_APP 3] e1.body 
	  in
	  tclTHENS 
	    (cut (mk_eq eq1 (mk_inv eq2))) 
	    [tclTHEN 
	       (tclTHEN 
		  (tclTHEN
		     (tclTHEN 
			(intros_using [aux])
			(generalize_tac [mkApp (Lazy.force coq_OMEGA8, [| 
					   eq1;eq2;mkVar id1;mkVar id2; 
					   mkVar aux|])]))
		     (clear [id1;id2;aux]))
		  (intros_using [id])) 
	       (loop l);
             tclTHEN (mk_then tac) reflexivity]
	    
      | STATE(new_eq,def,orig,m,sigma) :: l ->
	  let id = new_identifier () 
	  and id2 = hyp_of_tag orig.id in
	  tag_hypothesis id new_eq.id;
	  let eq1 = val_of(decompile def) 
	  and eq2 = val_of(decompile orig) in
	  let v = unintern_id sigma in
	  let vid = id_of_string v in
	  let theorem =
            mkApp (build_coq_ex (), [| 
		      Lazy.force coq_Z;
		      mkLambda
			(Name(id_of_string v),
			 Lazy.force coq_Z,
			 mk_eq (mkRel 1) eq1) |])
	  in
	  let mm = mk_integer m in
	  let p_initial = [P_APP 2;P_TYPE] in
	  let r = mk_plus eq2 (mk_times (mk_plus (mk_inv (mkVar vid)) eq1) mm) in
	  let tac = 
            clever_rewrite (P_APP 1 :: P_APP 1 :: P_APP 2 :: p_initial) 
              [[P_APP 1]] (Lazy.force coq_fast_Zopp_one) ::
            shuffle_mult_right p_initial
              orig.body m ({c= -1;v=sigma}::def.body) in
	  tclTHENS 
	    (cut theorem)  
	    [tclTHEN 
	       (tclTHEN 
		  (tclTHEN 
		     (tclTHEN 
			(tclTHEN 
			   (tclTHEN 
			      (tclTHEN 
				 (tclTHEN 
				    (intros_using [aux]) 
				    (elim_id aux))
				 (clear [aux]))
			      (intros_using [vid; aux]))
			   (generalize_tac
			      [mkApp (Lazy.force coq_OMEGA9, [| 
					 mkVar vid;eq2;eq1;mm;
					 mkVar id2;mkVar aux |])]))
			(mk_then tac)) 
		     (clear [aux])) 
		  (intros_using [id])) 
	       (loop l);
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
	    [tclTHEN (tclTHEN (mk_then tac1) (intros_using [id1])) 
	       (loop act1);
             tclTHEN (tclTHEN (mk_then tac2) (intros_using [id2])) 
	       (loop act2)]
      | SUM(e3,(k1,e1),(k2,e2)) :: l ->
	  let id = new_identifier () in
	  tag_hypothesis id e3;
	  let id1 = hyp_of_tag e1.id 
	  and id2 = hyp_of_tag e2.id in
	  let eq1 = val_of(decompile e1) 
	  and eq2 = val_of(decompile e2) in
	  if k1 = 1 & e2.kind = EQUA then
            let tac_thm =
              match e1.kind with
		| EQUA -> Lazy.force coq_OMEGA5 
		| INEQ -> Lazy.force coq_OMEGA6 
		| DISE -> Lazy.force coq_OMEGA20 
	    in
            let kk = mk_integer k2 in
            let p_initial =
              if e1.kind=DISE then [P_APP 1; P_TYPE] else [P_APP 2; P_TYPE] in
            let tac = shuffle_mult_right p_initial e1.body k2 e2.body in
            tclTHEN 
	      (tclTHEN 
		 (tclTHEN 
		    (generalize_tac [mkApp (tac_thm, [| eq1; eq2; 
					       kk; mkVar id1; mkVar id2 |])])
		    (mk_then tac)) 
		 (intros_using [id])) 
	      (loop l)
	  else
            let kk1 = mk_integer k1 
	    and kk2 = mk_integer k2 in
	    let p_initial = [P_APP 2;P_TYPE] in
	    let tac= shuffle_mult p_initial k1 e1.body k2 e2.body in
            tclTHENS (cut (mk_gt kk1 zero)) 
	      [tclTHENS 
		 (cut (mk_gt kk2 zero)) 
		 [tclTHEN 
		    (tclTHEN
		       (tclTHEN 
			  (tclTHEN 
			     (tclTHEN 
				(intros_using [aux2;aux1]) 
				(generalize_tac
				   [mkApp (Lazy.force coq_OMEGA7, [| 
					      eq1;eq2;kk1;kk2; 
					      mkVar aux1;mkVar aux2;
					      mkVar id1;mkVar id2 |])]))
			     (clear [aux1;aux2]))
			  (mk_then tac))
		       (intros_using [id]))
		    (loop l);
		  tclTHEN 
		    (tclTHEN (unfold sp_Zgt) simpl_in_concl) 
		    reflexivity ];
	       tclTHEN 
		 (tclTHEN (unfold sp_Zgt) simpl_in_concl) 
		 reflexivity ]
      | CONSTANT_NOT_NUL(e,k) :: l -> 
	  tclTHEN (generalize_tac [mkVar (hyp_of_tag e)]) Equality.discrConcl
      | CONSTANT_NUL(e) :: l -> 
	  tclTHEN (resolve_id (hyp_of_tag e)) reflexivity
      | CONSTANT_NEG(e,k) :: l ->
	  tclTHEN 
	    (tclTHEN 
	       (tclTHEN 
		  (tclTHEN 
		     (tclTHEN 
			(tclTHEN 
			   (generalize_tac [mkVar (hyp_of_tag e)]) 
			   (unfold sp_Zle))
			simpl_in_concl) 
		     (unfold sp_not)) 
		  (intros_using [aux])) 
	       (resolve_id aux))
	    reflexivity 
      | _ -> tclIDTAC 
  in
  loop

let normalize p_initial t =
  let (tac,t') = transform p_initial t in
  let (tac',t'') = condense p_initial t' in
  let (tac'',t''') = clear_zero p_initial t'' in 
  tac @ tac' @ tac'' , t'''
    
let normalize_equation id flag theorem pos t t1 t2 (tactic,defs) =
  let p_initial = [P_APP pos ;P_TYPE] in
  let (tac,t') = normalize p_initial t in
  let shift_left = 
    tclTHEN 
      (generalize_tac [mkApp (theorem, [| t1; t2; mkVar id |]) ])
      (clear [id]) 
  in
  if tac <> [] then
    let id' = new_identifier () in 
    ((id',((tclTHEN ((tclTHEN (shift_left) (mk_then tac))) 
	     (intros_using [id'])))) :: tactic,
     compile id' flag t' :: defs)
  else 
    (tactic,defs)
    
let destructure_omega gl tac_def (id,c) =
  if atompart_of_id id = "State" then 
    tac_def
  else
    try match destructurate c with
      | Kapp("eq",[typ;t1;t2]) 
	when destructurate (pf_nf gl typ) = Kapp("Z",[]) ->
	  let t = mk_plus t1 (mk_inv t2) in
	  normalize_equation 
	    id EQUA (Lazy.force coq_Zegal_left) 2 t t1 t2 tac_def
      | Kapp("Zne",[t1;t2]) ->
	  let t = mk_plus t1 (mk_inv t2) in
	  normalize_equation
	    id DISE (Lazy.force coq_Zne_left) 1 t t1 t2 tac_def
      | Kapp("Zle",[t1;t2]) ->
	  let t = mk_plus t2 (mk_inv t1) in
	  normalize_equation
	    id INEQ (Lazy.force coq_Zle_left) 2 t t1 t2 tac_def
      | Kapp("Zlt",[t1;t2]) ->
	  let t = mk_plus (mk_plus t2 (mk_integer (-1))) (mk_inv t1) in
	  normalize_equation
	    id INEQ (Lazy.force coq_Zlt_left) 2 t t1 t2 tac_def
      | Kapp("Zge",[t1;t2]) ->
	  let t = mk_plus t1 (mk_inv t2) in
	  normalize_equation
	    id INEQ (Lazy.force coq_Zge_left) 2 t t1 t2 tac_def
      | Kapp("Zgt",[t1;t2]) ->
	  let t = mk_plus (mk_plus t1 (mk_integer (-1))) (mk_inv t2) in
	  normalize_equation
	    id INEQ (Lazy.force coq_Zgt_left) 2 t t1 t2 tac_def
      | _ -> tac_def
    with e when catchable_exception e -> tac_def

let coq_omega gl =
  clear_tables ();
  let tactic_normalisation, system = 
    List.fold_left (destructure_omega gl) ([],[]) (pf_hyps_types gl) in
  let prelude,sys = 
    List.fold_left 
      (fun (tac,sys) (t,(v,th,b)) ->
	 if b then
           let id = new_identifier () in
           let i = new_id () in
           tag_hypothesis id i;
           (tclTHEN 
	      (tclTHEN 
		 (tclTHEN
		    (tclTHEN 
		       (tclTHEN
			  (simplest_elim (applist 
					    (Lazy.force coq_intro_Z, 
					     [t])))
			  (intros_using [v; id])) 
		       (elim_id id))
		    (clear [id])) 
		 (intros_using [th;id])) 
	      tac),
           {kind = INEQ; 
	    body = [{v=intern_id (string_of_id v); c=1}]; 
            constant = 0; id = i} :: sys
	 else
           (tclTHEN 
	      (tclTHEN 
		 (simplest_elim (applist (Lazy.force coq_new_var, [t])))
		 (intros_using [v;th])) 
	      tac),
           sys) 
      (tclIDTAC,[]) (dump_tables ()) 
  in
  let system = system @ sys in
  if !display_system_flag then display_system system;
  if !old_style_flag then begin
    try let _ = simplify false system in tclIDTAC gl
    with UNSOLVABLE -> 
      let _,path = depend [] [] (history ()) in
      if !display_action_flag then display_action path;
      (tclTHEN prelude (replay_history tactic_normalisation path)) gl 
  end else begin 
    try
      let path = simplify_strong system in
      if !display_action_flag then display_action path; 
      (tclTHEN prelude (replay_history tactic_normalisation path)) gl
    with NO_CONTRADICTION -> error "Omega can't solve this system"
  end

let coq_omega = solver_time coq_omega
		  
let nat_inject gl =
  let aux = id_of_string "auxiliary" in
  let table = Hashtbl.create 7 in
  let rec explore p t = 
    try match destructurate t with
      | Kapp("plus",[t1;t2]) ->
          (tclTHEN 
	     ((tclTHEN 
		 (clever_rewrite_gen p (mk_plus (mk_inj t1) (mk_inj t2))
                    ((Lazy.force coq_inj_plus),[t1;t2])) 
		 (explore (P_APP 1 :: p) t1))) 
	     (explore (P_APP 2 :: p) t2))
      | Kapp("mult",[t1;t2]) ->
          (tclTHEN 
	     (tclTHEN 
		(clever_rewrite_gen p (mk_times (mk_inj t1) (mk_inj t2))
                   ((Lazy.force coq_inj_mult),[t1;t2])) 
		(explore (P_APP 1 :: p) t1)) 
	     (explore (P_APP 2 :: p) t2))
      | Kapp("minus",[t1;t2]) ->
          let id = new_identifier () in
          tclTHENS
            (tclTHEN 
	       (simplest_elim (applist (Lazy.force coq_le_gt_dec, [t2;t1]))) 
	       (intros_using [id])) 
	    [
	      (tclTHEN 
		 (tclTHEN 
		    (tclTHEN 
		       (clever_rewrite_gen p 
			  (mk_minus (mk_inj t1) (mk_inj t2))
                          ((Lazy.force coq_inj_minus1),[t1;t2;mkVar id]))
		       (loop [id,mkApp (Lazy.force coq_le, [| t2;t1 |])]))
		    (explore (P_APP 1 :: p) t1)) 
		 (explore (P_APP 2 :: p) t2));
	      
	      (tclTHEN 
		 (clever_rewrite_gen p (mk_integer 0)
                    ((Lazy.force coq_inj_minus2),[t1;t2;mkVar id]))
		 (loop [id,mkApp (Lazy.force coq_gt, [| t2;t1 |])]))
	    ]
      | Kapp("S",[t']) ->
          let rec is_number t =
            try match destructurate t with 
		Kapp("S",[t]) -> is_number t
              | Kapp("O",[]) -> true
              | _ -> false
            with e when catchable_exception e -> false 
	  in
          let rec loop p t =
            try match destructurate t with 
		Kapp("S",[t]) ->
                  (tclTHEN 
                     (clever_rewrite_gen p 
			(mkApp (Lazy.force coq_Zs, [| mk_inj t |]))
			((Lazy.force coq_inj_S),[t])) 
		     (loop (P_APP 1 :: p) t))
              | _ -> explore p t 
            with e when catchable_exception e -> explore p t 
	  in
          if is_number t' then focused_simpl p else loop p t
      | Kapp("pred",[t]) ->
          let t_minus_one = 
	    mkApp (Lazy.force coq_minus, [| t; 
		      mkApp (Lazy.force coq_S, [| Lazy.force coq_O |]) |]) in
          tclTHEN
            (clever_rewrite_gen_nat (P_APP 1 :: p) t_minus_one 
               ((Lazy.force coq_pred_of_minus),[t]))
            (explore p t_minus_one) 
      | Kapp("O",[]) -> focused_simpl p
      | _ -> tclIDTAC 
    with e when catchable_exception e -> tclIDTAC 
	
  and loop = function
    | [] -> tclIDTAC
    | (i,t)::lit -> 
	  begin try match destructurate t with 
              Kapp("le",[t1;t2]) ->
		(tclTHEN 
		   (tclTHEN 
		      (tclTHEN
			 (tclTHEN 
			    (tclTHEN 
			       (generalize_tac 
				  [mkApp (Lazy.force coq_inj_le,
					     [| t1;t2;mkVar i |]) ])
			       (explore [P_APP 1; P_TYPE] t1))
			    (explore [P_APP 2; P_TYPE] t2))
			 (clear [i]))
		      (intros_using [i])) 
		   (loop lit))
            | Kapp("lt",[t1;t2]) ->
		(tclTHEN 
		   (tclTHEN 
		      (tclTHEN
			 (tclTHEN 
			    (tclTHEN 
			       (generalize_tac 
				  [mkApp (Lazy.force coq_inj_lt, [|  
					     t1;t2;mkVar i |]) ])
			       (explore [P_APP 1; P_TYPE] t1))
			    (explore [P_APP 2; P_TYPE] t2))
			 (clear [i]))
		      (intros_using [i])) 
		   (loop lit))
            | Kapp("ge",[t1;t2]) ->
		(tclTHEN 
		   (tclTHEN 
		      (tclTHEN
			 (tclTHEN 
			    (tclTHEN 
			       (generalize_tac 
				  [mkApp (Lazy.force coq_inj_ge,
					     [| t1;t2;mkVar i |]) ])
			       (explore [P_APP 1; P_TYPE] t1))
			    (explore [P_APP 2; P_TYPE] t2))
			 (clear [i]))
		      (intros_using [i])) 
		   (loop lit))
            | Kapp("gt",[t1;t2]) ->
		(tclTHEN 
		   (tclTHEN 
		      (tclTHEN
			 (tclTHEN 
			    (tclTHEN 
			       (generalize_tac 
				  [mkApp (Lazy.force coq_inj_gt, [|  
					     t1;t2;mkVar i |]) ])
			       (explore [P_APP 1; P_TYPE] t1))
			    (explore [P_APP 2; P_TYPE] t2))
			 (clear [i]))
		      (intros_using [i])) 
		   (loop lit))
            | Kapp("neq",[t1;t2]) ->
		(tclTHEN 
		   (tclTHEN 
		      (tclTHEN
			 (tclTHEN 
			    (tclTHEN 
			       (generalize_tac 
				  [mkApp (Lazy.force coq_inj_neq, [| 
					     t1;t2;mkVar i |]) ])
			       (explore [P_APP 1; P_TYPE] t1))
			    (explore [P_APP 2; P_TYPE] t2))
			 (clear [i]))
		      (intros_using [i])) 
		   (loop lit))
            | Kapp("eq",[typ;t1;t2]) ->
		if pf_conv_x gl typ (Lazy.force coq_nat) then
                  (tclTHEN
		     (tclTHEN 
			(tclTHEN
			   (tclTHEN 
			      (tclTHEN
				 (generalize_tac 
				    [mkApp (Lazy.force coq_inj_eq, [| 
					       t1;t2;mkVar i |]) ])
				 (explore [P_APP 2; P_TYPE] t1))
			      (explore [P_APP 3; P_TYPE] t2))
			   (clear [i]))
			(intros_using [i]))
		     (loop lit))
		else loop lit
	    | _ -> loop lit
	  with e when catchable_exception e -> loop lit end 
  in
  loop (List.rev (pf_hyps_types gl)) gl
    
let rec decidability gl t =
  match destructurate t with
    | Kapp("or",[t1;t2]) -> 
	mkApp (Lazy.force coq_dec_or, [| t1; t2;
		  decidability gl t1; decidability gl t2 |])
    | Kapp("and",[t1;t2]) -> 
	mkApp (Lazy.force coq_dec_and, [| t1; t2;
		  decidability gl t1; decidability gl t2 |])
    | Kimp(t1,t2) -> 
	mkApp (Lazy.force coq_dec_imp, [| t1; t2;
		  decidability gl t1; decidability gl t2 |])
    | Kapp("not",[t1]) -> mkApp (Lazy.force coq_dec_not, [| t1; 
				    decidability gl t1 |])
    | Kapp("eq",[typ;t1;t2]) -> 
	begin match destructurate (pf_nf gl typ) with
          | Kapp("Z",[]) ->  mkApp (Lazy.force coq_dec_eq, [| t1;t2 |])
          | Kapp("nat",[]) ->  mkApp (Lazy.force coq_dec_eq_nat, [| t1;t2 |])
          | _ -> errorlabstrm "decidability" 
		[< 'sTR "Omega: Can't solve a goal with equality on "; 
		   Printer.prterm typ >]
	end
    | Kapp("Zne",[t1;t2]) -> mkApp (Lazy.force coq_dec_Zne, [| t1;t2 |])
    | Kapp("Zle",[t1;t2]) -> mkApp (Lazy.force coq_dec_Zle, [| t1;t2 |])
    | Kapp("Zlt",[t1;t2]) -> mkApp (Lazy.force coq_dec_Zlt, [| t1;t2 |])
    | Kapp("Zge",[t1;t2]) -> mkApp (Lazy.force coq_dec_Zge, [| t1;t2 |])
    | Kapp("Zgt",[t1;t2]) -> mkApp (Lazy.force coq_dec_Zgt, [| t1;t2 |])
    | Kapp("le", [t1;t2]) -> mkApp (Lazy.force coq_dec_le, [| t1;t2 |])
    | Kapp("lt", [t1;t2]) -> mkApp (Lazy.force coq_dec_lt, [| t1;t2 |])
    | Kapp("ge", [t1;t2]) -> mkApp (Lazy.force coq_dec_ge, [| t1;t2 |])
    | Kapp("gt", [t1;t2]) -> mkApp (Lazy.force coq_dec_gt, [| t1;t2 |])
    | Kapp("False",[]) -> Lazy.force coq_dec_False
    | Kapp("True",[]) -> Lazy.force coq_dec_True
    | Kapp(t,_::_) -> error ("Omega: Unrecognized predicate or connective: "
			     ^ t)
    | Kapp(t,[]) -> error ("Omega: Unrecognized atomic proposition: "^ t)
    | Kvar _ -> error "Omega: Can't solve a goal with proposition variables"
    | _ -> error "Omega: Unrecognized proposition"
	  
let destructure_hyps gl =
  let rec loop evbd = function
    | [] -> (tclTHEN nat_inject coq_omega)
    | (i,t)::lit ->
	begin try match destructurate t with
          | Kapp(("Zle"|"Zge"|"Zgt"|"Zlt"|"Zne"),[t1;t2]) -> loop evbd lit
          | Kapp("or",[t1;t2]) ->
              (tclTHENS ((tclTHEN ((tclTHEN (elim_id i) (clear [i]))) 
			    (intros_using [i]))) 
		 ([ loop evbd ((i,t1)::lit); loop evbd ((i,t2)::lit) ]))
          | Kapp("and",[t1;t2]) ->
              let i1 = id_of_string (string_of_id i ^ "_left") in
              let i2 = id_of_string (string_of_id i ^ "_right") in
              (tclTHEN 
		 (tclTHEN 
		    (tclTHEN (elim_id i) (clear [i]))
		    (intros_using [i1;i2]))
		 (loop (i1::i2::evbd) ((i1,t1)::(i2,t2)::lit)))
          | Kimp(t1,t2) ->
              if isprop (pf_type_of gl t1) & closed0 t2 then begin
		(tclTHEN 
		   (tclTHEN 
		      (tclTHEN
			 (generalize_tac [mkApp (Lazy.force coq_imp_simp, [| 
						    t1; t2; 
						    decidability gl t1;
						    mkVar i|])]) 
			 (clear [i])) 
		      (intros_using [i])) 
		   (loop evbd ((i,mk_or (mk_not t1) t2)::lit)))
              end else loop evbd lit
          | Kapp("not",[t]) -> 
              begin match destructurate t with 
		  Kapp("or",[t1;t2]) -> 
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN 
			     (generalize_tac [mkApp (Lazy.force coq_not_or,[| 
							t1; t2; mkVar i |])])
			     (clear [i])) 
			  (intros_using [i])) 
                       (loop evbd ((i,mk_and (mk_not t1) (mk_not t2)):: lit)))
		| Kapp("and",[t1;t2]) -> 
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac
				[mkApp (Lazy.force coq_not_and, [| t1; t2;
					   decidability gl t1;mkVar i|])])
			     (clear [i]))
			  (intros_using [i]))
                       (loop evbd ((i,mk_or (mk_not t1) (mk_not t2))::lit)))
		| Kimp(t1,t2) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac 
				[mkApp (Lazy.force coq_not_imp, [| t1; t2; 
					   decidability gl t1;mkVar i |])])
			     (clear [i])) 
			  (intros_using [i]))
                       (loop evbd ((i,mk_and t1 (mk_not t2)) :: lit)))
		| Kapp("not",[t]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac
				[mkApp (Lazy.force coq_not_not, [| t;
					    decidability gl t; mkVar i |])])
			     (clear [i])) 
			  (intros_using [i])) 
                       (loop evbd ((i,t)::lit)))
		| Kapp("Zle", [t1;t2]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac [mkApp (Lazy.force coq_not_Zle,
							[| t1;t2;mkVar i|])])
			     (clear [i])) 
			  (intros_using [i])) 
		       (loop evbd lit))
		| Kapp("Zge", [t1;t2]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac [mkApp (Lazy.force coq_not_Zge,
							[| t1;t2;mkVar i|])])
			     (clear [i])) 
			  (intros_using [i])) 
		       (loop evbd lit))
		| Kapp("Zlt", [t1;t2]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac [mkApp (Lazy.force coq_not_Zlt,
							[| t1;t2;mkVar i|])])
			     (clear [i])) 
			  (intros_using [i])) 
		       (loop evbd lit))
		| Kapp("Zgt", [t1;t2]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac [mkApp (Lazy.force coq_not_Zgt,
							[| t1;t2;mkVar i|])])
			     (clear [i])) 
			  (intros_using [i])) 
		       (loop evbd lit))
		| Kapp("le", [t1;t2]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac [mkApp (Lazy.force coq_not_le,
							[| t1;t2;mkVar i|])])
			     (clear [i])) 
			  (intros_using [i])) 
		       (loop evbd lit))
		| Kapp("ge", [t1;t2]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac [mkApp (Lazy.force coq_not_ge,
							[| t1;t2;mkVar i|])])
			     (clear [i])) 
			  (intros_using [i])) 
		       (loop evbd lit))
		| Kapp("lt", [t1;t2]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac [mkApp (Lazy.force coq_not_lt,
							[| t1;t2;mkVar i|])])
			     (clear [i])) 
			  (intros_using [i])) 
		       (loop evbd lit))
		| Kapp("gt", [t1;t2]) ->
                    (tclTHEN 
		       (tclTHEN 
			  (tclTHEN
			     (generalize_tac [mkApp (Lazy.force coq_not_gt,
							[| t1;t2;mkVar i|])])
			     (clear [i])) 
			  (intros_using [i])) 
		       (loop evbd lit))
		| Kapp("eq",[typ;t1;t2]) ->
                    if !old_style_flag then begin 
		      match destructurate (pf_nf gl typ) with
			| Kapp("nat",_) -> 
                            (tclTHEN 
			       (tclTHEN 
				  (tclTHEN 
				     (simplest_elim 
					(applist 
					   (Lazy.force coq_not_eq, 
					    [t1;t2;mkVar i])))
				     (clear [i])) 
				  (intros_using [i])) 
			       (loop evbd lit))
			| Kapp("Z",_) ->
                            (tclTHEN 
			       (tclTHEN 
				  (tclTHEN 
				     (simplest_elim 
					(applist 
					   (Lazy.force coq_not_Zeq, 
					    [t1;t2;mkVar i])))
				     (clear [i])) 
				  (intros_using [i])) 
			       (loop evbd lit))
			| _ -> loop evbd lit
                    end else begin 
		      match destructurate (pf_nf gl typ) with
			| Kapp("nat",_) -> 
                            (tclTHEN 
			       (convert_hyp i 
				  (mkApp (Lazy.force coq_neq, [| t1;t2|])))
			       (loop evbd lit))
			| Kapp("Z",_) ->
                            (tclTHEN 
			       (convert_hyp i 
				  (mkApp (Lazy.force coq_Zne, [| t1;t2|])))
			       (loop evbd lit))
			| _ -> loop evbd lit
                    end
		| _ -> loop evbd lit
              end 
          | _ -> loop evbd lit 
	with e when catchable_exception e -> loop evbd lit
	end 
  in
  loop (pf_ids_of_hyps gl) (pf_hyps_types gl) gl

let destructure_goal gl =
  let concl = pf_concl gl in
  let rec loop t =
    match destructurate t with
      | Kapp("not",[t1;t2]) -> 
          (tclTHEN 
	     (tclTHEN (unfold sp_not) intro) 
	     destructure_hyps)
      | Kimp(a,b) -> (tclTHEN intro (loop b))
      | Kapp("False",[]) -> destructure_hyps
      | _ ->
          (tclTHEN 
	     (tclTHEN
		(Tactics.refine 
		   (mkApp (Lazy.force coq_dec_not_not, [| t;
			      decidability gl t; mkNewMeta () |])))
		intro) 
	     (destructure_hyps)) 
  in
  (loop concl) gl

let destructure_goal = all_time (destructure_goal)

let omega_solver gl = 
  let result = destructure_goal gl in 
  (* if !display_time_flag then begin text_time (); 
     flush Pervasives.stdout end; *)
  result

let omega = hide_atomic_tactic "Omega" omega_solver


