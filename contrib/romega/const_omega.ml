(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

let module_refl_name = "ReflOmegaCore"
let module_refl_path = ["Coq"; "romega"; module_refl_name]

type result = 
   Kvar of string
 | Kapp of string * Term.constr list
 | Kimp of Term.constr * Term.constr
 | Kufo;;

let destructurate t =
  let c, args = Term.decompose_app t in
  let env = Global.env() in
  match Term.kind_of_term c, args with
    | Term.Const sp, args ->
	Kapp (Names.string_of_id
		(Nametab.id_of_global (Libnames.ConstRef sp)),
	      args)
    | Term.Construct csp , args ->
	Kapp (Names.string_of_id
		(Nametab.id_of_global (Libnames.ConstructRef csp)),
	      args)
    | Term.Ind isp, args ->
	Kapp (Names.string_of_id
		(Nametab.id_of_global (Libnames.IndRef isp)),
	      args)
    | Term.Var id,[] -> Kvar(Names.string_of_id id)
    | Term.Prod (Names.Anonymous,typ,body), [] -> Kimp(typ,body)
    | Term.Prod (Names.Name _,_,_),[] ->
	Util.error "Omega: Not a quantifier-free goal"
    | _ -> Kufo

exception Destruct

let dest_const_apply t = 
  let f,args = Term.decompose_app t in 
  let ref = 
  match Term.kind_of_term f with 
    | Term.Const sp         -> Libnames.ConstRef sp
    | Term.Construct csp -> Libnames.ConstructRef csp
    | Term.Ind isp       -> Libnames.IndRef isp
    | _ -> raise Destruct
  in  Nametab.id_of_global ref, args

let recognize_number t =
  let rec loop t =
    let f,l = dest_const_apply t in
    match Names.string_of_id f,l with
       "xI",[t] -> Bigint.add Bigint.one (Bigint.mult Bigint.two (loop t))
     | "xO",[t] -> Bigint.mult Bigint.two (loop t)
     | "xH",[] -> Bigint.one
     | _ -> failwith "not a number" in
  let f,l = dest_const_apply t in
    match Names.string_of_id f,l with
        "Zpos",[t] -> loop t
      | "Zneg",[t] -> Bigint.neg (loop t)
      | "Z0",[] -> Bigint.zero
      | _ -> failwith "not a number";;


let logic_dir = ["Coq";"Logic";"Decidable"]

let coq_modules =
  Coqlib.init_modules @ [logic_dir] @ Coqlib.arith_modules @ Coqlib.zarith_base_modules
    @ [["Coq"; "omega"; "OmegaLemmas"]]
    @ [["Coq"; "Lists"; (if !Options.v7 then "PolyList" else "List")]]
    @ [module_refl_path]


let constant = Coqlib.gen_constant_in_modules "Omega" coq_modules

let coq_xH = lazy (constant "xH")
let coq_xO = lazy (constant "xO")
let coq_xI = lazy (constant "xI")
let coq_ZERO = lazy (constant "Z0")
let coq_POS = lazy (constant "Zpos")
let coq_NEG = lazy (constant "Zneg")
let coq_Z = lazy (constant "Z")
let coq_relation = lazy (constant  "comparison")
let coq_SUPERIEUR = lazy (constant "SUPERIEUR")
let coq_INFEEIEUR = lazy (constant "INFERIEUR")
let coq_EGAL = lazy (constant "EGAL")
let coq_Zplus = lazy (constant "Zplus")
let coq_Zmult = lazy (constant  "Zmult")
let coq_Zopp = lazy (constant "Zopp")

let coq_Zminus = lazy (constant "Zminus")
let coq_Zs = lazy (constant  "Zs")
let coq_Zgt = lazy (constant "Zgt")
let coq_Zle = lazy (constant "Zle")
let coq_inject_nat = lazy (constant  "inject_nat")

(* Peano *)
let coq_le = lazy(constant "le")
let coq_gt = lazy(constant "gt")

(* Integers *)
let coq_nat = lazy(constant "nat")
let coq_S = lazy(constant "S")
let coq_O = lazy(constant "O")
let coq_minus = lazy(constant "minus")

(* Logic *)
let coq_eq = lazy(constant  "eq")
let coq_refl_equal = lazy(constant  "refl_equal")
let coq_and = lazy(constant "and")
let coq_not = lazy(constant "not")
let coq_or = lazy(constant "or")
let coq_true = lazy(constant "true")
let coq_false = lazy(constant "false")
let coq_ex = lazy(constant "ex")
let coq_I = lazy(constant "I")

(* Lists *)
let coq_cons =  lazy (constant "cons")
let coq_nil =  lazy (constant "nil")

let coq_pcons = lazy (constant "Pcons")
let coq_pnil = lazy (constant "Pnil")

let coq_h_step = lazy (constant "h_step")
let coq_pair_step = lazy (constant  "pair_step")
let coq_p_left = lazy (constant  "P_LEFT")
let coq_p_right = lazy (constant  "P_RIGHT")
let coq_p_invert = lazy (constant  "P_INVERT")
let coq_p_step = lazy (constant  "P_STEP")
let coq_p_nop = lazy (constant  "P_NOP")


let coq_t_int = lazy (constant  "Tint")
let coq_t_plus = lazy (constant  "Tplus")
let coq_t_mult = lazy (constant  "Tmult")
let coq_t_opp = lazy (constant  "Topp")
let coq_t_minus = lazy (constant  "Tminus")
let coq_t_var = lazy (constant  "Tvar")

let coq_p_eq = lazy (constant  "EqTerm")
let coq_p_leq = lazy (constant  "LeqTerm")
let coq_p_geq = lazy (constant  "GeqTerm")
let coq_p_lt = lazy (constant  "LtTerm")
let coq_p_gt = lazy (constant  "GtTerm")
let coq_p_neq = lazy (constant  "NeqTerm")
let coq_p_true = lazy (constant  "TrueTerm")
let coq_p_false = lazy (constant  "FalseTerm")
let coq_p_not = lazy (constant  "Tnot")
let coq_p_or = lazy (constant  "Tor")
let coq_p_and = lazy (constant  "Tand")
let coq_p_imp = lazy (constant  "Timp")
let coq_p_prop = lazy (constant  "Tprop")

let coq_proposition = lazy (constant  "proposition")
let coq_interp_sequent = lazy (constant  "interp_goal_concl")
let coq_normalize_sequent = lazy (constant  "normalize_goal")
let coq_execute_sequent = lazy (constant  "execute_goal")
let coq_do_concl_to_hyp =  lazy (constant  "do_concl_to_hyp")
let coq_sequent_to_hyps = lazy (constant  "goal_to_hyps")
let coq_normalize_hyps_goal =
  lazy (constant  "normalize_hyps_goal")

(* Constructors for shuffle tactic *)
let coq_t_fusion =  lazy (constant  "t_fusion")
let coq_f_equal =  lazy (constant  "F_equal")
let coq_f_cancel =  lazy (constant  "F_cancel")
let coq_f_left =  lazy (constant  "F_left")
let coq_f_right =  lazy (constant  "F_right")

(* Constructors for reordering tactics *)
let coq_step = lazy (constant  "step")
let coq_c_do_both = lazy (constant  "C_DO_BOTH")
let coq_c_do_left = lazy (constant  "C_LEFT")
let coq_c_do_right = lazy (constant  "C_RIGHT")
let coq_c_do_seq = lazy (constant  "C_SEQ")
let coq_c_nop = lazy (constant  "C_NOP")
let coq_c_opp_plus = lazy (constant  "C_OPP_PLUS")
let coq_c_opp_opp = lazy (constant  "C_OPP_OPP")
let coq_c_opp_mult_r = lazy (constant  "C_OPP_MULT_R")
let coq_c_opp_one = lazy (constant  "C_OPP_ONE")
let coq_c_reduce = lazy (constant  "C_REDUCE")
let coq_c_mult_plus_distr = lazy (constant  "C_MULT_PLUS_DISTR")
let coq_c_opp_left = lazy (constant  "C_MULT_OPP_LEFT")
let coq_c_mult_assoc_r = lazy (constant  "C_MULT_ASSOC_R")
let coq_c_plus_assoc_r = lazy (constant  "C_PLUS_ASSOC_R")
let coq_c_plus_assoc_l = lazy (constant  "C_PLUS_ASSOC_L")
let coq_c_plus_permute = lazy (constant  "C_PLUS_PERMUTE")
let coq_c_plus_sym = lazy (constant  "C_PLUS_SYM")
let coq_c_red0 = lazy (constant  "C_RED0")
let coq_c_red1 = lazy (constant  "C_RED1")
let coq_c_red2 = lazy (constant  "C_RED2")
let coq_c_red3 = lazy (constant  "C_RED3")
let coq_c_red4 = lazy (constant  "C_RED4")
let coq_c_red5 = lazy (constant  "C_RED5")
let coq_c_red6 = lazy (constant  "C_RED6")
let coq_c_mult_opp_left = lazy (constant  "C_MULT_OPP_LEFT")
let coq_c_mult_assoc_reduced = 
  lazy (constant  "C_MULT_ASSOC_REDUCED")
let coq_c_minus = lazy (constant  "C_MINUS")
let coq_c_mult_sym = lazy (constant  "C_MULT_SYM")

let coq_s_constant_not_nul = lazy (constant  "O_CONSTANT_NOT_NUL")
let coq_s_constant_neg = lazy (constant  "O_CONSTANT_NEG")
let coq_s_div_approx = lazy (constant  "O_DIV_APPROX")
let coq_s_not_exact_divide = lazy (constant  "O_NOT_EXACT_DIVIDE")
let coq_s_exact_divide = lazy (constant  "O_EXACT_DIVIDE")
let coq_s_sum = lazy (constant  "O_SUM")
let coq_s_state = lazy (constant  "O_STATE")
let coq_s_contradiction = lazy (constant  "O_CONTRADICTION")
let coq_s_merge_eq = lazy (constant  "O_MERGE_EQ")
let coq_s_split_ineq =lazy (constant  "O_SPLIT_INEQ")
let coq_s_constant_nul =lazy (constant  "O_CONSTANT_NUL")
let coq_s_negate_contradict =lazy (constant  "O_NEGATE_CONTRADICT")
let coq_s_negate_contradict_inv =lazy (constant  "O_NEGATE_CONTRADICT_INV")

(* construction for the [extract_hyp] tactic *)
let coq_direction = lazy  (constant  "direction")
let coq_d_left = lazy  (constant  "D_left")
let coq_d_right = lazy  (constant  "D_right")
let coq_d_mono = lazy  (constant  "D_mono")

let coq_e_split = lazy  (constant  "E_SPLIT")
let coq_e_extract = lazy  (constant  "E_EXTRACT")
let coq_e_solve = lazy  (constant  "E_SOLVE")

let coq_decompose_solve_valid = 
  lazy (constant   "decompose_solve_valid")
let coq_do_reduce_lhyps = lazy (constant   "do_reduce_lhyps")
let coq_do_omega = lazy (constant  "do_omega")

(**
let constant dir s =
   try
     Libnames.constr_of_reference 
       (Nametab.absolute_reference
	  (Libnames.make_path
             (Names.make_dirpath (List.map Names.id_of_string (List.rev dir)))
             (Names.id_of_string s)))
   with e -> print_endline (String.concat "." dir); print_endline s;
             raise e

let path_fast_integer = ["Coq"; "ZArith"; "fast_integer"]
let path_zarith_aux = ["Coq"; "ZArith"; "zarith_aux"]
let path_logic = ["Coq"; "Init";"Logic"]
let path_datatypes = ["Coq"; "Init";"Datatypes"]
let path_peano = ["Coq"; "Init"; "Peano"]
let path_list = ["Coq"; "Lists"; "PolyList"]

let coq_xH = lazy (constant path_fast_integer "xH")
let coq_xO = lazy (constant path_fast_integer "xO")
let coq_xI = lazy (constant path_fast_integer "xI")
let coq_ZERO = lazy (constant path_fast_integer "ZERO")
let coq_POS = lazy (constant path_fast_integer "POS")
let coq_NEG = lazy (constant path_fast_integer "NEG")
let coq_Z = lazy (constant path_fast_integer "Z")
let coq_relation = lazy (constant path_fast_integer "relation")
let coq_SUPERIEUR = lazy (constant path_fast_integer "SUPERIEUR")
let coq_INFEEIEUR = lazy (constant path_fast_integer "INFERIEUR")
let coq_EGAL = lazy (constant path_fast_integer "EGAL")
let coq_Zplus = lazy (constant path_fast_integer "Zplus")
let coq_Zmult = lazy (constant path_fast_integer "Zmult")
let coq_Zopp = lazy (constant path_fast_integer "Zopp")

(* auxiliaires zarith *)
let coq_Zminus = lazy (constant path_zarith_aux "Zminus")
let coq_Zs = lazy (constant path_zarith_aux "Zs")
let coq_Zgt = lazy (constant path_zarith_aux "Zgt")
let coq_Zle = lazy (constant path_zarith_aux "Zle")
let coq_inject_nat = lazy (constant path_zarith_aux "inject_nat")

(* Peano *)
let coq_le = lazy(constant path_peano "le")
let coq_gt = lazy(constant path_peano "gt")

(* Integers *)
let coq_nat = lazy(constant path_datatypes "nat")
let coq_S = lazy(constant path_datatypes "S")
let coq_O = lazy(constant path_datatypes "O")

(* Minus *)
let coq_minus = lazy(constant ["Arith"; "Minus"] "minus")

(* Logic *)
let coq_eq = lazy(constant path_logic "eq")
let coq_refl_equal = lazy(constant path_logic "refl_equal")
let coq_and = lazy(constant path_logic "and")
let coq_not = lazy(constant path_logic "not")
let coq_or = lazy(constant path_logic "or")
let coq_true = lazy(constant path_logic "true")
let coq_false = lazy(constant path_logic "false")
let coq_ex = lazy(constant path_logic "ex")
let coq_I = lazy(constant path_logic "I")

(* Lists *)
let coq_cons =  lazy (constant path_list  "cons")
let coq_nil =  lazy (constant path_list "nil")

let coq_pcons = lazy (constant module_refl_path "Pcons")
let coq_pnil = lazy (constant module_refl_path "Pnil")

let coq_h_step = lazy (constant module_refl_path "h_step")
let coq_pair_step = lazy (constant module_refl_path "pair_step")
let coq_p_left = lazy (constant module_refl_path "P_LEFT")
let coq_p_right = lazy (constant module_refl_path "P_RIGHT")
let coq_p_invert = lazy (constant module_refl_path "P_INVERT")
let coq_p_step = lazy (constant module_refl_path "P_STEP")
let coq_p_nop = lazy (constant module_refl_path "P_NOP")


let coq_t_int = lazy (constant module_refl_path "Tint")
let coq_t_plus = lazy (constant module_refl_path "Tplus")
let coq_t_mult = lazy (constant module_refl_path "Tmult")
let coq_t_opp = lazy (constant module_refl_path "Topp")
let coq_t_minus = lazy (constant module_refl_path "Tminus")
let coq_t_var = lazy (constant module_refl_path "Tvar")

let coq_p_eq = lazy (constant module_refl_path "EqTerm")
let coq_p_leq = lazy (constant module_refl_path "LeqTerm")
let coq_p_geq = lazy (constant module_refl_path "GeqTerm")
let coq_p_lt = lazy (constant module_refl_path "LtTerm")
let coq_p_gt = lazy (constant module_refl_path "GtTerm")
let coq_p_neq = lazy (constant module_refl_path "NeqTerm")
let coq_p_true = lazy (constant module_refl_path "TrueTerm")
let coq_p_false = lazy (constant module_refl_path "FalseTerm")
let coq_p_not = lazy (constant module_refl_path "Tnot")
let coq_p_or = lazy (constant module_refl_path "Tor")
let coq_p_and = lazy (constant module_refl_path "Tand")
let coq_p_imp = lazy (constant module_refl_path "Timp")
let coq_p_prop = lazy (constant module_refl_path "Tprop")

let coq_proposition = lazy (constant module_refl_path "proposition")
let coq_interp_sequent = lazy (constant module_refl_path "interp_goal_concl")
let coq_normalize_sequent = lazy (constant module_refl_path "normalize_goal")
let coq_execute_sequent = lazy (constant module_refl_path "execute_goal")
let coq_do_concl_to_hyp =  lazy (constant module_refl_path "do_concl_to_hyp")
let coq_sequent_to_hyps = lazy (constant module_refl_path "goal_to_hyps")
let coq_normalize_hyps_goal =
  lazy (constant module_refl_path "normalize_hyps_goal")

(* Constructors for shuffle tactic *)
let coq_t_fusion =  lazy (constant module_refl_path "t_fusion")
let coq_f_equal =  lazy (constant module_refl_path "F_equal")
let coq_f_cancel =  lazy (constant module_refl_path "F_cancel")
let coq_f_left =  lazy (constant module_refl_path "F_left")
let coq_f_right =  lazy (constant module_refl_path "F_right")

(* Constructors for reordering tactics *)
let coq_step = lazy (constant module_refl_path "step")
let coq_c_do_both = lazy (constant module_refl_path "C_DO_BOTH")
let coq_c_do_left = lazy (constant module_refl_path "C_LEFT")
let coq_c_do_right = lazy (constant module_refl_path "C_RIGHT")
let coq_c_do_seq = lazy (constant module_refl_path "C_SEQ")
let coq_c_nop = lazy (constant module_refl_path "C_NOP")
let coq_c_opp_plus = lazy (constant module_refl_path "C_OPP_PLUS")
let coq_c_opp_opp = lazy (constant module_refl_path "C_OPP_OPP")
let coq_c_opp_mult_r = lazy (constant module_refl_path "C_OPP_MULT_R")
let coq_c_opp_one = lazy (constant module_refl_path "C_OPP_ONE")
let coq_c_reduce = lazy (constant module_refl_path "C_REDUCE")
let coq_c_mult_plus_distr = lazy (constant module_refl_path "C_MULT_PLUS_DISTR")
let coq_c_opp_left = lazy (constant module_refl_path "C_MULT_OPP_LEFT")
let coq_c_mult_assoc_r = lazy (constant module_refl_path "C_MULT_ASSOC_R")
let coq_c_plus_assoc_r = lazy (constant module_refl_path "C_PLUS_ASSOC_R")
let coq_c_plus_assoc_l = lazy (constant module_refl_path "C_PLUS_ASSOC_L")
let coq_c_plus_permute = lazy (constant module_refl_path "C_PLUS_PERMUTE")
let coq_c_plus_sym = lazy (constant module_refl_path "C_PLUS_SYM")
let coq_c_red0 = lazy (constant module_refl_path "C_RED0")
let coq_c_red1 = lazy (constant module_refl_path "C_RED1")
let coq_c_red2 = lazy (constant module_refl_path "C_RED2")
let coq_c_red3 = lazy (constant module_refl_path "C_RED3")
let coq_c_red4 = lazy (constant module_refl_path "C_RED4")
let coq_c_red5 = lazy (constant module_refl_path "C_RED5")
let coq_c_red6 = lazy (constant module_refl_path "C_RED6")
let coq_c_mult_opp_left = lazy (constant module_refl_path "C_MULT_OPP_LEFT")
let coq_c_mult_assoc_reduced = 
  lazy (constant module_refl_path "C_MULT_ASSOC_REDUCED")
let coq_c_minus = lazy (constant module_refl_path "C_MINUS")
let coq_c_mult_sym = lazy (constant module_refl_path "C_MULT_SYM")

let coq_s_constant_not_nul = lazy (constant module_refl_path "O_CONSTANT_NOT_NUL")
let coq_s_constant_neg = lazy (constant module_refl_path "O_CONSTANT_NEG")
let coq_s_div_approx = lazy (constant module_refl_path "O_DIV_APPROX")
let coq_s_not_exact_divide = lazy (constant module_refl_path "O_NOT_EXACT_DIVIDE")
let coq_s_exact_divide = lazy (constant module_refl_path "O_EXACT_DIVIDE")
let coq_s_sum = lazy (constant module_refl_path "O_SUM")
let coq_s_state = lazy (constant module_refl_path "O_STATE")
let coq_s_contradiction = lazy (constant module_refl_path "O_CONTRADICTION")
let coq_s_merge_eq = lazy (constant module_refl_path "O_MERGE_EQ")
let coq_s_split_ineq =lazy (constant module_refl_path "O_SPLIT_INEQ")
let coq_s_constant_nul =lazy (constant module_refl_path "O_CONSTANT_NUL")
let coq_s_negate_contradict =lazy (constant module_refl_path "O_NEGATE_CONTRADICT")
let coq_s_negate_contradict_inv =lazy (constant module_refl_path "O_NEGATE_CONTRADICT_INV")

(* construction for the [extract_hyp] tactic *)
let coq_direction = lazy  (constant module_refl_path "direction")
let coq_d_left = lazy  (constant module_refl_path "D_left")
let coq_d_right = lazy  (constant module_refl_path "D_right")
let coq_d_mono = lazy  (constant module_refl_path "D_mono")

let coq_e_split = lazy  (constant module_refl_path "E_SPLIT")
let coq_e_extract = lazy  (constant module_refl_path "E_EXTRACT")
let coq_e_solve = lazy  (constant module_refl_path "E_SOLVE")

let coq_decompose_solve_valid = 
  lazy (constant  module_refl_path "decompose_solve_valid")
let coq_do_reduce_lhyps = lazy (constant  module_refl_path "do_reduce_lhyps")
let coq_do_omega = lazy (constant module_refl_path "do_omega")

*)
(* \subsection{Construction d'expressions} *)


let mk_var v = Term.mkVar (Names.id_of_string v)
let mk_plus t1 t2 = Term.mkApp (Lazy.force coq_Zplus,[|  t1; t2 |])
let mk_times t1 t2 = Term.mkApp (Lazy.force coq_Zmult, [| t1; t2 |])
let mk_minus t1 t2 = Term.mkApp (Lazy.force coq_Zminus, [| t1;t2 |])
let mk_eq t1 t2 = Term.mkApp (Lazy.force coq_eq, [| Lazy.force coq_Z; t1; t2 |])
let mk_le t1 t2 = Term.mkApp (Lazy.force coq_Zle, [|t1; t2 |])
let mk_gt t1 t2 = Term.mkApp (Lazy.force coq_Zgt, [|t1; t2 |])
let mk_inv t = Term.mkApp (Lazy.force coq_Zopp, [|t |])
let mk_and t1 t2 =  Term.mkApp (Lazy.force coq_and, [|t1; t2 |])
let mk_or t1 t2 =  Term.mkApp (Lazy.force coq_or, [|t1; t2 |])
let mk_not t = Term.mkApp (Lazy.force coq_not, [|t |])
let mk_eq_rel t1 t2 = Term.mkApp (Lazy.force coq_eq, [|
				Lazy.force coq_relation; t1; t2 |])
let mk_inj t = Term.mkApp (Lazy.force coq_inject_nat, [|t |])


let do_left t = 
  if t = Lazy.force coq_c_nop then Lazy.force coq_c_nop
  else Term.mkApp (Lazy.force coq_c_do_left, [|t |] )

let do_right t = 
  if t = Lazy.force coq_c_nop then Lazy.force coq_c_nop
  else Term.mkApp (Lazy.force coq_c_do_right, [|t |])

let do_both t1 t2 = 
  if t1 = Lazy.force coq_c_nop then do_right t2
  else if t2 = Lazy.force coq_c_nop then do_left t1
  else Term.mkApp (Lazy.force coq_c_do_both , [|t1; t2 |])

let do_seq t1 t2 =
  if t1 = Lazy.force coq_c_nop then t2
  else if t2 = Lazy.force coq_c_nop then t1
  else Term.mkApp (Lazy.force coq_c_do_seq, [|t1; t2 |])
  
let rec do_list = function
  | [] -> Lazy.force coq_c_nop
  | [x] -> x
  | (x::l) -> do_seq x (do_list l)

let mk_integer n =
  let rec loop n = 
    if n=Bigint.one then Lazy.force coq_xH else
      let (q,r) = Bigint.euclid n Bigint.two in
      Term.mkApp
        ((if r = Bigint.zero then Lazy.force coq_xO else Lazy.force coq_xI),
	[| loop q |]) in
    
    if n = Bigint.zero then Lazy.force coq_ZERO 
    else
      if Bigint.is_strictly_pos n then
        Term.mkApp (Lazy.force coq_POS, [| loop n |])
      else
        Term.mkApp (Lazy.force coq_NEG, [| loop (Bigint.neg n) |])

let mk_Z = mk_integer

let rec mk_nat = function
  | 0 -> Lazy.force coq_O
  | n -> Term.mkApp (Lazy.force coq_S, [| mk_nat (n-1) |])

let mk_list typ l =
  let rec loop = function
    | [] ->
	Term.mkApp (Lazy.force coq_nil, [|typ|])
    | (step :: l) -> 
	Term.mkApp (Lazy.force coq_cons, [|typ; step; loop l |]) in
  loop l

let mk_plist l =
  let rec loop = function
    | [] ->
	(Lazy.force coq_pnil)
    | (step :: l) -> 
	Term.mkApp (Lazy.force coq_pcons, [| step; loop l |]) in
  loop l


let mk_shuffle_list l = mk_list (Lazy.force coq_t_fusion) l

