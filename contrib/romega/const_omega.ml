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
		(Termops.id_of_global env (Nametab.ConstRef sp)),
              args)
    | Term.Construct csp , args ->
	Kapp (Names.string_of_id
		(Termops.id_of_global env (Nametab.ConstructRef csp)),
	        args)
    | Term.Ind isp, args ->
	Kapp (Names.string_of_id
		(Termops.id_of_global env (Nametab.IndRef isp)),args)
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
    | Term.Const sp         -> Nametab.ConstRef sp
    | Term.Construct csp -> Nametab.ConstructRef csp
    | Term.Ind isp       -> Nametab.IndRef isp
    | _ -> raise Destruct
  in
  Termops.id_of_global (Global.env()) ref, args

let recognize_number t =
  let rec loop t =
    let f,l = dest_const_apply t in
    match Names.string_of_id f,l with
       "xI",[t] -> 1 + 2 * loop t
     | "xO",[t] -> 2 * loop t 
     | "xH",[] -> 1
     | _ -> failwith "not a number" in
  let f,l = dest_const_apply t in
    match Names.string_of_id f,l with
       "POS",[t] -> loop t | "NEG",[t] -> - (loop t) | "ZERO",[] -> 0
     | _ -> failwith "not a number";;

let constant dir s =
  try
    Declare.global_absolute_reference
      (Names.make_path
        (Names.make_dirpath (List.map Names.id_of_string (List.rev dir)))
        (Names.id_of_string s))
  with e -> print_endline (String.concat "." dir); print_endline s; 
            raise e

let coq_xH = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "xH")
let coq_xO = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "xO")
let coq_xI = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "xI")
let coq_ZERO = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "ZERO")
let coq_POS = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "POS")
let coq_NEG = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "NEG")
let coq_Z = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "Z")
let coq_relation = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "relation")
let coq_SUPERIEUR = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "SUPERIEUR")
let coq_INFEEIEUR = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "INFERIEUR")
let coq_EGAL = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "EGAL")
let coq_Zplus = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "Zplus")
let coq_Zmult = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "Zmult")
let coq_Zopp = lazy (constant ["Coq"; "ZArith"; "fast_integer"] "Zopp")

(* auxiliaires zarith *)
let coq_Zminus = lazy (constant ["Coq"; "ZArith"; "zarith_aux"] "Zminus")
let coq_Zs = lazy (constant ["Coq"; "ZArith"; "zarith_aux"] "Zs")
let coq_Zgt = lazy (constant ["Coq"; "ZArith"; "zarith_aux"] "Zgt")
let coq_Zle = lazy (constant ["Coq"; "ZArith"; "zarith_aux"] "Zle")
let coq_inject_nat = lazy (constant ["Coq"; "ZArith"; "zarith_aux"] "inject_nat")

(* Peano *)
let coq_le = lazy(constant ["Init"; "Peano"] "le")
let coq_gt = lazy(constant ["Init"; "Peano"] "gt")

(* Datatypes *)
let coq_nat = lazy(constant ["Coq"; "Init"; "Datatypes"] "nat")
let coq_S = lazy(constant ["Coq"; "Init"; "Datatypes"] "S")
let coq_O = lazy(constant ["Coq"; "Init"; "Datatypes"] "O")

(* Minus *)
let coq_minus = lazy(constant ["Arith"; "Minus"] "minus")

(* Logic *)
let coq_eq = lazy(constant ["Init"; "Logic"] "eq")
let coq_refl_equal = lazy(constant ["Coq"; "Init"; "Logic"] "refl_equal")
let coq_and = lazy(constant ["Coq"; "Init"; "Logic"] "and")
let coq_not = lazy(constant ["Coq"; "Init"; "Logic"] "not")
let coq_or = lazy(constant ["Coq"; "Init"; "Logic"] "or")
let coq_ex = lazy(constant ["Coq"; "Init"; "Logic"] "ex")

(* Lists *)
let coq_cons =  lazy (constant ["Coq"; "Lists"; "PolyList"] "cons")
let coq_nil =  lazy (constant ["Coq"; "Lists"; "PolyList"] "nil")

let coq_t_nat = lazy (constant module_refl_path "Tint")
let coq_t_plus = lazy (constant module_refl_path "Tplus")
let coq_t_mult = lazy (constant module_refl_path "Tmult")
let coq_t_opp = lazy (constant module_refl_path "Topp")
let coq_t_minus = lazy (constant module_refl_path "Tminus")
let coq_t_var = lazy (constant module_refl_path "Tvar")
let coq_t_equal = lazy (constant module_refl_path "EqTerm")
let coq_t_leq = lazy (constant module_refl_path "LeqTerm")
let coq_t_geq = lazy (constant module_refl_path "GeqTerm")
let coq_t_lt = lazy (constant module_refl_path "LtTerm")
let coq_t_gt = lazy (constant module_refl_path "GtTerm")
let coq_t_neq = lazy (constant module_refl_path "NeqTerm")

let coq_proposition = lazy (constant module_refl_path "proposition")
let coq_interp_sequent = lazy (constant module_refl_path "interp_goal")
let coq_normalize_sequent = lazy (constant module_refl_path "normalize_goal")
let coq_execute_sequent = lazy (constant module_refl_path "execute_goal")
let coq_sequent_to_hyps = lazy (constant module_refl_path "goal_to_hyps")

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
    if n=1 then Lazy.force coq_xH else 
      Term.mkApp ((if n mod 2 = 0 then Lazy.force coq_xO else Lazy.force coq_xI),
		 [| loop (n/2) |]) in
    
    if n = 0 then Lazy.force coq_ZERO 
    else Term.mkApp ((if n > 0 then Lazy.force coq_POS else Lazy.force coq_NEG),
		     [| loop (abs n) |])

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

let mk_shuffle_list l = mk_list (Lazy.force coq_t_fusion) l

