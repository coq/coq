
(* $Id$ *)

open Util
open Stamps
open Names
(* open Generic *)
open Sign
open Term
open Instantiate
open Environ
open Reduction
open Evd
open Typing
open Tacred
open Proof_trees
open Proof_type
open Logic
open Refiner
open Evar_refiner

let re_sig it gc = { it = it; sigma = gc }

(**************************************************************)
(* Operations for handling terms under a local typing context *)
(**************************************************************)

type 'a sigma   = 'a Proof_type.sigma;;
type validation = Proof_type.validation;;
type tactic     = Proof_type.tactic;;

let unpackage = Refiner.unpackage
let repackage = Refiner.repackage
let apply_sig_tac = Refiner.apply_sig_tac

let sig_it     = Refiner.sig_it
let sig_sig    = Refiner.sig_sig
let project    = compose ts_it sig_sig
let pf_env gls = (sig_it gls).evar_env
let pf_hyps gls = named_context (sig_it gls).evar_env

let pf_concl gls = (sig_it gls).evar_concl
(*
let pf_untyped_hyps gls  =
  let sign = Environ.named_context (pf_env gls) in
  map_sign_typ (fun x -> body_of_type x) sign
*)
let pf_hyps_types gls  =
  let sign = Environ.named_context (pf_env gls) in
  List.map (fun (id,_,x) -> (id,body_of_type x)) sign

let pf_nth_hyp_id gls n = let (id,c,t) = List.nth (pf_hyps gls) (n-1) in id

let pf_last_hyp gl = List.hd (pf_hyps gl)

let pf_get_hyp_typ gls id = 
  try 
    body_of_type (snd (lookup_id id (pf_hyps gls)))
  with Not_found -> 
    error ("No such hypothesis : " ^ (string_of_id id))

let pf_ids_of_hyps gls = ids_of_named_context (named_context (pf_env gls))

let pf_ctxt gls      = get_ctxt (sig_it gls)

let pf_interp_constr gls c =
  let evc = project gls in 
  Astterm.interp_constr evc (sig_it gls).evar_env c

let pf_interp_openconstr gls c =
  let evc = project gls in 
  Astterm.interp_openconstr evc (sig_it gls).evar_env c

let pf_interp_type gls c =
  let evc = project gls in 
  Astterm.interp_type evc (sig_it gls).evar_env c

let pf_global gls id = Declare.construct_reference (sig_it gls).evar_env CCI id

let pf_parse_const gls = compose (pf_global gls) id_of_string

let pf_execute gls =
  let evc = project gls in 
  Typing.unsafe_machine (sig_it gls).evar_env evc

let pf_reduction_of_redexp gls re c = 
  reduction_of_redexp re (pf_env gls) (project gls) c 

let pf_reduce redfun gls c       = redfun (pf_env gls) (project gls) c 

let pf_whd_betadeltaiota         = pf_reduce whd_betadeltaiota
let pf_whd_betadeltaiota_stack   = pf_reduce whd_betadeltaiota_stack
let pf_hnf_constr                = pf_reduce hnf_constr
let pf_red_product               = pf_reduce red_product
let pf_nf                        = pf_reduce nf
let pf_nf_betaiota               = pf_reduce nf_betaiota
let pf_compute                   = pf_reduce compute
let pf_unfoldn ubinds            = pf_reduce (unfoldn ubinds)
let pf_type_of                   = pf_reduce type_of

let pf_conv_x                   = pf_reduce is_conv
let pf_conv_x_leq               = pf_reduce is_conv_leq
let pf_const_value              = pf_reduce (fun env _ -> constant_value env)
let pf_one_step_reduce          = pf_reduce one_step_reduce
let pf_reduce_to_mind           = pf_reduce reduce_to_mind
let pf_reduce_to_ind            = pf_reduce reduce_to_ind

let hnf_type_of gls = compose (pf_whd_betadeltaiota gls) (pf_type_of gls)

let pf_check_type gls c1 c2 =
  let casted = mkCast (c1, c2) in pf_type_of gls casted

(************************************)
(* Tactics handling a list of goals *)
(************************************)

type transformation_tactic = proof_tree -> (goal list * validation)

type validation_list = proof_tree list -> proof_tree list

type tactic_list = (goal list sigma) -> (goal list sigma) * validation_list

let first_goal         = first_goal
let goal_goal_list     = goal_goal_list
let apply_tac_list     = apply_tac_list
let then_tactic_list   = then_tactic_list
let tactic_list_tactic = tactic_list_tactic
let tclFIRSTLIST       = tclFIRSTLIST
let tclIDTAC_list      = tclIDTAC_list


(********************************************************)
(* Functions for handling the state of the proof editor *)
(********************************************************)

type pftreestate = Refiner.pftreestate

let proof_of_pftreestate    = proof_of_pftreestate
let cursor_of_pftreestate   = cursor_of_pftreestate
let is_top_pftreestate      = is_top_pftreestate
let evc_of_pftreestate      = evc_of_pftreestate
let top_goal_of_pftreestate = top_goal_of_pftreestate
let nth_goal_of_pftreestate = nth_goal_of_pftreestate
let traverse                = traverse
let solve_nth_pftreestate   = solve_nth_pftreestate
let solve_pftreestate       = solve_pftreestate
let weak_undo_pftreestate   = weak_undo_pftreestate
let mk_pftreestate          = mk_pftreestate
let extract_pftreestate     = extract_pftreestate
let extract_open_pftreestate = extract_open_pftreestate
let first_unproven          = first_unproven
let last_unproven           = last_unproven
let nth_unproven            = nth_unproven
let node_prev_unproven      = node_prev_unproven
let node_next_unproven      = node_next_unproven
let next_unproven           = next_unproven
let prev_unproven           = prev_unproven
let top_of_tree             = top_of_tree
let frontier                = frontier
let change_constraints_pftreestate = change_constraints_pftreestate
let instantiate_pf     = instantiate_pf
let instantiate_pf_com = instantiate_pf_com

(***********************************)
(* Walking constraints re-exported *)
(***********************************)

type walking_constraints = Evar_refiner.walking_constraints
type 'a result_w_tactic  = walking_constraints -> walking_constraints * 'a
type w_tactic            = walking_constraints -> walking_constraints

let startWalk       = startWalk
let walking_THEN    = walking_THEN
let walking         = walking
let w_Focusing_THEN = w_Focusing_THEN
let w_Declare       = w_Declare
let w_Declare_At    = w_Declare_At
let w_Define        = w_Define
let w_Underlying    = w_Underlying
let w_env           = w_env
let w_hyps          = w_hyps
let w_type_of       = w_type_of
let w_IDTAC         = w_IDTAC
let w_ORELSE        = w_ORELSE
let w_add_sign      = w_add_sign
let ctxt_type_of    = ctxt_type_of

let w_defined_const wc k     = defined_constant (w_env wc) k
let w_defined_evar wc k      = Evd.is_defined (w_Underlying wc) k
let w_const_value wc         = constant_value (w_env wc)
let w_conv_x wc m n          = is_conv (w_env wc) (w_Underlying wc) m n
let w_whd_betadeltaiota wc c = whd_betadeltaiota (w_env wc) (w_Underlying wc) c
let w_hnf_constr wc c        = hnf_constr (w_env wc) (w_Underlying wc) c


(*************************************************)
(* Tacticals re-exported from the Refiner module.*)
(*************************************************)

(* A special exception for levels for the Fail tactic *)
exception FailError = Refiner.FailError

let tclIDTAC         = tclIDTAC
let tclORELSE        = tclORELSE
let tclTHEN          = tclTHEN
let tclTHENLIST      = tclTHENLIST
let tclTHEN_i        = tclTHEN_i
let tclTHENL         = tclTHENL
let tclTHENS         = tclTHENS
let tclTHENSI        = tclTHENSI
let tclREPEAT        = tclREPEAT
let tclFIRST         = tclFIRST
let tclSOLVE         = tclSOLVE
let tclTRY           = tclTRY
let tclTHENTRY       = tclTHENTRY
let tclCOMPLETE      = tclCOMPLETE
let tclAT_LEAST_ONCE = tclAT_LEAST_ONCE
let tclFAIL          = tclFAIL
let tclDO            = tclDO
let tclPROGRESS      = tclPROGRESS
let tclWEAK_PROGRESS = tclWEAK_PROGRESS
let tclNOTSAMEGOAL   = tclNOTSAMEGOAL
let tclINFO          = tclINFO

let unTAC            = unTAC


(********************************************)
(* Definition of the most primitive tactics *)
(********************************************)

let refiner = refiner

(* This does not check that the variable name is not here *)
let unsafe_introduction id =
  without_check
    (refiner (Prim { name = Intro; newids = [id];
                     hypspecs = []; terms = []; params = [] }))

let introduction id pf =
  refiner (Prim { name = Intro; newids = [id];
                  hypspecs = []; terms = []; params = [] }) pf

let intro_replacing whereid pf = 
  refiner (Prim { name = Intro_replacing; newids = [];
                  hypspecs = [whereid]; terms = []; params = [] }) pf

let refine c pf = 
  refiner (Prim { name = Refine; terms = [c];
		  hypspecs = []; newids = []; params = [] }) pf

let convert_concl c pf = 
  refiner (Prim { name = Convert_concl; terms = [c];
                  hypspecs = []; newids = []; params = [] }) pf

let convert_hyp id c pf = 
  refiner (Prim { name = Convert_hyp; hypspecs = [id];
                  terms = [c]; newids = []; params = []}) pf

let thin ids gl = 
  refiner (Prim { name = Thin; hypspecs = ids;
                  terms = []; newids = []; params = []}) gl

let move_hyp with_dep id1 id2 gl = 
  refiner (Prim { name = Move with_dep;
                  hypspecs = [id1;id2]; terms = [];
		  newids = []; params = []}) gl

let mutual_fix lf ln lar pf = 
  refiner (Prim { name = Fix; newids = lf;
                  hypspecs = []; terms = lar;
                  params = List.map Ast.num ln}) pf

let mutual_cofix lf lar pf = 
  refiner (Prim { name     = Cofix;
                  newids   = lf; hypspecs = [];
                  terms    = lar; params   = []}) pf
    
let rename_bound_var_goal gls =
  let { evar_env = env; evar_concl = cl } as gl = sig_it gls in 
  let ids = ids_of_named_context (Environ.named_context env) in
  convert_concl (rename_bound_var ids cl) gls
    

(***************************************)
(* The interpreter of defined tactics *)
(***************************************)

let vernac_tactic = vernac_tactic
let context       = context

let add_tactic = Refiner.add_tactic

let overwriting_tactic = Refiner.overwriting_add_tactic


(* Some combinators for parsing tactic arguments. 
   They transform the Coqast.t arguments of the tactic into 
   constr arguments *)

type ('a,'b) parse_combinator = ('a -> tactic) -> ('b -> tactic)

(* Inutile ?! réécrit plus loin 
let tactic_com tac t x = tac (pf_interp_constr x t) x
      
let tactic_com_sort tac t x = tac (pf_interp_type x t) x
      
let tactic_com_list tac tl x =
  let translate = pf_interp_constr x in 
  tac (List.map translate tl) x
    
let tactic_bind_list tac tl x =
  let translate = pf_interp_constr x in 
  tac (List.map (fun (b,c)->(b,translate c)) tl) x

let tactic_com_bind_list tac (c,tl) x =
  let translate = pf_interp_constr x in 
  tac (translate c,List.map (fun (b,c')->(b,translate c')) tl) x

let tactic_com_bind_list_list tac args gl =
  let translate (c,tl) = 
    (pf_interp_constr gl c,
     List.map (fun (b,c')->(b,pf_interp_constr gl c')) tl) in 
  tac (List.map translate args) gl
*)

(********************************************************)
(* Functions for hiding the implementation of a tactic. *)
(********************************************************)

(* hide_tactic s tac pr registers a tactic s under the name s *)

let hide_tactic  s tac  =
  add_tactic s tac;
  (fun args -> vernac_tactic(s,args))

(* overwriting_register_tactic s tac pr registers a tactic s under the
   name s even if a tactic of the same name is already registered *)

let overwrite_hidden_tactic s tac  =
  overwriting_add_tactic s tac;
  (fun args -> vernac_tactic(s,args))

let tactic_com = 

  fun tac t x -> tac (pf_interp_constr x t) x

let tactic_opencom = 
  fun tac t x -> tac (pf_interp_openconstr x t) x
      
let tactic_com_sort = 
  fun tac t x -> tac (pf_interp_type x t) x
      
let tactic_com_list =    
  fun tac tl x -> 
    let translate = pf_interp_constr x in 
    tac (List.map translate tl) x

let tactic_bind_list =
  fun tac tl x -> 
    let translate = pf_interp_constr x in 
    tac (List.map (fun (b,c)->(b,translate c)) tl) x

let tactic_com_bind_list =
  fun tac (c,tl) x -> 
    let translate = pf_interp_constr x in 
    tac (translate c,List.map (fun (b,c')->(b,translate c')) tl) x

let tactic_com_bind_list_list =
  fun tac args gl -> 
    let translate (c,tl) = 
      (pf_interp_constr gl c,
       List.map (fun (b,c')->(b,pf_interp_constr gl c')) tl)
    in 
    tac (List.map translate args) gl

(* Some useful combinators for hiding tactic implementations *)

type 'a hide_combinator = string -> ('a -> tactic) -> ('a -> tactic)

let hide_atomic_tactic s tac = 
  add_tactic s (function [] -> tac | _ -> assert false);
  vernac_tactic(s,[])

let overwrite_hidden_atomic_tactic s tac =
  overwriting_tactic s (function [] -> tac | _ -> assert false);
  vernac_tactic(s,[])


let hide_constr_comarg_tactic s tac =
  let tacfun = function 
    | [Constr c]    -> tac c
    | [Command com] -> tactic_com tac com
    | _ -> anomaly "hide_constr_comarg_tactic : neither CONSTR nor COMMAND"
  in 
  add_tactic s tacfun;
  (fun c -> vernac_tactic(s,[Constr c]),
   fun com -> vernac_tactic(s,[Command com]))
 
let overwrite_hidden_constr_comarg_tactic s tac =
  let tacfun = function 
    | [Constr c] -> tac c
    | [Command com] -> 
        (fun gls -> tac (pf_interp_constr gls com) gls)
    | _ -> 
	anomaly 
	  "overwrite_hidden_constr_comarg_tactic : neither CONSTR nor COMMAND"
  in 
  overwriting_tactic s tacfun;
  (fun c -> vernac_tactic(s,[(Constr c)]), 
   fun c -> vernac_tactic(s,[(Command c)]))

let hide_constr_tactic s tac =
  let tacfun = function 
    | [Constr c]    -> tac c
    | [Command com] -> tactic_com tac com
    | _ -> anomaly "hide_constr_tactic : neither CONSTR nor COMMAND"
  in 
  add_tactic s tacfun;
  (fun c  -> vernac_tactic(s,[(Constr c)]))

let hide_openconstr_tactic s tac =
  let tacfun = function 
    | [OpenConstr c] -> tac c
    | [Command com] -> tactic_opencom tac com
    | _ -> anomaly "hide_openconstr_tactic : neither OPENCONSTR nor COMMAND"
  in 
  add_tactic s tacfun;
  (fun c  -> vernac_tactic(s,[(OpenConstr c)]))

let hide_numarg_tactic s tac =
  let tacfun = (function [Integer n] -> tac n | _ -> assert false) in 
  add_tactic s tacfun;
  fun n -> vernac_tactic(s,[Integer n])

let hide_ident_tactic s tac =
  let tacfun = (function [Identifier id] -> tac id | _ -> assert false) in
  add_tactic s tacfun;
  fun id -> vernac_tactic(s,[Identifier id])
      
let hide_string_tactic s tac =
  let tacfun = (function [Quoted_string str] -> tac str | _ -> assert false) in
  add_tactic s tacfun;
  fun str -> vernac_tactic(s,[Quoted_string str])

let hide_identl_tactic s tac =
  let tacfun = (function [Clause idl] -> tac idl | _ -> assert false) in 
  add_tactic s tacfun;
  fun idl -> vernac_tactic(s,[Clause idl])

let hide_constrl_tactic s tac = 
  let tacfun = function 
    | ((Command com)::_) as al -> 
      	tactic_com_list tac 
          (List.map (function (Command com) -> com | _ -> assert false) al)
    | ((Constr com)::_) as al ->
      	tac (List.map (function (Constr c) -> c | _ -> assert false) al)
    | _ -> anomaly "hide_constrl_tactic : neither CONSTR nor COMMAND"
  in 
  add_tactic s tacfun;
  fun ids -> vernac_tactic(s,(List.map (fun id -> Constr id) ids))

let hide_bindl_tactic s tac = 
  let tacfun = function  
    | [Bindings  al] -> tactic_bind_list tac al
    | [Cbindings al] -> tac al
    | _ -> anomaly "hide_bindl_tactic : neither BINDINGS nor CBINDINGS"
  in 
  add_tactic s tacfun;
  fun bindl -> vernac_tactic(s,[Cbindings bindl])
      
let hide_cbindl_tactic s tac = 
  let tacfun = function 
    | [Command com; Bindings al] -> tactic_com_bind_list tac (com,al)
    | [Constr c; Cbindings al]  -> tac (c,al)
    | _ -> anomaly "hide_cbindl_tactic : neither CONSTR nor COMMAND"
  in 
  add_tactic s tacfun;
  fun (c,bindl) -> vernac_tactic(s,[Constr c; Cbindings bindl])
      
let hide_cbindll_tactic s tac = 
  let rec getcombinds = function 
    | ((Command com)::(Bindings al)::l) -> (com,al)::(getcombinds l)
    | []                                ->  [] 
    | _ -> anomaly "hide_cbindll_tactic : not the expected form" 
  in  
  let rec getconstrbinds = function
    | ((Constr c)::(Cbindings al)::l) -> (c,al)::(getconstrbinds l)
    | []                              ->  [] 
    | _ -> anomaly "hide_cbindll_tactic : not the expected form" 
  in  
  let rec putconstrbinds = function 
    | (c,binds)::l -> (Constr c)::(Cbindings binds)::(putconstrbinds l)
    |  []          -> [] 
  in
  let tacfun = function 
    | ((Command com)::_) as args -> 
      	tactic_com_bind_list_list tac (getcombinds args)
    | ((Constr com)::_) as args -> tac (getconstrbinds args)
    | _ -> anomaly "hide_cbindll_tactic : neither CONSTR nor COMMAND"
  in 
  add_tactic s tacfun;
  fun l -> vernac_tactic(s,putconstrbinds l)


(* Pretty-printers *)

open Pp
open Printer

let pr_com sigma goal com =
  prterm (rename_bound_var 
            (ids_of_named_context (named_context goal.evar_env)) 
            (Astterm.interp_constr sigma goal.evar_env com))

let pr_one_binding sigma goal = function
  | (Dep id,com)  -> [< print_id id ; 'sTR":=" ; pr_com sigma goal com >]
  | (NoDep n,com) -> [< 'iNT n ; 'sTR":=" ; pr_com sigma goal com >]
  | (Com,com)     -> [< pr_com sigma goal com >]

let pr_bindings sigma goal lb =
  let prf = pr_one_binding sigma goal in
  match lb with 
    | [] -> [< prlist_with_sep pr_spc prf lb >]
    | _  -> [<'sTR"with";'sPC;prlist_with_sep pr_spc prf lb >]
	  
let rec pr_list f = function
  | []   -> [<>] 
  | a::l1 -> [< (f a) ; pr_list f l1>]

let pr_gls gls =
  hOV 0 [< pr_decls (sig_sig gls) ; 'fNL ; pr_seq (sig_it gls) >]

let pr_glls glls =
  hOV 0 [< pr_decls (sig_sig glls) ; 'fNL ;
           prlist_with_sep pr_fnl pr_seq (sig_it glls) >]

let pr_tactic = Refiner.pr_tactic
