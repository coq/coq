(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Pp
open Term
open Names
open Declarations
open Environ
open Esubst
open Debug

let stats = ref false
let share = ref true

(* Profiling *)
let beta = ref 0
let delta = ref 0
let zeta = ref 0
let evar = ref 0
let iota = ref 0
let prune = ref 0

let reset () =
  beta := 0; delta := 0; zeta := 0; evar := 0; iota := 0; prune := 0

let stop() =
  msgnl (str "[Reds: beta=" ++ int !beta ++ str" delta=" ++ int !delta ++
	 str" zeta=" ++ int !zeta ++ str" evar=" ++ int !evar ++
         str" iota=" ++ int !iota ++ str" prune=" ++ int !prune ++ str"]")

let incr_cnt red cnt =
  if red then begin
    if !stats then incr cnt;
    true
  end else 
    false

let with_stats c =
  if !stats then begin
    reset();
    let r = Lazy.force c in
    stop();
    r
  end else
    Lazy.force c

type transparent_state = Idpred.t * KNpred.t

let all_opaque = (Idpred.empty, KNpred.empty)
let all_transparent = (Idpred.full, KNpred.full)

module type RedFlagsSig = sig
  type reds
  type red_kind
  val fBETA : red_kind
  val fDELTA : red_kind
  val fIOTA : red_kind
  val fZETA : red_kind
  val fCONST : constant -> red_kind
  val fVAR : identifier -> red_kind
  val no_red : reds
  val red_add : reds -> red_kind -> reds
  val red_sub : reds -> red_kind -> reds
  val red_add_transparent : reds -> transparent_state -> reds
  val mkflags : red_kind list -> reds
  val red_set : reds -> red_kind -> bool
  val red_get_const : reds -> bool * evaluable_global_reference list
end

module RedFlags = (struct

  (* [r_const=(true,cl)] means all constants but those in [cl] *)
  (* [r_const=(false,cl)] means only those in [cl] *)
  (* [r_delta=true] just mean [r_const=(true,[])] *)

  type reds = {
    r_beta : bool;
    r_delta : bool;
    r_const : transparent_state;
    r_zeta : bool;
    r_evar : bool;
    r_iota : bool }

  type red_kind = BETA | DELTA | IOTA | ZETA
	      | CONST of constant | VAR of identifier
  let fBETA = BETA
  let fDELTA = DELTA
  let fIOTA = IOTA
  let fZETA = ZETA
  let fCONST kn  = CONST kn
  let fVAR id  = VAR id
  let no_red = {
    r_beta = false;
    r_delta = false;
    r_const = all_opaque;
    r_zeta = false;
    r_evar = false;
    r_iota = false }

  let red_add red = function
    | BETA -> { red with r_beta = true }
    | DELTA -> { red with r_delta = true; r_const = all_transparent }
    | CONST kn ->
	let (l1,l2) = red.r_const in
	{ red with r_const = l1, KNpred.add kn l2 }
    | IOTA -> { red with r_iota = true }
    | ZETA -> { red with r_zeta = true }
    | VAR id ->
	let (l1,l2) = red.r_const in
	{ red with r_const = Idpred.add id l1, l2 }

  let red_sub red = function
    | BETA -> { red with r_beta = false }
    | DELTA -> { red with r_delta = false }
    | CONST kn ->
 	let (l1,l2) = red.r_const in
	{ red with r_const = l1, KNpred.remove kn l2 }
    | IOTA -> { red with r_iota = false }
    | ZETA -> { red with r_zeta = false }
    | VAR id ->
	let (l1,l2) = red.r_const in
	{ red with r_const = Idpred.remove id l1, l2 }

  let red_add_transparent red tr =
    { red with r_const = tr } 

  let mkflags = List.fold_left red_add no_red

  let red_set red = function
    | BETA -> incr_cnt red.r_beta beta
    | CONST kn -> 
	let (_,l) = red.r_const in
	let c = KNpred.mem kn l in
	incr_cnt c delta
    | VAR id -> (* En attendant d'avoir des kn pour les Var *)
	let (l,_) = red.r_const in
	let c = Idpred.mem id l in
	incr_cnt c delta
    | ZETA -> incr_cnt red.r_zeta zeta
    | IOTA -> incr_cnt red.r_iota iota
    | DELTA -> (* Used for Rel/Var defined in context *)
	incr_cnt red.r_delta delta

  let red_get_const red =
    let p1,p2 = red.r_const in
    let (b1,l1) = Idpred.elements p1 in
    let (b2,l2) = KNpred.elements p2 in
    if b1=b2 then
      let l1' = List.map (fun x -> EvalVarRef x) l1 in
      let l2' = List.map (fun x -> EvalConstRef x) l2 in
      (b1, l1' @ l2')
    else error "unrepresentable pair of predicate"

end : RedFlagsSig)

open RedFlags

let betadeltaiota = mkflags [fBETA;fDELTA;fZETA;fIOTA]
let betadeltaiotanolet = mkflags [fBETA;fDELTA;fIOTA]
let betaiota = mkflags [fBETA;fIOTA]
let beta = mkflags [fBETA]
let betaiotazeta = mkflags [fBETA;fIOTA;fZETA]
let unfold_red kn = 
  let flag = match kn with
    | EvalVarRef id -> fVAR id
    | EvalConstRef kn -> fCONST kn
  in (* Remove fZETA for finer behaviour ? *)
  mkflags [fBETA;flag;fIOTA;fZETA]

(************************* Obsolète
(* [r_const=(true,cl)] means all constants but those in [cl] *)
(* [r_const=(false,cl)] means only those in [cl] *)
type reds = {
  r_beta : bool;
  r_const : bool * constant_path list * identifier list;
  r_zeta : bool;
  r_evar : bool;
  r_iota : bool }

let betadeltaiota_red = {
  r_beta = true;
  r_const = true,[],[];
  r_zeta = true;
  r_evar = true;
  r_iota = true } 

let betaiota_red = {
  r_beta = true;
  r_const = false,[],[];
  r_zeta = false;
  r_evar = false;
  r_iota = true }
		     
let beta_red = {
  r_beta = true;
  r_const = false,[],[];
  r_zeta = false;
  r_evar = false;
  r_iota = false }

let no_red = {
  r_beta = false;
  r_const = false,[],[];
  r_zeta = false;
  r_evar = false;
  r_iota = false }

let betaiotazeta_red = {
  r_beta = true;
  r_const = false,[],[];
  r_zeta = true;
  r_evar = false;
  r_iota = true }

let unfold_red kn =
  let c = match kn with
    | EvalVarRef id -> false,[],[id]
    | EvalConstRef kn -> false,[kn],[]
  in {
  r_beta = true;
  r_const = c;
  r_zeta = true;   (* false for finer behaviour ? *)
  r_evar = false;
  r_iota = true }

(* Sets of reduction kinds.
   Main rule: delta implies all consts (both global (= by
   kernel_name) and local (= by Rel or Var)), all evars, and zeta (= letin's).
   Rem: reduction of a Rel/Var bound to a term is Delta, but reduction of 
   a LetIn expression is Letin reduction *)

type red_kind =
    BETA | DELTA | ZETA | IOTA
  | CONST of constant_path list | CONSTBUT of constant_path list
  | VAR of identifier | VARBUT of identifier

let rec red_add red = function
  | BETA -> { red with r_beta = true }
  | DELTA ->
      (match red.r_const with
	| _,_::_,[] | _,[],_::_ -> error "Conflict in the reduction flags"
	| _ -> { red with r_const = true,[],[]; r_zeta = true; r_evar = true })
  | CONST cl ->
      (match red.r_const with
	| true,_,_ -> error "Conflict in the reduction flags"
	| _,l1,l2 -> { red with r_const = false, list_union cl l1, l2 })
  | CONSTBUT cl ->
      (match red.r_const with
	| false,_::_,_ | false,_,_::_ ->
			   error "Conflict in the reduction flags"
	| _,l1,l2 ->
	    { red with r_const = true, list_union cl l1, l2;
		r_zeta = true; r_evar = true })
  | IOTA -> { red with r_iota = true }
  | ZETA -> { red with r_zeta = true }
  | VAR id ->
      (match red.r_const with
	| true,_,_ -> error "Conflict in the reduction flags"
	| _,l1,l2 -> { red with r_const = false, l1, list_union [id] l2 })
  | VARBUT cl ->
      (match red.r_const with
	| false,_::_,_ | false,_,_::_ ->
			   error "Conflict in the reduction flags"
	| _,l1,l2 ->
	    { red with r_const = true, l1, list_union [cl] l2;
		r_zeta = true; r_evar = true })

let red_delta_set red =
  let b,_,_ = red.r_const in b

let red_local_const = red_delta_set

(* to know if a redex is allowed, only a subset of red_kind is used ... *)
let red_set red = function
  | BETA -> incr_cnt red.r_beta beta
  | CONST [kn] -> 
      let (b,l,_) = red.r_const in
      let c = List.mem kn l in
      incr_cnt ((b & not c) or (c & not b)) delta
  | VAR id -> (* En attendant d'avoir des kn pour les Var *)
     let (b,_,l) = red.r_const in
      let c = List.mem id l in
      incr_cnt ((b & not c) or (c & not b)) delta
  | ZETA -> incr_cnt red.r_zeta zeta
  | EVAR -> incr_cnt red.r_zeta evar
  | IOTA -> incr_cnt red.r_iota iota
  | DELTA -> red_delta_set red (*Used for Rel/Var defined in context*)
  (* Not for internal use *)
  | CONST _ | CONSTBUT _ | VAR _ | VARBUT _ -> failwith "not implemented"

(* Gives the constant list *)
let red_get_const red =
  let b,l1,l2 = red.r_const in
  let l1' = List.map (fun x -> EvalConstRef x) l1 in
  let l2' = List.map (fun x -> EvalVarRef x) l2 in
  b, l1' @ l2'
fin obsolète **************)
(* specification of the reduction function *)


(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
 *  * i_tab is the cache table of the results
 *  * i_repr is the function to get the representation from the current
 *         state of the cache and the body of the constant. The result
 *         is stored in the table.
 *  * i_rels = (4,[(1,c);(3,d)]) means there are 4 free rel variables
 *    and only those with index 1 and 3 have bodies which are c and d resp.
 *  * i_vars is the list of _defined_ named variables.
 *
 * ref_value_cache searchs in the tab, otherwise uses i_repr to
 * compute the result and store it in the table. If the constant can't
 * be unfolded, returns None, but does not store this failure.  * This
 * doesn't take the RESET into account. You mustn't keep such a table
 * after a Reset.  * This type is not exported. Only its two
 * instantiations (cbv or lazy) are.
 *)

type table_key =
  | ConstKey of constant
  | VarKey of identifier
  | FarRelKey of int
   (* FarRel: index in the rel_context part of _initial_ environment *)

let prtk = function
  | ConstKey kn -> prn kn
  | VarKey id -> print_string (string_of_id id)
  | FarRelKey i -> print_char 'x'; print_int i

type 'a infos = {
  i_flags : reds;
  i_repr : 'a infos -> constr -> 'a;
  i_env : env;
  i_rels : int * (int * constr) list;
  i_vars : (identifier * constr) list;
  i_tab : (table_key, 'a) Hashtbl.t }

let info_flags info = info.i_flags

let ref_value_cache info ref =
  try  
    Some (Hashtbl.find info.i_tab ref)
  with Not_found ->
  try
    let body =
      match ref with
	| FarRelKey n ->
	    let (s,l) = info.i_rels in lift n (List.assoc (s-n) l)
	| VarKey id -> List.assoc id info.i_vars
	| ConstKey cst -> constant_value info.i_env cst
    in
    let v = info.i_repr info body in
    Hashtbl.add info.i_tab ref v;
    Some v
  with
    | Not_found (* List.assoc *)
    | NotEvaluableConst _ (* Const *)
      -> None

let defined_vars flags env =
(*  if red_local_const (snd flags) then*)
    fold_named_context 
      (fun env (id,b,t) e ->
	 match b with
	   | None -> e
	   | Some body -> (id, body)::e)
      env ~init:[]
(*  else []*)

let defined_rels flags env =
(*  if red_local_const (snd flags) then*)
  fold_rel_context 
      (fun env (id,b,t) (i,subs) ->
	 match b with
	   | None -> (i+1, subs)
	   | Some body -> (i+1, (i,body) :: subs))
      env ~init:(0,[])
(*  else (0,[])*)


let rec mind_equiv info kn1 kn2 = 
  kn1 = kn2 ||
	match (lookup_mind kn1 info.i_env).mind_equiv with
	    Some kn1' -> mind_equiv info kn2 kn1'
	  | None -> match (lookup_mind kn2 info.i_env).mind_equiv with
		Some kn2' -> mind_equiv info kn2' kn1
	      | None -> false

let create mk_cl flgs env =
  { i_flags = flgs;
    i_repr = mk_cl;
    i_env = env;
    i_rels = defined_rels flgs env;
    i_vars = defined_vars flgs env;
    i_tab = Hashtbl.create 17 }

(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *) 

type 'a stack_member =
  | Zapp of 'a list
  | Zcase of case_info * 'a * 'a array
  | Zfix of 'a * 'a stack
  | Zshift of int
  | Zupdate of 'a

and 'a stack = 'a stack_member list

let empty_stack = []
let append_stack_list = function
  | ([],s) -> s
  | (l1, Zapp l :: s) -> Zapp (l1@l) :: s
  | (l1, s) -> Zapp l1 :: s
let append_stack v s = append_stack_list (Array.to_list v, s)

(* Collapse the shifts in the stack *)
let zshift n s =
  match (n,s) with
      (0,_) -> s
    | (_,Zshift(k)::s) -> Zshift(n+k)::s
    | _ -> Zshift(n)::s

let rec stack_args_size = function
  | Zapp l::s -> List.length l + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | Zupdate(_)::s -> stack_args_size s
  | _ -> 0

(* When used as an argument stack (only Zapp can appear) *)
let rec decomp_stack = function
  | Zapp[v]::s -> Some (v, s)
  | Zapp(v::l)::s -> Some (v, (Zapp l :: s))
  | Zapp [] :: s -> decomp_stack s
  | _ -> None
let rec decomp_stackn = function
  | Zapp [] :: s -> decomp_stackn s
  | Zapp l :: s -> (Array.of_list l, s)
  | _ -> assert false
let array_of_stack s =
  let rec stackrec = function
  | [] -> []
  | Zapp args :: s -> args :: (stackrec s)
  | _ -> assert false
  in Array.of_list (List.concat (stackrec s))
let rec list_of_stack = function
  | [] -> []
  | Zapp args :: s -> args @ (list_of_stack s)
  | _ -> assert false
let rec app_stack = function
  | f, [] -> f
  | f, (Zapp [] :: s) -> app_stack (f, s)
  | f, (Zapp args :: s) -> 
      app_stack (applist (f, args), s)
  | _ -> assert false
let rec stack_assign s p c = match s with
  | Zapp args :: s ->
      let q = List.length args in 
      if p >= q then
	Zapp args :: stack_assign s (p-q) c
      else
        (match list_chop p args with
            (bef, _::aft) -> Zapp (bef@c::aft) :: s
          | _ -> assert false)
  | _ -> s
let rec stack_tail p s =
  if p = 0 then s else
    match s with
      | Zapp args :: s ->
	  let q = List.length args in
	  if p >= q then stack_tail (p-q) s
	  else
            let (_,aft) = list_chop p args in
            Zapp aft :: s
      | _ -> failwith "stack_tail"
let rec stack_nth s p = match s with
  | Zapp args :: s ->
      let q = List.length args in
      if p >= q then stack_nth s (p-q)
      else List.nth args p
  | _ -> raise Not_found


(**********************************************************************)
(* Lazy reduction: the one used in kernel operations                  *)

(* type of shared terms. fconstr and frterm are mutually recursive.
 * Clone of the constr structure, but completely mutable, and
 * annotated with booleans (true when we noticed that the term is
 * normal and neutral) FLIFT is a delayed shift; allows sharing
 * between 2 lifted copies of a given term FCLOS is a delayed
 * substitution applied to a constr
 *)
type red_state = Norm | Cstr | Whnf | Red

type fconstr = { 
  mutable norm: red_state; 
  mutable term: fterm }

and fterm =
  | FRel of int
  | FAtom of constr
  | FCast of fconstr * fconstr
  | FFlex of table_key
  | FInd of inductive
  | FConstruct of constructor
  | FApp of fconstr * fconstr array
  | FFix of (int array * int) * (name array * fconstr array * fconstr array)
      * constr array * fconstr subs
  | FCoFix of int * (name array * fconstr array * fconstr array)
      * constr array * fconstr subs
  | FCases of case_info * fconstr * fconstr * fconstr array
  | FLambda of name * fconstr * fconstr * constr * fconstr subs
  | FProd of name * fconstr * fconstr * constr * fconstr subs
  | FLetIn of name * fconstr * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential_key * fconstr array
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FLOCKED

let fterm_of v = v.term
let set_whnf v = if v.norm = Red then v.norm <- Whnf
let set_cstr v = if v.norm = Red then v.norm <- Cstr
let set_norm v = v.norm <- Norm
let is_val v = v.norm = Norm

(* Printing for debug *)

let prft imap =
  let rec prfc_rec fc = (* if fc.norm = Norm then prch '#'; *) prft_rec fc.term
  and pr_sep fc = prch ' '; prfc_rec fc
  and pr_bar fc = pr " | "; prfc_rec fc
  and pr_sub s = prch '{'; prs prfc_rec s; prch '}'
  and prft_rec = function
    | FRel i -> print_char 'x'; print_int i
    | FFlex tk -> prch '$'; prtk tk
    | FApp (f,va) ->
	if Array.length va <= 0 then prfc_rec f
	else print_char '('; prfc_rec f; Array.iter pr_sep va; print_char ')'
    | FFix ((_,i),(vn,_,_),_,_) -> pr_name vn.(i)
    | FCoFix (i,(vn,_,_),_,_) -> pr_name vn.(i)
    | FConstruct c -> pr_construct imap c
    | FInd i -> pr_ind imap i
    | FAtom c -> prc imap c
    | FCLOS (c,s) -> pr "(clos "; prc imap c; prch ' '; pr_sub s; prch ')'
    | FLOCKED -> pr "lock"
    | FLIFT (i,fc) -> prch '^'; pri i; prch '('; prfc_rec fc; prch ')'
    | FEvar (k,fcv) -> pr "(evar "; pri k; Array.iter pr_sep fcv; prch ')'
    | FLetIn (n,fc1,fc2,fc3,c,s) -> pr "(let "; pr_name n; pr " = "; prfc_rec fc1; pr " : "; prfc_rec fc2; pr " in "; prfc_rec fc3; prch ')'
    | FProd (n,fc1,fc2,c,s) -> prch '('; pr_name n; prch ':'; prfc_rec fc1; prch ')'; prfc_rec fc2
    | FLambda (n,fc1,fc2,c,s) -> prch '['; pr_name n; prch ':'; prfc_rec fc1; prch ']'; prfc_rec fc2
    | FCases (_,fc1,fc2,fcv) -> pr "(case "; prfc_rec fc2; pr " of"; Array.iter pr_bar fcv; prch ')'
    | FCast (fc1,fc2) -> pr "(cast "; prfc_rec fc1; pr " : "; prfc_rec fc2; prch ')'
  in prft_rec

let prfc imap fc = (* if fc.norm = Norm then prch '#'; *) prft imap fc.term

let prfcv imap fcv =
  if Array.length fcv = 0 then pr "<empty>"
  else
    let pr_sep i fc = if i>0 then pr ", "; prfc imap fc in
      Array.iteri pr_sep fcv

let prst imap =
  let rec prstrec s = prch '['; prlist prstm "," s; prch ']'
  and pr_sep fc = prch ' '; prfc imap fc
  and prstm = function
    | Zapp l -> prch '['; prlist (prfc imap) "," l; prch ']'
    | Zfix (f,s) -> pr "(fix "; prfc imap f; prstrec s; prch ')'
    | Zupdate fc -> pr "(up "; prfc imap fc; prch ')'
    | Zshift i -> prch '^'; pri i
    | Zcase (_,fc,fcv) -> pr "(case "; prfc imap fc; Array.iter pr_sep fcv; prch ')'
  in prstrec

let prc info = prc (imap info.i_env)
let prcv info = prcv (imap info.i_env)
let prft info = prft (imap info.i_env)
let prfc info = prfc (imap info.i_env)
let prfcv info = prfcv (imap info.i_env)
let prst info = prst (imap info.i_env)

let prcst info (t,stk) = prc info t; pr " "; prst info stk
let precst info (e,t,stk) =
  prch '{'; prs (prfc info) e; pr "} "; prc info t; pr " "; prst info stk
let prfcst info (m,stk) = prfc info m; pr " "; prst info stk

let enterc s info t = enter_pr s (prc info) t
let entercst s info t stk = enter_pr s (prcst info) (t,stk)
let enterecst s info e t stk = enter_pr s (precst info) (e,t,stk)
let enterfc s info = enter_pr s (prfc info)
let enterfcst s info m stk = enter_pr s (prfcst info) (m,stk)

let leavefc s info = leave_pr s (prfc info)
let leavefcst s info = leave_pr s (prfcst info)

(* Could issue a warning if no is still Red, pointing out that we loose
   sharing. *)
let update v1 (no,t) =
  if !share then
    (v1.norm <- no;
     v1.term <- t;
     v1)
  else {norm=no;term=t}

(* Lifting. Preserves sharing.
   lft_fconstr always create a new cell, while lift_fconstr avoids it
   when the lift is 0. *)
let rec lft_fconstr n ft =
  match ft.term with
    FLIFT(k,m) -> lft_fconstr (n+k) m
  | _ -> {norm=ft.norm; term=FLIFT(n,ft)}
let lift_fconstr k f =
  if k=0 then f else lft_fconstr k f
let lift_fconstr_vect k v =
  if k=0 then v else Array.map (fun f -> lft_fconstr k f) v
let lift_fconstr_list k l =
  if k=0 then l else List.map (fun f -> lft_fconstr k f) l


(* since the head may be reducible, we might introduce lifts of 0 *)
let compact_stack head stk =
  let rec strip_rec depth = function
    | Zshift(k)::s -> strip_rec (depth+k) s
    | Zupdate(m)::s ->
        (* Be sure to create a new cell otherwise sharing would be
           lost by the update operation *)
        let h' = lft_fconstr depth head in
        let _ = update m (h'.norm,h'.term) in
        strip_rec depth s
    | stk -> zshift depth stk in
  strip_rec 0 stk

(* Put an update mark in the stack, only if needed *)
let zupdate m s =
  if !share & m.norm = Red
  then
    let s' = compact_stack m s in
    let _ = m.term <- FLOCKED in
    Zupdate(m)::s'
  else s

let clos_rel pr_fun e i =
  match expand_rel pr_fun i e with
    | Inl(n,mt) -> lift_fconstr n mt
    | Inr(k,None) -> {norm=Red; term= FRel k}
    | Inr(k,Some p) ->
        lift_fconstr (k-p) {norm=Norm;term=FFlex(FarRelKey p)}

(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let rec mk_clos e t =
  match kind_of_term t with
    | Rel i -> clos_rel (fun _ -> prch '?') e i
    | Var x -> { norm = Red; term = FFlex (VarKey x) }
    | Meta _ | Sort _ ->  { norm = Norm; term = FAtom t }
    | Ind kn -> { norm = Norm; term = FInd kn }
    | Construct kn -> { norm = Cstr; term = FConstruct kn }
    | Evar (ev,args) ->
        { norm = Cstr; term = FEvar (ev,Array.map (mk_clos e) args) }
    | (Fix _|CoFix _|Lambda _|Prod _) ->
        {norm = Cstr; term = FCLOS(t,e)}
    | (App _|Case _|Cast _|Const _|LetIn _) ->
        {norm = Red; term = FCLOS(t,e)}

let mk_clos_vect env v = Array.map (mk_clos env) v

(* Translate the head constructor of t from constr to fconstr. This
   function is parameterized by the function to apply on the direct
   subterms.
   Could be used insted of mk_clos. *)
let mk_clos_deep clos_fun env t =
  match kind_of_term t with
    | (Rel _|Ind _|Construct _|Var _|Meta _ | Sort _|Evar _) ->
        mk_clos env t
    | Cast (a,b) ->
        { norm = Red;
          term = FCast (clos_fun env a, clos_fun env b)}
    | App (f,v) ->
        { norm = Red;
	  term = FApp (clos_fun env f, Array.map (clos_fun env) v) }
    | Const kn ->
        { norm = Red;
	  term = FFlex (ConstKey kn) }
    | Case (ci,p,c,v) ->
        { norm = Red;
	  term = FCases (ci, clos_fun env p, clos_fun env c,
			 Array.map (clos_fun env) v) }
    | Fix (op,(lna,tys,bds)) ->
	let env' = subs_liftn (Array.length bds) env in
        { norm = Cstr;
	  term = FFix
                   (op,(lna, Array.map (clos_fun env) tys,
                             Array.map (clos_fun env') bds),
                    bds, env) }
    | CoFix (op,(lna,tys,bds)) ->
	let env' = subs_liftn (Array.length bds) env in
        { norm = Cstr;
	  term = FCoFix
                   (op,(lna, Array.map (clos_fun env) tys,
	                     Array.map (clos_fun env') bds),
	            bds, env) }
    | Lambda (n,t,c) ->
        { norm = Cstr;
	  term = FLambda (n, clos_fun env t,
			  clos_fun (subs_lift env) c,
			  c, env) }
    | Prod (n,t,c)   ->
        { norm = Cstr;
	  term = FProd (n, clos_fun env t, 
			clos_fun (subs_lift env) c,
			c, env) }
    | LetIn (n,b,t,c) ->
        { norm = Red;
	  term = FLetIn (n, clos_fun env b, clos_fun env t,
			 clos_fun (subs_lift env) c,
			 c, env) }

(* The inverse of mk_clos_deep: move back to constr *)
let rec to_constr constr_fun lfts v =
  match v.term with
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (FarRelKey p) -> mkRel (reloc_rel p lfts)
    | FFlex (VarKey x) -> mkVar x
    | FAtom c ->
        (match kind_of_term c with
          | Sort s -> mkSort s
          | Meta m -> mkMeta m
          | _ -> assert false)
    | FCast (a,b) ->
        mkCast (constr_fun lfts a, constr_fun lfts b)
    | FFlex (ConstKey op) -> mkConst op
    | FInd op -> mkInd op
    | FConstruct op -> mkConstruct op
    | FCases (ci,p,c,ve) ->
	mkCase (ci, constr_fun lfts p,
                constr_fun lfts c,
		Array.map (constr_fun lfts) ve)
    | FFix (op,(lna,tys,bds),_,_) ->
	let lfts' = el_liftn (Array.length bds) lfts in
	mkFix (op, (lna, Array.map (constr_fun lfts) tys,
		         Array.map (constr_fun lfts') bds))
    | FCoFix (op,(lna,tys,bds),_,_) ->
	let lfts' = el_liftn (Array.length bds) lfts in
	mkCoFix (op, (lna, Array.map (constr_fun lfts) tys,
		           Array.map (constr_fun lfts') bds))
    | FApp (f,ve) ->
	mkApp (constr_fun lfts f,
	       Array.map (constr_fun lfts) ve)
    | FLambda (n,t,c,_,_)   ->
	mkLambda (n, constr_fun lfts t,
	             constr_fun (el_lift lfts) c)
    | FProd (n,t,c,_,_)   ->
	mkProd (n, constr_fun lfts t,
	           constr_fun (el_lift lfts) c)
    | FLetIn (n,b,t,c,_,_) ->
	mkLetIn (n, constr_fun lfts b,
	      constr_fun lfts t,
	      constr_fun (el_lift lfts) c)
    | FEvar (ev,args) -> mkEvar(ev,Array.map (constr_fun lfts) args)
    | FLIFT (k,a) -> to_constr constr_fun (el_shft k lfts) a
    | FCLOS (t,env) ->
        let fr = mk_clos_deep mk_clos env t in
        let unfv = update v (fr.norm,fr.term) in
        to_constr constr_fun lfts unfv
    | FLOCKED -> anomaly "Closure.to_constr: found locked term"

(* This function defines the correspondance between constr and
   fconstr. When we find a closure whose substitution is the identity,
   then we directly return the constr to avoid possibly huge
   reallocation. *)
let term_of_fconstr lams =
  let rec term_of_fconstr_lift lfts v =
    match v.term with
      | FCLOS(t,env) when is_subs_id env & is_lift_id lfts -> t
      | _ -> to_constr term_of_fconstr_lift lfts v in
    term_of_fconstr_lift (ELID lams)



(* fstrong applies unfreeze_fun recursively on the (freeze) term and
 * yields a term.  Assumes that the unfreeze_fun never returns a
 * FCLOS term. 
let rec fstrong unfreeze_fun lfts v =
  to_constr (fstrong unfreeze_fun) lfts (unfreeze_fun v)
*)

(* TODO: the norm flags are not handled properly *)
let rec zip zfun m stk =
  match stk with
    | [] -> m
    | Zapp args :: s ->
        let args = Array.of_list args in
        zip zfun {norm=m.norm; term=FApp(m, Array.map zfun args)} s
    | Zcase(ci,p,br)::s ->
        let t = FCases(ci, zfun p, m, Array.map zfun br) in
        zip zfun {norm=m.norm; term=t} s
    | Zfix(fx,par)::s ->
        zip zfun fx (par @ append_stack_list ([m], s))
    | Zshift(n)::s ->
        zip zfun (lift_fconstr n m) s
    | Zupdate(rf)::s ->
        zip zfun (update rf (m.norm,m.term)) s

(* let fapp_stack (m,stk) = zip (fun x -> x) m stk *)

let fapp_stack info =
  let rec fapp m stk =
    enterfcst "fapp_stack" info m stk; leavefc "fapp_stack" info (match stk with
      | [] -> m
      | Zapp args :: s ->
	  fapp {m with term = FApp(m,Array.of_list args)} s
      | Zcase(ci,p,br)::s ->
          fapp {m with term = FCases(ci,p,m,br)} s
      | Zfix(fx,par)::s ->
          fapp fx (par @ append_stack_list ([m],s))
      | Zshift(n)::s ->
          fapp (lift_fconstr n m) s
      | Zupdate(rf)::s ->
          fapp (update rf (m.norm,m.term)) s)
  in fun (m,stk) -> fapp m stk

(*********************************************************************)

(* The assertions in the functions below are granted because they are
   called only when m is a constructor, a cofix
   (strip_update_shift_app), a fix (get_nth_arg) or an abstraction
   (strip_update_shift, through get_arg). *)

(* optimised for the case where there are no shifts... *)
let strip_update_shift head stk =
  assert (head.norm <> Red);
  let rec strip_rec h depth = function
    | Zshift(k)::s -> strip_rec (lift_fconstr k h) (depth+k) s
    | Zupdate(m)::s ->
        strip_rec (update m (h.norm,h.term)) depth s
    | stk -> (depth,stk) in
  strip_rec head 0 stk

(* optimised for the case where there are no shifts... *)
let strip_update_shift_app head stk =
  assert (head.norm <> Red);
  let rec strip_rec rstk h depth = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) (depth+k) s
    | (Zapp args :: s) as stk ->
        strip_rec (Zapp args :: rstk)
          {norm=h.norm;term=FApp(h,Array.of_list args)} depth s
    | Zupdate(m)::s ->
        strip_rec rstk (update m (h.norm,h.term)) depth s
    | stk -> (depth,List.rev rstk, stk) in
  strip_rec [] head 0 stk


let rec get_nth_arg head n stk =
  assert (head.norm <> Red);
  let rec strip_rec rstk h depth n = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) (depth+k) n s
    | Zapp args::s' ->
        let q = List.length args in
        if n >= q
        then
          strip_rec (Zapp args::rstk)
            {norm=h.norm;term=FApp(h,Array.of_list args)} depth (n-q) s'
        else
          (match list_chop n args with
              (bef, v::aft) -> 
                let stk' =
                  List.rev (if n = 0 then rstk else (Zapp bef :: rstk)) in
                (Some (stk', v), append_stack_list (aft,s'))
            | _ -> assert false)
    | Zupdate(m)::s ->
        strip_rec rstk (update m (h.norm,h.term)) depth n s
    | s -> (None, List.rev rstk @ s) in
  strip_rec [] head 0 n stk

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let get_arg h stk =
  let (depth,stk') = strip_update_shift h stk in
  match  decomp_stack stk' with
      Some (v, s') -> (Some (depth,v), s')
    | None -> (None, zshift depth stk')


(* Iota reduction: extract the arguments to be passed to the Case
   branches *)
let rec reloc_rargs_rec depth stk =
  match stk with
      Zapp args :: s ->
        Zapp (lift_fconstr_list depth args) :: reloc_rargs_rec depth s
    | Zshift(k)::s -> if k=depth then s else reloc_rargs_rec (depth-k) s
    | _ -> stk

let reloc_rargs depth stk =
  if depth = 0 then stk else reloc_rargs_rec depth stk

let rec drop_parameters depth n stk =
  match stk with
      Zapp args::s ->
        let q = List.length args in
        if n > q then drop_parameters depth (n-q) s
        else if n = q then reloc_rargs depth s
        else
          let (_,aft) = list_chop n args in
          reloc_rargs depth (append_stack_list (aft,s))
    | Zshift(k)::s -> drop_parameters (depth-k) n s
    | [] -> assert (n=0); []
    | _ -> assert false (* we know that n < stack_args_size(stk) *)


(* Iota reduction: expansion of a fixpoint.
 * Given a fixpoint and a substitution, returns the corresponding
 * fixpoint body, and the substitution in which it should be
 * evaluated: its first variables are the fixpoint bodies
 *
 * FCLOS(fix Fi {F0 := T0 .. Fn-1 := Tn-1}, S)
 *    -> (S. FCLOS(F0,S) . ... . FCLOS(Fn-1,S), Ti)
 *)
(* does not deal with FLIFT *)
let contract_fix_vect fix =
  let (thisbody, make_body, env, nfix) =
    match fix with
      | FFix ((reci,i),def,bds,env) ->
          (bds.(i),
	   (fun j -> { norm = Whnf; term = FFix ((reci,j),def,bds,env) }),
	   env, Array.length bds)
      | FCoFix (i,def,bds,env) ->
          (bds.(i),
	   (fun j -> { norm = Whnf; term = FCoFix (j,def,bds,env) }),
	   env, Array.length bds)
      | _ -> anomaly "Closure.contract_fix_vect: not a (co)fixpoint" 
  in
  let rec subst_bodies_from_i i env =
    if i = nfix then
      mk_clos env thisbody
    else
      subst_bodies_from_i (i+1) (subs_cons (make_body i, env))
  in       
  subst_bodies_from_i 0 env

(* access functions for rewriting *)

let is_rule_defined info fl v =
  match fl with
    | ConstKey kn ->
	lookup_rules kn info.i_env <> [] &
	arity (lookup_constant kn info.i_env) <= stack_args_size v
    | _ -> false

let is_free info = function
  | ConstKey kn -> is_free (lookup_constant kn info.i_env)
  | _ -> true

let cime_env info = cime info.i_env

let add_delta info = { info with i_flags = red_add info.i_flags fDELTA }

(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
let rec knh info m stk =
  enterfcst "knh" info m stk; leavefcst "knh" info (match m.term with
    | FLIFT(k,a) -> knh info a (zshift k stk)
    | FCLOS(t,e) -> knht info e t (Zupdate(m)::stk)
    | FLOCKED -> anomaly "Closure.knh: found lock"
    | FApp(a,b) -> knh info a (append_stack b (zupdate m stk))
    | FCases(ci,p,t,br) -> knh info t (Zcase(ci,p,br)::zupdate m stk)
    | FFix((ri,n),_,_,_) ->
        branch "knh" "fix";(set_whnf m;
         match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh info arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FCast(t,_) -> knh info t stk
(* cases where knh stops *)
    | (FFlex _|FLetIn _|FConstruct _|FEvar _) -> (m, stk)
    | (FRel _|FAtom _|FInd _) -> (set_norm m; (m, stk))
    | (FLambda _|FCoFix _|FProd _) ->
        (set_whnf m; (m, stk)))

(* The same for pure terms *)
and knht info e t stk =
  enterecst "knht" info e t stk; leavefcst "knht" info (match kind_of_term t with
    | App(a,b) ->
        knht info e a (append_stack (mk_clos_vect e b) stk)
    | Case(ci,p,t,br) ->
        knht info e t (Zcase(ci, mk_clos e p, mk_clos_vect e br)::stk)
    | Fix _ -> knh info (mk_clos_deep mk_clos e t) stk
    | Cast(a,b) -> knht info e a stk
    | Rel n -> knh info (clos_rel (prfc info) e n) stk
    | (Lambda _|Prod _|Construct _|CoFix _|Ind _|
       LetIn _|Const _|Term.Var _|Evar _|Meta _|Sort _) ->
        (mk_clos_deep mk_clos e t, stk))


(***********************************************************************)

(* Computes a normal form from the result of knh without trying to rewrite. *)
let rec knr_old info lams m stk =
  enterfcst "knr_old" info m stk; leavefcst "knr_old" info (match m.term with
  | FLambda(_,_,_,f,e) when red_set info.i_flags fBETA ->
      (match get_arg m stk with
          (Some(depth,arg),s) -> knit info lams (subs_shift_cons(depth,e,arg)) f s
        | (None,s) -> (m,s))
  | FFlex(ConstKey kn) when red_set info.i_flags (fCONST kn) ->
      branch_pr"knr_old""flag set"prn kn;(match ref_value_cache info (ConstKey kn) with
           Some v -> kni info lams v stk
         | None -> (set_norm m; (m,stk)))
  | FFlex(ConstKey kn) when not (red_set info.i_flags (fCONST kn)) ->
      branch_pr"knr_old""NOT SET"prn kn;(m,stk)
  | FFlex(VarKey id) when red_set info.i_flags (fVAR id) ->
      (match ref_value_cache info (VarKey id) with
          Some v -> kni info lams v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(FarRelKey k) when red_set info.i_flags fDELTA ->
      (match ref_value_cache info (FarRelKey k) with
          Some v -> kni info lams v stk
        | None -> (set_norm m; (m,stk)))
  | FConstruct(ind,c) when red_set info.i_flags fIOTA ->
      (match strip_update_shift_app m stk with
          (depth, args, Zcase(ci,_,br)::s) ->
            assert (ci.ci_npar>=0);
            let rargs = drop_parameters depth ci.ci_npar args in
            kni info lams br.(c-1) (rargs@s)
        | (_, cargs, Zfix(fx,par)::s) ->
            let rarg = fapp_stack info (m,cargs) in
            let stk' = par @ append_stack [|rarg|] s in
            let efx = contract_fix_vect fx.term in
            kni info lams efx stk'
        | (_,args,s) -> (m,args@s))
  | FCoFix _ when red_set info.i_flags fIOTA ->
      (match strip_update_shift_app m stk with
          (_, args, ((Zcase _::_) as stk')) ->
            let efx = contract_fix_vect m.term in
            kni info lams efx (args@stk')
        | (_,args,s) -> (m,args@s))
  | FLetIn (_,v,_,_,bd,e) when red_set info.i_flags fZETA ->
      knit info lams (subs_cons(v,e)) bd stk
  | _ -> (m,stk))

(* Computes a normal form from the result of knh. *)
and knr info lams m stk =
  enterfcst "knr" info m stk; leavefcst "knr" info (match m.term with
  | FFlex (ConstKey kn as fl) when red_set info.i_flags fIOTA
      & lookup_rules kn info.i_env <> []
      & stack_args_size stk >= arity (lookup_constant kn info.i_env) ->
      (branch"knr""test rewriting";match kind_of_term (term_of_fconstr lams (fapp_stack info (m,stk))) with
	 | App (f,va) -> branch_pr "knr" "args:" (prcv info) va;
	     let norm = klt (add_delta info) lams in
	     let va' = Array.map norm va in branch_pr "knr" "args':" (prfcv info) va';
	     let c = mkApp (f, Array.map (term_of_fconstr lams) va') in
	       (match kind_of_term f with
		  | Const kn' when kn'=kn ->
			(match Cime.normalize (cime_env info) c with
			   | Some c' -> branch_pr "knr" "cime result" (prc info) c';knit info lams (ESID lams) c' []
			   | _ -> branch"knr""no cime nf";(* knr_old info lams m stk *)
			       let m,stk = knht info (ESID lams) c [] in
				  set_norm m; m,stk)
		  | Fix _ | CoFix _ -> (* knr_old info lams m stk *)
		      let m,stk = knht info (ESID lams) c [] in
			knr_old info lams m stk
		  | _ -> knr_old info lams m stk)
	 | _ -> knr_old info lams m stk)
  | _ -> knr_old info lams m stk)

(* Computes the weak head normal form of a term *)
and kni info lams m stk =
  enterfcst "kni" info m stk; leavefcst "kni" info (let (hm,s) = knh info m stk in
  knr info lams hm s)

and knit info lams e t stk =
  let (ht,s) = knht info e t stk in
  knr info lams ht s

and kh info v stk = fapp_stack info (kni info 0 v stk)

(***********************************************************************)

(* Computes the strong normal form of a term.
   1- Calls kni
   2- tries to rebuild the term. If a closure still has to be computed,
      calls itself recursively. *)
and kl info lams m =
  enterfc "kl" info m; leavefc "kl" info (if is_val m then (incr prune; m)
  else
    let (nm,s) = kni info lams m [] in
    down_then_up info lams nm s)

and klt info lams t =
  enterc "klt" info t; leavefc "klt" info (
    let (nm,s) = knit info lams (ESID lams) t [] in
    down_then_up info lams nm s)

(* no redex: go up for atoms and already normalized terms, go down
   otherwise. *) 
and down_then_up info lams m stk =
  enterfcst "down_then_up" info m stk; leavefc "down_then_up" info (let nm =
    if is_val m then (incr prune; m) else 
      let nt =
      match m.term with
        | FLambda(na,ty,bd,f,e) ->
            FLambda(na, kl info lams ty, kl info lams bd, f, e)
        | FLetIn(na,a,b,c,f,e) ->
            FLetIn(na, kl info lams a, kl info lams b, kl info lams c, f, e)
        | FProd(na,dom,rng,f,e) ->
            FProd(na, kl info lams dom, kl info lams rng, f, e)
        | FCoFix(n,(na,ftys,fbds),bds,e) ->
            FCoFix(n,(na, Array.map (kl info lams) ftys,
                          Array.map (kl info lams) fbds),bds,e)
        | FEvar(i,args) -> FEvar(i, Array.map (kl info lams) args)
        | t -> t in
      {norm=Norm;term=nt} in
(* Precondition: m.norm = Norm *)
  zip (kl info lams) nm stk)

let whd_val_rew info v = term_of_fconstr 0 (kh info v [])

let norm_val_rew info lams v = term_of_fconstr lams (kl info lams v)

(* Initialization and then normalization *)

(* weak reduction *)
let whd_val info v = with_stats (lazy (whd_val_rew info v))

(* strong reduction *)
let norm_val info lams v = with_stats (lazy (norm_val_rew info lams v))

let inject = mk_clos (ESID 0)

let whd_stack = kni

(* cache of constants: the body is computed only when needed. *)
type clos_infos = fconstr infos

let create_clos_infos flgs env =
  create (fun _ -> inject) flgs env

let unfold_reference = ref_value_cache

