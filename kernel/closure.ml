
(* $Id$ *)

open Util
open Pp
open Term
open Names
open Environ
open Instantiate
open Univ
open Evd
open Esubst


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
  mSGNL [< 'sTR"[Reds: beta=";'iNT !beta; 'sTR" delta="; 'iNT !delta;
	   'sTR" zeta="; 'iNT !zeta; 'sTR" evar="; 'iNT !evar;
           'sTR" iota="; 'iNT !iota; 'sTR" prune="; 'iNT !prune; 'sTR"]" >]

let with_stats c =
  if !stats then begin
    reset();
    let r = Lazy.force c in
    stop();
    r
  end else
    Lazy.force c

type evaluable_global_reference =
  | EvalVarRef of identifier
  | EvalConstRef of section_path

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

let unfold_red sp =
  let c = match sp with
    | EvalVarRef id -> false,[],[id]
    | EvalConstRef sp -> false,[sp],[]
  in {
  r_beta = true;
  r_const = c;
  r_zeta = true;   (* false for finer behaviour ? *)
  r_evar = false;
  r_iota = true }

(* Sets of reduction kinds.
   Main rule: delta implies all consts (both global (= by
   section_path) and local (= by Rel or Var)), all evars, and zeta (= letin's).
   Rem: reduction of a Rel/Var bound to a term is Delta, but reduction of 
   a LetIn expression is Letin reduction *)

type red_kind =
    BETA | DELTA | ZETA | EVAR | IOTA
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
  | EVAR -> { red with r_evar = true }
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


let incr_cnt red cnt =
  if red then begin
    if !stats then incr cnt;
    true
  end else 
    false

let red_delta_set red =
  let b,_,_ = red.r_const in b

let red_local_const = red_delta_set

(* to know if a redex is allowed, only a subset of red_kind is used ... *)
let red_set red = function
  | BETA -> incr_cnt red.r_beta beta
  | CONST [sp] -> 
      let (b,l,_) = red.r_const in
      let c = List.mem sp l in
      incr_cnt ((b & not c) or (c & not b)) delta
  | VAR id -> (* En attendant d'avoir des sp pour les Var *)
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

(* specification of the reduction function *)

type red_mode = UNIFORM | SIMPL | WITHBACK

type flags = red_mode * reds

(* (UNIFORM,r)  == r-reduce in any context
 * (SIMPL,r)    == bdi-reduce under cases or fix, r otherwise (like hnf does)
 * (WITHBACK,r) == internal use: means we are under a case or in rec. arg. of
 *                 fix
 *)

(* Examples *)
let no_flag = (UNIFORM,no_red)
let beta = (UNIFORM,beta_red)
let betaiota = (UNIFORM,betaiota_red)
let betadeltaiota = (UNIFORM,betadeltaiota_red)

let hnf_flags = (SIMPL,betaiotazeta_red)
let unfold_flags sp = (UNIFORM, unfold_red sp)

let flags_under = function
  | (SIMPL,r) -> (WITHBACK,r)
  | fl -> fl


(* Reductions allowed in "normal" circumstances: reduce only what is
 * specified by r *)

let red_top (_,r) rk = red_set r rk

(* Sometimes, we may want to perform a bdi reduction, to generate new redexes.
 * Typically: in the Simpl reduction, terms in recursive position of a fixpoint
 * are bdi-reduced, even if r is weaker.
 *
 * It is important to keep in mind that when we talk of "normal" or
 * "head normal" forms, it always refer to the reduction specified by r,
 * whatever the term context. *)

let red_under (md,r) rk =
  match md with
    | WITHBACK -> true
    | _ -> red_set r rk

(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
 *  * i_evc is the set of constraints for existential variables
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

type 'a table_key =
  | ConstBinding of constant
  | EvarBinding of (existential * 'a subs)
  | VarBinding of identifier
  | FarRelBinding of int

type ('a, 'b) infos = {
  i_flags : flags;
  i_repr : ('a, 'b) infos -> 'a subs -> constr -> 'a;
  i_env : env;
  i_evc : 'b evar_map;
  i_rels : int * (int * constr) list;
  i_vars : (identifier * constr) list;
  i_tab : ('a table_key, 'a) Hashtbl.t }

let info_flags info = info.i_flags

let ref_value_cache info ref =
  try  
    Some (Hashtbl.find info.i_tab ref)
  with Not_found ->
  try
    let body,subs =
      match ref with
	| FarRelBinding n ->
	    let (s,l) = info.i_rels in lift n (List.assoc (s-n) l), ESID 0
	| VarBinding id -> List.assoc id info.i_vars, ESID 0
	| EvarBinding (evc,subs) -> existential_value info.i_evc evc, subs
	| ConstBinding cst -> constant_value info.i_env cst, ESID 0
    in
    let v = info.i_repr info subs body in
    Hashtbl.add info.i_tab ref v;
    Some v
  with
    | Not_found (* List.assoc *)
    | NotInstantiatedEvar (* Evar *)
    | NotEvaluableConst _ (* Const *)
      -> None

let defined_vars flags env =
(*  if red_local_const (snd flags) then*)
    fold_named_context 
      (fun env (id,b,t) e ->
	 match b with
	   | None -> e
	   | Some body -> (id, body)::e)
      env []
(*  else []*)

let defined_rels flags env =
(*  if red_local_const (snd flags) then*)
  fold_rel_context 
      (fun env (id,b,t) (i,subs) ->
	 match b with
	   | None -> (i+1, subs)
	   | Some body -> (i+1, (i,body) :: subs))
      env (0,[])
(*  else (0,[])*)

let create mk_cl flgs env sigma =
  { i_flags = flgs;
    i_repr = mk_cl;
    i_env = env;
    i_evc = sigma;
    i_rels = defined_rels flgs env;
    i_vars = defined_vars flgs env;
    i_tab = Hashtbl.create 17 }


let infos_under infos = { infos with i_flags = flags_under infos.i_flags }


(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *) 

type 'a stack_member =
  | Zapp of 'a array * int
  | Zcase of case_info * 'a * 'a array
  | Zfix of 'a * 'a stack
  | Zshift of int
  | Zupdate of 'a

and 'a stack = 'a stack_member list

let empty_stack = []

let append_stackn v p s = if Array.length v = p then s else Zapp(v,p)::s
let append_stack v s = append_stackn v 0 s

(* Collapse the shifts in the stack *)
let zshift n s =
  match (n,s) with
      (0,_) -> s
    | (_,Zshift(k)::s) -> Zshift(n+k)::s
    | _ -> Zshift(n)::s

let rec stack_args_size = function
  | Zapp(v,n)::s -> Array.length v - n + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | Zupdate(_)::s -> stack_args_size s
  | _ -> 0

(* Parameterization: check the a given reduction is allowed in the
   context of the stack *)
let can_red info stk r =
  red_top info.i_flags r ||
  (fst info.i_flags = SIMPL &&
    List.exists (function (Zcase _|Zfix _) -> true | _ -> false) stk)


(* When used as an argument stack (only Zapp can appear) *)
let decomp_stack = function
  | Zapp(v,n)::s -> Some (v.(n), append_stackn v (n+1) s)
  | [] -> None
  | _ -> assert false
let decomp_stackn = function
  | Zapp(v,n)::s ->
      ((if n = 0 then v else Array.sub v n (Array.length v - n)), s)
  | _ -> assert false
let array_of_stack s =
  let rec stackrec = function
  | [] -> []
  | stk ->
      let (args,s) = decomp_stackn stk in
      args :: (stackrec s)
  in Array.concat (stackrec s)
let rec list_of_stack = function
  | [] -> []
  | stk ->
      let (args,s) = decomp_stackn stk in
      Array.fold_right (fun a l -> a::l) args (list_of_stack s)
let rec app_stack = function
  | f, [] -> f
  | f, stk -> 
      let (args,s) = decomp_stackn stk in
      app_stack (appvect (f, args), s)
let rec stack_assign s p c = match s with
  | Zapp(v,n)::s ->
      let q = Array.length v - n in 
      if p >= q then
	Zapp (v, n) :: stack_assign s (p-q) c
      else
	let v' = Array.sub v n q in
	v'.(p) <- c;
	Zapp (v',0) :: s
  | _ -> s
let rec stack_tail p s =
  if p = 0 then s else
    match s with
      | Zapp (v, n) :: s ->
	  let q = Array.length v - n in
	  if p >= q then stack_tail (p-q) s
	  else Zapp (v, n+p) :: s
      | _ -> failwith "stack_tail"
let rec stack_nth s p = match s with
  | Zapp (v, n) :: s ->
      let q = Array.length v - n in
      if p >= q then stack_nth s (p-q)
      else v.(p+n)
  | _ -> raise Not_found


(**********************************************************************)
(* Lazy reduction: the one used in kernel operations                  *)

(* type of shared terms. fconstr and frterm are mutually recursive.
 * Clone of the Generic.term structure, but completely mutable, and
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
  | FFlex of freference
  | FInd of inductive_path * fconstr array
  | FConstruct of constructor_path * fconstr array
  | FApp of fconstr * fconstr array
  | FFix of (int array * int) * (fconstr array * name list * fconstr array)
      * constr array * fconstr subs
  | FCoFix of int * (fconstr array * name list * fconstr array)
      * constr array * fconstr subs
  | FCases of case_info * fconstr * fconstr * fconstr array
  | FLambda of name * fconstr * fconstr * constr * fconstr subs
  | FProd of name * fconstr * fconstr * constr * fconstr subs
  | FLetIn of name * fconstr * fconstr * fconstr * constr * fconstr subs
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs

and freference =
  (* only vars as args of FConst ... exploited for caching *)
  | FConst of section_path * fconstr array
  | FEvar of (existential * fconstr subs)
  | FVar of identifier
  | FFarRel of int (* index in the rel_context part of _initial_ environment *)

let fterm_of v = v.term
let set_whnf v = if v.norm = Red then v.norm <- Whnf
let set_cstr v = if v.norm = Red then v.norm <- Cstr
let set_norm v = v.norm <- Norm
let is_val v = v.norm = Norm

(* Put an update mark in the stack, only if needed *)
let zupdate m s =
  if !share & m.norm = Red then Zupdate(m)::s else s

(* Could issue a warning if no is still Red, pointing out that we loose
   sharing. *)
let update v1 (no,t) =
  if !share then
    (v1.norm <- no;
     v1.term <- t;
     v1)
  else {norm=no;term=t}

let rec lft_fconstr n ft =
  match ft.term with
    FLIFT(k,m) -> lft_fconstr (n+k) m
  | _ -> {norm=ft.norm; term=FLIFT(n,ft)}
let lift_fconstr k f =
  if k=0 then f else lft_fconstr k f
let lift_fconstr_vect k v =
  if k=0 then v else Array.map (fun f -> lft_fconstr k f) v

let clos_rel e i =
  match expand_rel i e with
    | Inl(n,mt) -> lift_fconstr n mt
    | Inr(k,None) -> {norm=Red; term= FRel k}
    | Inr(k,Some p) ->
        lift_fconstr (k-p) {norm=Norm;term=FFlex(FFarRel p)}

(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let mk_clos e t =
  match kind_of_term t with
    | IsRel i -> clos_rel e i
    | IsVar x -> { norm = Red; term = FFlex (FVar x) }
    | IsMeta _ | IsSort _ ->  { norm = Norm; term = FAtom t }
    | (IsMutInd _|IsMutConstruct _|IsFix _|IsCoFix _
      |IsLambda _|IsProd _) ->
        {norm = Cstr; term = FCLOS(t,e)}
    | (IsApp _|IsMutCase _|IsCast _|IsConst _|IsEvar _|IsLetIn _) ->
        {norm = Red; term = FCLOS(t,e)}

let mk_clos_vect env v = Array.map (mk_clos env) v

(* Translate the head constructor of t from constr to fconstr. This
   function is parameterized by the function to apply on the direct
   subterms.
   Could be used insted of mk_clos. *)
let mk_clos_deep clos_fun env t =
  match kind_of_term t with
    | IsRel i -> clos_rel env i
    | (IsVar _|IsMeta _ | IsSort _) -> mk_clos env t
    | IsCast (a,b) ->
        { norm = Red;
          term = FCast (clos_fun env a, clos_fun env b)}
    | IsApp (f,v) ->
        { norm = Red;
	  term = FApp (clos_fun env f, Array.map (clos_fun env) v) }
    | IsMutInd (sp,v) ->
        { norm = Cstr; term = FInd (sp, Array.map (clos_fun env) v) }
    | IsMutConstruct (sp,v) ->
        { norm = Cstr; term = FConstruct (sp,Array.map (clos_fun env) v)}
    | IsConst (sp,v) ->
        { norm = Red;
	  term = FFlex (FConst (sp,Array.map (clos_fun env) v)) }
    | IsEvar (_,v as ev) ->
        { norm = Red;
	  term = FFlex (FEvar (ev, env)) }

    | IsMutCase (ci,p,c,v) ->
        { norm = Red;
	  term = FCases (ci, clos_fun env p, clos_fun env c,
			 Array.map (clos_fun env) v) }
    | IsFix (op,(tys,lna,bds)) ->
	let env' = subs_liftn (Array.length bds) env in
        { norm = Cstr;
	  term = FFix (op, (Array.map (clos_fun env) tys, lna,
			    Array.map (clos_fun env') bds),
		       bds, env) }
    | IsCoFix (op,(tys,lna,bds)) ->
	let env' = subs_liftn (Array.length bds) env in
        { norm = Cstr;
	  term = FCoFix (op, (Array.map (clos_fun env) tys, lna,
			      Array.map (clos_fun env') bds),
			 bds, env) }

    | IsLambda (n,t,c) ->
        { norm = Cstr;
	  term = FLambda (n, clos_fun env t,
			  clos_fun (subs_lift env) c,
			  c, env) }
    | IsProd (n,t,c)   ->
        { norm = Cstr;
	  term = FProd (n, clos_fun env t, 
			clos_fun (subs_lift env) c,
			c, env) }
    | IsLetIn (n,b,t,c) ->
        { norm = Red;
	  term = FLetIn (n, clos_fun env b, clos_fun env t,
			 clos_fun (subs_lift env) c,
			 c, env) }

(* The inverse of mk_clos_deep: move back to constr *)
let rec to_constr constr_fun lfts v =
  match v.term with
    | FRel i -> IsRel (reloc_rel i lfts)
    | FFlex (FFarRel p) -> IsRel (reloc_rel p lfts)
    | FFlex (FVar x) -> IsVar x
    | FAtom c ->
        (match kind_of_term c with
          | IsSort s -> IsSort s
          | IsMeta m -> IsMeta m
          | _ -> assert false)
    | FCast (a,b) ->
        IsCast (constr_fun lfts a, constr_fun lfts b)
    | FFlex (FConst (op,ve)) ->
	IsConst (op, Array.map (constr_fun lfts) ve)
    | FFlex (FEvar ((n,args),env)) ->
	let f a = constr_fun lfts (mk_clos env a) in
	IsEvar (n, Array.map f args)
    | FInd (op,ve) ->
	IsMutInd (op, Array.map (constr_fun lfts) ve)
    | FConstruct (op,ve) -> 
	IsMutConstruct (op, Array.map (constr_fun lfts) ve)
    | FCases (ci,p,c,ve) ->
	IsMutCase (ci, constr_fun lfts p,
		   constr_fun lfts c,
		   Array.map (constr_fun lfts) ve)
    | FFix (op,(tys,lna,bds),_,_) ->
	let lfts' = el_liftn (Array.length bds) lfts in
	IsFix (op, (Array.map (constr_fun lfts) tys, lna,
		    Array.map (constr_fun lfts') bds))
    | FCoFix (op,(tys,lna,bds),_,_) ->
	let lfts' = el_liftn (Array.length bds) lfts in
	IsCoFix (op, (Array.map (constr_fun lfts) tys, lna,
		      Array.map (constr_fun lfts') bds))
    | FApp (f,ve) ->
	IsApp (constr_fun lfts f,
	       Array.map (constr_fun lfts) ve)
    | FLambda (n,t,c,_,_)   ->
	IsLambda (n, constr_fun lfts t,
	             constr_fun (el_lift lfts) c)
    | FProd (n,t,c,_,_)   ->
	IsProd (n, constr_fun lfts t,
	           constr_fun (el_lift lfts) c)
    | FLetIn (n,b,t,c,_,_) ->
	IsLetIn (n, constr_fun lfts b,
	      constr_fun lfts t,
	      constr_fun (el_lift lfts) c)
    | FLIFT (k,a) -> to_constr constr_fun (el_shft k lfts) a
    | FCLOS (t,env) ->
        let fr = mk_clos_deep mk_clos env t in
        let unfv = update v (fr.norm,fr.term) in
        to_constr constr_fun lfts unfv

(* This function defines the correspondance between constr and
   fconstr. When we find a closure whose substitution is the identity,
   then we directly return the constr to avoid possibly huge
   reallocation. *)
let term_of_fconstr =
  let rec term_of_fconstr_lift lfts v =
    match v.term with
      | FCLOS(t,env) when is_subs_id env & is_lift_id lfts -> t
      | _ -> mk_constr (to_constr term_of_fconstr_lift lfts v) in
  term_of_fconstr_lift ELID



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
    | Zapp(_)::_ ->
        let (args,s) = decomp_stackn stk in
        zip zfun {norm=m.norm; term=FApp(m, Array.map zfun args)} s
    | Zcase(ci,p,br)::s ->
        let t = FCases(ci, zfun p, m, Array.map zfun br) in
        zip zfun {norm=m.norm; term=t} s
    | Zfix(fx,par)::s ->
        zip zfun fx (par @ append_stack [|m|] s)
    | Zshift(n)::s ->
        zip zfun (lift_fconstr n m) s
    | Zupdate(rf)::s ->
        zip zfun (update rf (m.norm,m.term)) s

let fapp_stack (m,stk) = zip (fun x -> x) m stk

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
    | (Zapp(_)::_) as stk ->
        let (args,s) = decomp_stackn stk in
        strip_rec (Zapp(args,0)::rstk)
          {norm=h.norm;term=FApp(h,args)} depth s
    | Zupdate(m)::s ->
        strip_rec rstk (update m (h.norm,h.term)) depth s
    | stk -> (depth,List.rev rstk, stk) in
  strip_rec [] head 0 stk


let rec get_nth_arg head n stk =
  assert (head.norm <> Red);
  let rec strip_rec rstk h depth n = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) (depth+k) n s
    | Zapp(v, p)::s' ->
        let q = Array.length v - p in
        if n >= q
        then
          let v' = if p = 0 then v else Array.sub v p q in
          strip_rec (Zapp(v',0)::rstk)
            {norm=h.norm;term=FApp(h,v')} depth (n-q) s'
        else
          let rstk' =
            if n = 0 then rstk else Zapp(Array.sub v p n,0)::rstk in
          (Some (List.rev rstk', v.(p+n)), append_stackn v (p+n+1) s')
    | Zupdate(m)::s ->
        strip_rec rstk (update m (h.norm,h.term)) depth n s
    | s -> (None, List.rev rstk @ s) in
  strip_rec [] head 0 n stk

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let get_arg h stk =
  let (depth,stk') = strip_update_shift h stk in
  match stk' with
      Zapp(v,p)::s -> (Some(depth,v.(p)), append_stackn v (p+1) s)
    | _ -> (None, zshift depth stk')


(* Iota reduction: extract the arguments to be passed to the Case
   branches *)
let rec reloc_rargs_rec depth stk =
  match stk with
      Zapp(_)::_ ->
        let (args,s) = decomp_stackn stk in
        Zapp(lift_fconstr_vect depth args,0) :: reloc_rargs_rec depth s
    | Zshift(k)::s -> if k=depth then s else reloc_rargs_rec (depth-k) s
    | _ -> stk

let reloc_rargs depth stk =
  if depth = 0 then stk else reloc_rargs_rec depth stk

let rec drop_parameters depth n stk =
  match stk with
      Zapp(v,p)::s ->
        let q = Array.length v - p in
        if n > q then drop_parameters depth (n-q) s
        else if n = q then reloc_rargs depth s
        else reloc_rargs depth (Zapp(v,p+n)::s)
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


(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
let rec knh m stk =
  match m.term with
    | FLIFT(k,a) -> knh a (zshift k stk)
    | FCLOS(t,e) -> knht e t (Zupdate(m)::stk)
    | FApp(a,b) -> knh a (append_stack b (zupdate m stk))
    | FCases(ci,p,t,br) -> knh t (Zcase(ci,p,br)::zupdate m stk)
    | FFix((ri,n),_,_,_) ->
        (set_whnf m;
         match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FCast(t,_) -> knh t stk
(* cases where knh stops *)
    | (FFlex _|FLetIn _) -> (m, stk)
    | (FRel _|FAtom _) -> (set_norm m; (m, stk))
    | (FLambda _|FConstruct _|FCoFix _|FInd _|FProd _) ->
        (set_whnf m; (m, stk))

(* The same for pure terms *)
and knht e t stk =
  match kind_of_term t with
    | IsApp(a,b) ->
        knht e a (append_stack (mk_clos_vect e b) stk)
    | IsMutCase(ci,p,t,br) ->
        knht e t (Zcase(ci, mk_clos e p, mk_clos_vect e br)::stk)
    | IsFix _ -> knh (mk_clos_deep mk_clos e t) stk
    | IsCast(a,b) -> knht e a stk
    | IsRel n -> knh (clos_rel e n) stk
    | (IsLambda _|IsProd _|IsMutConstruct _|IsCoFix _|IsMutInd _|
       IsLetIn _|IsConst _|IsVar _|IsEvar _|IsMeta _|IsSort _) ->
        (mk_clos_deep mk_clos e t, stk)


(***********************************************************************)

(* Computes a normal form from the result of knh. *)
let rec knr info m stk =
  match m.term with
  | FLambda(_,_,_,f,e) when can_red info stk BETA ->
      (match get_arg m stk with
          (Some(depth,arg),s) -> knit info (subs_shift_cons(depth,e,arg)) f s
        | (None,s) -> (m,s))
  | FFlex(FConst(sp,args)) when can_red info stk (CONST [sp]) ->
      let cst = (sp, Array.map term_of_fconstr args) in
      (match ref_value_cache info (ConstBinding cst) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(FEvar ev) when can_red info stk EVAR ->
(* In the case of evars, if it is not defined, then we do not set the
   flag to Norm, because it may be instantiated later on *)
      (match ref_value_cache info (EvarBinding ev) with
          Some v -> kni info v stk
        | None -> (m,stk))
  | FFlex(FVar id) when can_red info stk (VAR id) ->
      (match ref_value_cache info (VarBinding id) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(FFarRel k) when can_red info stk DELTA ->
      (match ref_value_cache info (FarRelBinding k) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FConstruct((sp,c),args) when can_red info stk IOTA ->
      (match strip_update_shift_app m stk with
          (depth, args, Zcase((cn,_),_,br)::s) ->
            let npar = stack_args_size args - cn.(c-1) in
            assert (npar>=0);
            let rargs = drop_parameters depth npar args in
            kni info br.(c-1) (rargs@s)
        | (_, cargs, Zfix(fx,par)::s) ->
            let rarg = fapp_stack(m,cargs) in
            let stk' = par @ append_stack [|rarg|] s in
            let efx = contract_fix_vect fx.term in
            kni info efx stk'
        | (_,args,s) -> (m,args@s))
  | FCoFix _ when can_red info stk IOTA ->
      (match strip_update_shift_app m stk with
          (_, args, ((Zcase((cn,_),_,br)::_) as stk')) ->
            let efx = contract_fix_vect m.term in
            kni info efx (args@stk')
        | (_,args,s) -> (m,args@s))
  | FLetIn (_,v,_,_,bd,e) when can_red info stk ZETA ->
      knit info (subs_cons(v,e)) bd stk
  | _ -> (m,stk)

(* Computes the weak head normal form of a term *)
and kni info m stk =
  let (hm,s) = knh m stk in
  knr info hm s
and knit info e t stk =
  let (ht,s) = knht e t stk in
  knr info ht s

let kh info v stk = fapp_stack(kni info v stk)

(***********************************************************************)

(* Computes the strong normal form of a term.
   1- Calls kni
   2- tries to rebuild the term. If a closure still has to be computed,
      calls itself recursively. *)
let rec kl info m =
  if is_val m then (incr prune; m)
  else
    let (nm,s) = kni info m [] in
    down_then_up info nm s

(* no redex: go up for atoms and already normalized terms, go down
   otherwise. *) 
and down_then_up info m stk =
  let nm =
    if is_val m then (incr prune; m) else 
      let nt =
      match m.term with
        | FLambda(na,ty,bd,f,e) ->
            FLambda(na, kl info ty, kl info bd, f, e)
        | FLetIn(na,a,b,c,f,e) ->
            FLetIn(na, kl info a, kl info b, kl info c, f, e)
        | FProd(na,dom,rng,f,e) ->
            FProd(na, kl info dom, kl info rng, f, e)
        | FInd(ind,args) ->
            FInd(ind, Array.map (kl info) args)
        | FConstruct(c,args) ->
            FConstruct(c, Array.map (kl info) args)
        | FCoFix(n,(ftys,na,fbds),bds,e) ->
            FCoFix(n,(Array.map (kl info) ftys, na,
                      Array.map (kl info) fbds),bds,e)
        | FFlex(FConst(sp,args)) ->
            FFlex(FConst(sp, Array.map (kl info) args))
        | FFlex(FEvar((i,args),e)) ->
            FFlex(FEvar((i,args),e))
        | t -> t in
      {norm=Norm;term=nt} in
(* Precondition: m.norm = Norm *)
  zip (kl info) nm stk


(* Initialization and then normalization *)

(* weak reduction *)
let whd_val info v =
  with_stats (lazy (term_of_fconstr (kh info v [])))

(* strong reduction *)
let norm_val info v =
  with_stats (lazy (term_of_fconstr (kl info v)))

let inject = mk_clos (ESID 0)

(* cache of constants: the body is computed only when needed. *)
type 'a clos_infos = (fconstr, 'a) infos

let create_clos_infos flgs env sigma =
  create (fun _ -> mk_clos) flgs env sigma

let unfold_reference info = function
  | FConst (op,v) -> 
      let cst = (op, Array.map (norm_val info) v) in
      ref_value_cache info (ConstBinding cst)
  | FEvar ev -> ref_value_cache info (EvarBinding ev)
  | FVar id -> ref_value_cache info (VarBinding id)
  | FFarRel p -> ref_value_cache info (FarRelBinding p)

(* Head normal form. *)

(* TODO: optimise *)
let rec strip_applstack k acc m =
  match m.term with
      FApp(a,b) ->
        strip_applstack k (append_stack (lift_fconstr_vect k b) acc) a
    | FLIFT(n,a) ->
        strip_applstack (k+n) acc a
    | FCLOS _ -> assert false
    | _ -> (k,m,acc)


let fhnf info v =
  strip_applstack 0 [] (kh info v [])

let fhnf_apply info k head appl =
  let stk = zshift k appl in
  strip_applstack 0 [] (kh info head stk)
