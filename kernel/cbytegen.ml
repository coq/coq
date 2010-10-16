(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Author: Benjamin Grégoire as part of the bytecode-based virtual reduction
   machine, Oct 2004 *)
(* Extension: Arnaud Spiwack (support for native arithmetic), May 2005 *)

open Util
open Names
open Term
open Native
open Cbytecodes
open Cemitcodes
open Declarations
open Pre_env
open Clambda
open Pp

(* Compilation of variables + computing free variables                    *)

(* The virtual machine doesn't distinguish closures and their environment *)

(* Representation of function environments :                              *)
(*        [clos_t | code | fv1 | fv2 | ... | fvn ]                        *)
(*                ^                                                       *)
(*  The offset for accessing free variables is 1 (we must skip the code   *)
(*  pointer).                                                             *)
(*  While compiling, free variables are stored in [in_env] in order       *)
(*  opposite to machine representation, so we can add new free variables  *)
(*  easily (i.e. without changing the position of previous variables)     *)
(* Function arguments are on the stack in the same order as the           *)
(* application :  f arg1 ... argn                                         *)
(*   - the stack is then :                                                *)
(*        arg1 : ... argn : extra args : return addr : ...                *)
(* In the function body [arg1] is represented by de Bruijn [n], and       *)
(* [argn] by de Bruijn [1]                                                *)

(* Representation of environements of mutual fixpoints :                  *)
(* [t1|C1| ... |tc|Cc| ... |t(nbr)|C(nbr)| fv1 | fv2 | .... | fvn | type] *)
(*                ^<----------offset--------->                            *)
(* type = [Ct1 | .... | Ctn]                                              *)
(* Ci is the code pointer of the i-th body                                *)
(* At runtime, a fixpoint environment (which is the same as the fixpoint  *)
(* itself) is a pointer to the field holding its code pointer.            *)
(* In each fixpoint body, de Bruijn [nbr] represents the first fixpoint   *)
(* and de Bruijn [1] the last one.                                        *)
(* Access to these variables is performed by the [Koffsetclosure n]       *)
(* instruction that shifts the environment pointer of [n] fields.         *)

(* This allows to represent mutual fixpoints in just one block.           *)
(* [Ct1 | ... | Ctn] is an array holding code pointers of the fixpoint    *)
(* types. They are used in conversion tests (which requires that          *)
(* fixpoint types must be convertible). Their environment is the one of   *)
(* the last fixpoint :                                                    *)
(* [t1|C1| ... |tc|Cc| ... |t(nbr)|C(nbr)| fv1 | fv2 | .... | fvn | type] *)
(*                                ^                                       *)

(* Representation of mutual cofix :                                       *)
(*  a1 =   [A_t | accumulate | [Cfx_t | fcofix1 ] ]                       *)
(*                ...                                                     *)
(*  anbr = [A_t | accumulate | [Cfx_t | fcofixnbr ] ]                     *)
(*                                                                        *)
(*  fcofix1 = [clos_t   | code1   | a1 |...| anbr | fv1 |...| fvn | type] *)
(*                      ^                                                 *)
(*                ...                                                     *)
(*  fcofixnbr = [clos_t | codenbr | a1 |...| anbr | fv1 |...| fvn | type] *)
(*                      ^                                                 *)
(* The [ai] blocks are functions that accumulate their arguments:         *)
(*           ai arg1  argp --->                                           *)
(*    ai' = [A_t | accumulate | [Cfx_t | fcofixi] | arg1 | ... | argp ]   *)
(* If such a block is matched against, we have to force evaluation,       *)
(* function [fcofixi] is then applied to [ai'] [arg1] ... [argp]          *)
(* Once evaluation is completed [ai'] is updated with the result:         *)
(*  ai' <--                                                               *)
(*   [A_t | accumulate | [Cfxe_t |fcofixi|result] | arg1 | ... | argp ]   *)
(* This representation is nice because the application of the cofix is    *)
(* evaluated only once (it simulates a lazy evaluation)                   *)
(* Moreover, when cofix don't have arguments, it is possible to create    *)
(* a cycle, e.g.:                                                         *)
(*   cofix one := cons 1 one                                              *)
(*   a1 = [A_t | accumulate | [Cfx_t|fcofix1] ]                           *)
(*   fcofix1 = [clos_t | code | a1]                                       *)
(* The result of evaluating [a1] is [cons_t | 1 | a1].                    *)
(* When [a1] is updated :                                                 *)
(*  a1 = [A_t | accumulate | [Cfxe_t | fcofix1 | [cons_t | 1 | a1]] ]     *)
(* The cycle is created ...                                               *)
(*                                                                        *)
(* In Cfxe_t accumulators, we need to store [fcofixi] for testing         *)
(* conversion of cofixpoints (which is intentional).                      *)
   
type vm_env = {
    size : int;              (* longueur de la liste [n] *)
    fv_rev : fv_elem list    (* [fvn; ... ;fv1] *)
  }    
   
   
type comp_env = { 
    nb_stack : int;              (* nbre de variables sur la pile          *)
    in_stack : int list;         (* position dans la pile                  *)
    nb_rec : int;                (* nbre de fonctions mutuellement         *)
                                 (* recursives =  nbr                      *)
    pos_rec  : instruction list; (* instruction d'acces pour les variables *)
                                 (*  de point fix ou de cofix              *)
    offset : int;                 
    in_env : vm_env ref 
  } 
    
let empty_fv = { size= 0;  fv_rev = [] }
  
let fv r = !(r.in_env)
   
let empty_comp_env ()= 
  { nb_stack = 0; 
    in_stack = [];
    nb_rec = 0;
    pos_rec = [];
    offset = 0; 
    in_env = ref empty_fv;
  } 

(*i Creation functions for comp_env *)

let rec add_param n sz l =
  if n = 0 then l else add_param (n - 1) sz (n+sz::l) 
   
let comp_env_fun arity = 
  { nb_stack = arity; 
    in_stack = add_param arity 0 [];
    nb_rec = 0;
    pos_rec = [];
    offset = 1; 
    in_env = ref empty_fv 
  } 
    

let comp_env_fix_type rfv =
  { nb_stack = 0;
    in_stack = [];
    nb_rec = 0;
    pos_rec = [];
    offset = 1; 
    in_env = rfv 
  }
   
let comp_env_fix ndef curr_pos arity rfv =
   let prec = ref [] in
   for i = ndef downto 1 do
     prec := Koffsetclosure (2 * (ndef - curr_pos - i)) :: !prec 
   done;
   { nb_stack = arity; 
     in_stack = add_param arity 0 [];
     nb_rec = ndef; 
     pos_rec = !prec;
     offset = 2 * (ndef - curr_pos - 1)+1;
     in_env = rfv 
   } 

let comp_env_cofix_type ndef rfv =
  { nb_stack = 0;
    in_stack = [];
    nb_rec = 0;
    pos_rec = [];
    offset = 1+ndef;
    in_env = rfv
  }

let comp_env_cofix ndef arity rfv =
   let prec = ref [] in
   for i = 1 to ndef do
     prec := Kenvacc i :: !prec
   done;
   { nb_stack = arity; 
     in_stack = add_param arity 0 [];
     nb_rec = ndef; 
     pos_rec = !prec;
     offset = ndef+1;
     in_env = rfv 
   }

(* [push_param ] add function parameters on the stack *)
let push_param n sz r =
  { r with
    nb_stack = r.nb_stack + n;
    in_stack = add_param n sz r.in_stack }

(* [push_local sz r] add a new variable on the stack at position [sz] *)
let push_local sz r =
  { r with
    nb_stack = r.nb_stack + 1;
    in_stack = (sz + 1) :: r.in_stack }



(*i Compilation of variables *)
let find_at el l = 
  let rec aux n = function
    | [] -> raise Not_found
    | hd :: tl -> if hd = el then n else aux (n+1) tl
  in aux 1 l

let pos_named id r =
  let env = !(r.in_env) in
  let cid = FVnamed id in
  try Kenvacc(r.offset + env.size - (find_at cid env.fv_rev))
  with Not_found ->
    let pos = env.size in
    r.in_env := { size = pos+1; fv_rev =  cid:: env.fv_rev};
    Kenvacc (r.offset + pos)

let pos_rel i r sz = 
  if i <= r.nb_stack then
    Kacc(sz - (List.nth r.in_stack (i-1)))
  else
    let i = i - r.nb_stack in
    if i <= r.nb_rec then 
      try List.nth r.pos_rec (i-1)
      with (Failure _|Invalid_argument _) -> assert false
    else
      let i = i - r.nb_rec in
      let db = FVrel(i) in
      let env = !(r.in_env) in
      try Kenvacc(r.offset + env.size - (find_at db env.fv_rev))
      with Not_found ->
	let pos = env.size in
	r.in_env := { size = pos+1; fv_rev =  db:: env.fv_rev};
	Kenvacc(r.offset + pos)

(*i  Examination of the continuation *)

(* Discard all instructions up to the next label.                        *)
(* This function is to be applied to the continuation before adding a    *)
(* non-terminating instruction (branch, raise, return, appterm)          *)
(* in front of it.                                                       *)

let rec discard_dead_code cont = cont
(*function
    [] -> []
  | (Klabel _ | Krestart ) :: _ as cont -> cont
  | _ :: cont -> discard_dead_code cont
*)

(* Return a label to the beginning of the given continuation.            *)
(*   If the sequence starts with a branch, use the target of that branch *)
(*   as the label, thus avoiding a jump to a jump.                       *)

let label_code = function
  | Klabel lbl :: _ as cont -> (lbl, cont)
  | Kbranch lbl :: _ as cont -> (lbl, cont)
  | cont -> let lbl = Label.create() in (lbl, Klabel lbl :: cont)

(* Return a branch to the continuation. That is, an instruction that,
   when executed, branches to the continuation or performs what the
   continuation performs. We avoid generating branches to returns. *)
(* spiwack: make_branch was only used once. Changed it back to the ZAM
      one to match the appropriate semantics (old one avoided the 
      introduction of an unconditional branch operation, which seemed
      appropriate for the 31-bit integers' code). As a memory, I leave
      the former version in this comment.
let make_branch cont =
  match cont with
  | (Kreturn _ as return) :: cont' -> return, cont'
  | Klabel lbl as b :: _ -> b, cont
  | _ -> let b = Klabel(Label.create()) in b,b::cont
*)

let rec make_branch_2 lbl n cont =
  function
    | Kreturn m :: _ -> (Kreturn (n + m), cont)
    | Klabel _ :: c  -> make_branch_2 lbl n cont c
    | Kpop m :: c    -> make_branch_2 lbl (n + m) cont c
    | _              ->
	match lbl with
        | Some lbl -> (Kbranch lbl, cont)
	| None     -> 
	    let lbl = Label.create() in
	    (Kbranch lbl, Klabel lbl :: cont)

let make_branch cont =
  match cont with
  | (Kbranch _ as branch) :: _ -> (branch, cont)
  | (Kreturn _ as return) :: _ -> (return, cont)
  |  Klabel lbl :: _ -> make_branch_2 (Some lbl) 0 cont cont
  | _ ->  make_branch_2 (None) 0 cont cont

(* Check if we're in tailcall position *)

let rec is_tailcall = function
  | Kreturn k :: _ -> Some k
  | Klabel _ :: c -> is_tailcall c
  | _ -> None

(* Extention of the continuation *)
	
(* Add a Kpop n instruction in front of a continuation *)
let rec add_pop n = function
  | Kpop m :: cont -> add_pop (n+m) cont
  | Kreturn m:: cont -> Kreturn (n+m) ::cont
  | cont -> if n = 0 then cont else Kpop n :: cont

let add_grab arity lbl cont =
  if arity = 1 then Klabel lbl :: cont
  else Krestart :: Klabel lbl :: Kgrab (arity - 1) :: cont
 
let add_grabrec rec_arg arity lbl cont =
  if rec_arg < 0 then (* No check *)
    add_grab arity lbl cont
  else
    if arity = 1 then 
      Klabel lbl :: Kgrabrec 0 :: Krestart :: cont
    else
      Krestart :: Klabel lbl :: Kgrabrec rec_arg ::
      Krestart :: Kgrab (arity - 1) :: cont
				      
(* continuation of a cofix *)

let cont_cofix arity =
    (* accu = res                                                         *)
    (* stk  = ai::args::ra::...                                           *)
    (* ai   = [At|accumulate|[Cfx_t|fcofix]|args]                         *)
  [ Kpush;
    Kpush;        (*                 stk = res::res::ai::args::ra::...    *)
    Kacc 2;
    Kfield 1;
    Kfield 0;
    Kmakeblock(2, cofix_evaluated_tag); 
    Kpush;        (*  stk = [Cfxe_t|fcofix|res]::res::ai::args::ra::...*)
    Kacc 2;
    Ksetfield 1;  (*   ai = [At|accumulate|[Cfxe_t|fcofix|res]|args]      *)
                  (*  stk = res::ai::args::ra::...                        *)   
    Kacc 0;       (* accu = res                                           *)
    Kreturn (arity+2) ]


(* Code of closures *)
let fun_code = ref []

let init_fun_code () = fun_code := []

(* Compiling free variables *)

let compile_fv_elem reloc fv sz cont =
  match fv with
  | FVrel i -> pos_rel i reloc sz :: cont
  | FVnamed id -> pos_named id reloc :: cont

let rec compile_fv reloc l sz cont =
  match l with
  | [] -> cont
  | [fvn] -> compile_fv_elem reloc fvn sz cont
  | fvn :: tl ->
      compile_fv_elem reloc fvn sz 
	(Kpush :: compile_fv reloc tl (sz + 1) cont)

(* Compilation of lambda expression *)
		  
let rec compile_lam reloc lam sz cont =
  match lam with
  | Lrel(_, i) -> pos_rel i reloc sz :: cont
  | Lvar id -> pos_named id reloc :: cont

  | Lprod (dom,codom) ->
      let cont1 = 
	Kpush :: compile_lam reloc dom (sz+1) (Kmakeprod :: cont) in
      compile_lam reloc codom sz cont1

  | Llam (ids,body) ->
      let arity = Array.length ids in
      let r_fun = comp_env_fun arity in
      let lbl_fun = Label.create () in
      let cont_fun =
	compile_lam r_fun body arity [Kreturn arity] in
      fun_code := [Ksequence(add_grab arity lbl_fun cont_fun,!fun_code)];
      let fv = fv r_fun in
      compile_fv reloc fv.fv_rev sz (Kclosure(lbl_fun,fv.size) :: cont)

  | Lrec(id,body) ->
      let params,body = decompose_Llam body in
      let arity = Array.length params in
      assert (arity >= 1);
      let rfv = ref empty_fv in
      let env_body = comp_env_fix 1 0 arity rfv in
      let cont1 = 
	compile_lam env_body body arity [Kreturn arity] in
      let lbl_fun = Label.create () in
      let fcode =  add_grab arity lbl_fun cont1 in
      fun_code := [Ksequence(fcode,!fun_code)];
      let fv = !rfv in
      compile_fv reloc fv.fv_rev sz (Kclosure(lbl_fun, fv.size) :: cont)   

  | Llet (id,def,body) ->
      compile_lam reloc def sz 
	(Kpush :: 
	 compile_lam (push_local sz reloc) body (sz+1) (add_pop 1 cont))

  | Lapp (f, args) ->
      let nargs = Array.length args in
      if nargs = 0 then compile_lam reloc f sz cont
      else begin match is_tailcall cont with
      | Some k -> 
	  compile_args reloc args 0 nargs sz
	    (Kpush ::
	     compile_lam reloc f (sz + nargs)
	       (Kappterm(nargs, k + nargs) :: (discard_dead_code cont)))
      | None ->
	  if nargs <= 4 then
	    compile_args reloc args 0 nargs sz 
	      (Kpush :: compile_lam reloc f (sz+nargs) (Kapply nargs :: cont))
	  else 
	    let lbl,cont1 = label_code cont in
	    Kpush_retaddr lbl ::
	    compile_args reloc args 0 nargs (sz + 3)
	      (Kpush :: compile_lam reloc f (sz+3+nargs) 
			 (Kapply nargs :: cont1))
      end

  | Lconst kn -> Kgetglobal kn :: cont 

  | Lprim (kn, op, args) -> 
      let nargs = Array.length args in
      begin match op with
      | Int31lsl when nargs = 2 && args.(1) = Lint 1 ->
	  compile_args reloc args 0 1 sz (Kprim_const(op,kn,1)::cont)
      | Int31lsr when nargs = 2 && args.(1) = Lint 1 ->
	  compile_args reloc args 0 1 sz (Kprim_const(op,kn,1)::cont)
      | _ ->
          compile_args reloc args 0 nargs sz (Kprim(op, kn)::cont)
      end
  | Lcprim(kn, op, args) ->
      let nparams, nargs = Native.caml_prim_arity op in
      let all = nparams + nargs in
      assert (all = Array.length args && all <= 4);
      let (jump, cont) = make_branch cont in
      let lbl_default = Label.create () in
      let default =
	let cont = Kgetglobal kn :: Kapply all :: jump :: !fun_code in
	Klabel lbl_default ::
	Kpush ::
	if nparams = 0 then cont
	else 
	  compile_args reloc 
	    args 0 nparams (sz + nargs) (Kpush::cont) in
      fun_code := default;
      compile_args reloc args nparams nargs sz 
	(Kcamlprim (op, lbl_default) :: cont)

  | Lareint args ->
      let nargs = Array.length args in
      compile_args reloc args 0 nargs sz
	(Kareint nargs :: cont)
      
  | Lif(t, bt, bf) ->
      let branch, cont = make_branch cont in
      let lbl_true =  Label.create() in
      let lbl_false = Label.create() in
      compile_lam reloc t sz 
	(Kswitch([|lbl_true;lbl_false|],[||]) ::
	 Klabel lbl_false ::
	 compile_lam reloc bf sz 
	   (branch ::
	    Klabel lbl_true ::
	    compile_lam reloc bt sz cont))
  
  | Lcase(annot,t,a,(bconst,bblock)) ->
      (* Compilation of the predicate *)
      let lbl_type, code =
	label_code 
	  (compile_lam reloc t sz [Kpop sz; Kstop]) in
      fun_code := [Ksequence(code,!fun_code)];
      (* Compilation of the branches *)
      let branch1, cont = make_branch cont in
      let sz_b,branch,is_tailcall =
	match branch1 with 
	| Kreturn k -> assert (k = sz); sz, branch1, true
	| _ -> sz+3, Kjump, false in
      let annot_sw = 
	{ci = annot.asw_ci;rtbl = annot.asw_reloc;tailcall = is_tailcall } in
         let nconst = Array.length bconst in
      let nblock = Array.length bblock  in
      let lbl_sw = Label.create () in
      let lbl_consts = Array.create nconst Label.no in
      let lbl_blocks = Array.create (nblock + 1) Label.no in
      let seq = ref cont in  
      (* Compilation of constant branches *)
      for i = nconst - 1 downto 0 do
	let aux = 
	  compile_lam reloc bconst.(i) sz_b (branch::!seq) in
	let lbl_b,code_b = label_code aux in
	lbl_consts.(i) <- lbl_b; 
	seq := code_b
      done;
      (* Compilation of the accumulate branch *)
      let aux = 
	Kmakeswitchblock (lbl_type,lbl_sw,annot_sw,sz) :: branch :: !seq in
      let lbl_accu, code_accu = label_code aux in
      lbl_blocks.(0) <- lbl_accu;
      seq := code_accu;
      (* Compilation of block branches *)
      for i = nblock - 1 downto 0 do
	let (ids, body) = bblock.(i) in
	let arity = Array.length ids in
	let aux = 
	  compile_lam (push_param arity sz_b reloc) 
	    body (sz_b+arity) (add_pop arity (branch::!seq)) in
	let lbl_b, code_b = label_code (Kpushfields arity :: aux) in
	lbl_blocks.(i+1) <- lbl_b;
	seq := code_b
      done;
      (* Continuation of the argument *)
      let c =
	Klabel lbl_sw :: Kswitch(lbl_consts,lbl_blocks) :: !seq in
      let code_sw = 
 	match branch1 with 
        | Kbranch lbl -> Kpush_retaddr lbl ::  c
	| _ -> c in
      (* Compilation of the argument *)
      compile_lam reloc a sz code_sw
      
  | Lfix ((rec_args, init), (decl, ltypes, lbodies)) ->
      let ndef = Array.length ltypes in
      let rfv = ref empty_fv in
      let lbl_types = Array.create ndef Label.no in
      let lbl_bodies = Array.create ndef Label.no in
      (* Compilation des types *)
      let env_type = comp_env_fix_type rfv in
      for i = 0 to ndef - 1 do
	let lbl,fcode = 
	  label_code 
	    (compile_lam env_type ltypes.(i) 0 [Kstop]) in 
	lbl_types.(i) <- lbl; 
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compiling bodies *)
      for i = 0 to ndef - 1 do
	let params,body = decompose_Llam lbodies.(i) in
	let arity = Array.length params in
	let env_body = comp_env_fix ndef i arity rfv in
	let cont1 = 
	  compile_lam env_body body arity [Kreturn arity] in
	let lbl = Label.create () in
	lbl_bodies.(i) <- lbl;
	let fcode =  add_grabrec rec_args.(i) arity lbl cont1 in
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      let fv = !rfv in
      compile_fv reloc fv.fv_rev sz 
	(Kclosurerec(fv.size,init,lbl_types,lbl_bodies) :: cont)

  | Lcofix(init, (decl,ltypes,lbodies)) ->
      let ndef = Array.length ltypes in
      let lbl_types = Array.create ndef Label.no in
      let lbl_bodies = Array.create ndef Label.no in
      (* Compiling types *)
      let rfv = ref empty_fv in
      let env_type = comp_env_cofix_type ndef rfv in
      for i = 0 to ndef - 1 do
	let lbl,fcode = 
	  label_code 
	    (compile_lam env_type lbodies.(i) 0 [Kstop]) in
	lbl_types.(i) <- lbl; 
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compiling bodies *)
      for i = 0 to ndef - 1 do
	let params,body = decompose_Llam lbodies.(i) in
	let arity = Array.length params in
	let env_body = comp_env_cofix ndef arity rfv in
	let lbl = Label.create () in
	let cont1 = 
	  compile_lam env_body body (arity+1) (cont_cofix arity) in
	let cont2 = 
	  add_grab (arity+1) lbl cont1 in
	lbl_bodies.(i) <- lbl;
	fun_code := [Ksequence(cont2,!fun_code)];
      done;
      let fv = !rfv in
      compile_fv reloc fv.fv_rev sz 
	(Kclosurecofix(fv.size, init, lbl_types, lbl_bodies) :: cont)
  
  | Lmakeblock (tag,args) ->
      compile_args reloc args 0 (Array.length args) sz
	(Kmakeblock(Array.length args, tag)::cont)
  | Lint i   -> Kconst (Const_b0 i) :: cont
  | Lsort s  -> Kconst (Const_sorts s) :: cont
  | Lind ind -> Kconst (Const_ind ind) :: cont
  | Lval v   -> Kconst (Const_val v) :: cont
 
and compile_args reloc args istart nargs sz cont =
  let nargs_m_1 = nargs - 1 in  
  let c = ref (compile_lam reloc args.(istart) (sz + nargs_m_1) cont) in
  for i = 1 to nargs_m_1 do
    c := compile_lam reloc args.(istart + i) (sz + nargs_m_1 - i) (Kpush :: !c)
  done; 
  !c



let compile_opt opt env c =
(*  if draw then begin
    msgerrnl (str "Start compilation");
    print_constr c;
    flush_all()
  end; *)
  set_global_env env;
  init_fun_code ();
  Label.reset_label_counter ();
  let lam =lambda_of_constr opt c in
(*    try lambda_of_constr opt c 
    with e -> 
      Printf.printf "lambda_of_constr fail\n";
      (Pp.msgerrnl (Clambda.pr_constr c));
      Pp.flush_all ();
      flush stdout;raise e
  in *)
  let reloc = empty_comp_env () in
  let init_code = compile_lam reloc lam 0 [Kstop] in
  let fv = List.rev (!(reloc.in_env).fv_rev) in
  if Flags.vm_draw_instr () then begin 
    msgerrnl (str "main =");
    draw_instr init_code;
    msgerrnl (str "fun_code =");
    draw_instr !fun_code;
    msgerr (str "fv = ");
    List.iter (fun v ->
      match v with
      | FVnamed id -> msgerr (str ((string_of_id id)^"; "))
      | FVrel i -> msgerr (str ((string_of_int i)^"; "))) fv; 
    msgerrnl (str "");
    flush_all()
  end;
  init_code,!fun_code, Array.of_list fv

let compile env c = compile_opt (Flags.vm_optimize ()) env c

let compile_constant_body env body boxed =
  match body with
  | Opaque _ -> BCconstant
  | Primitive _op -> BCconstant
  | Def sb ->
      let body = Declarations.force sb in
      if boxed then
	let res = compile env body in
	let to_patch = to_memory res in
	BCdefined(true, to_patch)
      else
	match kind_of_term body with
	| Const kn' -> BCallias (get_allias env kn')
	| _ -> 
	    let res = compile env body in
	    let to_patch = to_memory res in
	    BCdefined (false, to_patch)

