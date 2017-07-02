(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Author: Benjamin Grégoire as part of the bytecode-based virtual reduction
   machine, Oct 2004 *)
(* Extension: Arnaud Spiwack (support for native arithmetic), May 2005 *)

open Util
open Names
open Cbytecodes
open Cemitcodes
open Term
open Declarations
open Pre_env


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

(* Representation of environments of mutual fixpoints :                  *)
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

(* This allows representing mutual fixpoints in just one block.           *)
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

module Config = struct
  let stack_threshold = 256 (* see byterun/coq_memory.h *)
  let stack_safety_margin = 15
end

type argument = ArgConstr of Constr.t | ArgUniv of Univ.Level.t

let empty_fv = { size= 0;  fv_rev = []; fv_fwd = FvMap.empty }
let push_fv d e = {
  size = e.size + 1;
  fv_rev = d :: e.fv_rev;
  fv_fwd = FvMap.add d e.size e.fv_fwd;
}

let fv r = !(r.in_env)

let empty_comp_env ?(univs=0) ()=
  { nb_uni_stack = univs;
    nb_stack = 0;
    in_stack = [];
    nb_rec = 0;
    pos_rec = [];
    offset = 0;
    in_env = ref empty_fv
  }

(* Maximal stack size reached during the current function body. Used to
   reallocate the stack if we lack space. *)
let max_stack_size = ref 0

let set_max_stack_size stack_size =
  if stack_size > !max_stack_size then
    max_stack_size := stack_size

let ensure_stack_capacity f x =
  let old = !max_stack_size in
  max_stack_size := 0;
  let code = f x in
  let used_safe =
    !max_stack_size + Config.stack_safety_margin
  in
  max_stack_size := old;
  if used_safe > Config.stack_threshold then
    Kensurestackcapacity used_safe :: code
  else code

(*i Creation functions for comp_env *)

let rec add_param n sz l =
  if Int.equal n 0 then l else add_param (n - 1) sz (n+sz::l)

let comp_env_fun ?(univs=0) arity =
  { nb_uni_stack = univs ;
    nb_stack = arity;
    in_stack = add_param arity 0 [];
    nb_rec = 0;
    pos_rec = [];
    offset = 1;
    in_env = ref empty_fv
  }


let comp_env_fix_type  rfv =
  { nb_uni_stack = 0;
    nb_stack = 0;
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
   { nb_uni_stack = 0;
     nb_stack = arity;
     in_stack = add_param arity 0 [];
     nb_rec = ndef;
     pos_rec = !prec;
     offset = 2 * (ndef - curr_pos - 1)+1;
     in_env = rfv
   }

let comp_env_cofix_type ndef rfv =
  { nb_uni_stack = 0;
    nb_stack = 0;
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
   { nb_uni_stack = 0;
     nb_stack = arity;
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
let find_at fv env = FvMap.find fv env.fv_fwd

let pos_named id r =
  let env = !(r.in_env) in
  let cid = FVnamed id in
  try Kenvacc(r.offset + find_at cid env)
  with Not_found ->
    let pos = env.size in
    r.in_env := push_fv cid env;
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
      try Kenvacc(r.offset + find_at db env)
      with Not_found ->
	let pos = env.size in
	r.in_env := push_fv db env;
	Kenvacc(r.offset + pos)

let pos_universe_var i r sz =
  if i < r.nb_uni_stack then
    Kacc (sz - r.nb_stack - (r.nb_uni_stack - i))
  else
    let env = !(r.in_env) in
    let db = FVuniv_var i in
    try Kenvacc (r.offset + find_at db env)
    with Not_found ->
      let pos = env.size in
      r.in_env := push_fv db env;
      Kenvacc(r.offset + pos)

(*i  Examination of the continuation *)

(* Discard all instructions up to the next label.                        *)
(* This function is to be applied to the continuation before adding a    *)
(* non-terminating instruction (branch, raise, return, appterm)          *)
(* in front of it.                                                       *)

let discard_dead_code cont = cont
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
    Kreturn m :: _ -> (Kreturn (n + m), cont)
  | Klabel _ :: c  -> make_branch_2 lbl n cont c
  | Kpop m :: c    -> make_branch_2 lbl (n + m) cont c
  | _              ->
      match lbl with
        Some lbl -> (Kbranch lbl, cont)
      | None     -> let lbl = Label.create() in (Kbranch lbl, Klabel lbl :: cont)

let make_branch cont =
  match cont with
    (Kbranch _ as branch) :: _ -> (branch, cont)
  | (Kreturn _ as return) :: _ -> (return, cont)
  | Klabel lbl :: _ -> make_branch_2 (Some lbl) 0 cont cont
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
  | cont -> if Int.equal n 0 then cont else Kpop n :: cont

let add_grab arity lbl cont =
  if Int.equal arity 1 then Klabel lbl :: cont
  else Krestart :: Klabel lbl :: Kgrab (arity - 1) :: cont

let add_grabrec rec_arg arity lbl cont =
  if Int.equal arity 1 && rec_arg < arity then
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


(*i Global environment *)

let global_env = ref empty_env

let set_global_env env = global_env := env


(* Code of closures *)
let fun_code = ref []

let init_fun_code () = fun_code := []

(* Compilation of constructors and inductive types *)


(* Limitation due to OCaml's representation of non-constant
  constructors: limited to 245 + 1 (0 tag) cases. *)

exception TooLargeInductive of Id.t

let max_nb_const = 0x1000000 
let max_nb_block = 0x1000000 + last_variant_tag - 1

let str_max_constructors = 
  Format.sprintf 
    " which has more than %i constant constructors or more than %i non-constant constructors" max_nb_const max_nb_block

let check_compilable ib = 
  
  if not (ib.mind_nb_args <= max_nb_block && ib.mind_nb_constant <= max_nb_const) then 
    raise (TooLargeInductive ib.mind_typename)

(* Inv: arity > 0 *)

let const_bn tag args = 
  if tag < last_variant_tag then Const_bn(tag, args)
  else
    Const_bn(last_variant_tag, Array.append [|Const_b0 (tag - last_variant_tag) |] args)

(*
If [tag] hits the OCaml limitation for non constant constructors, we switch to
another representation for the remaining constructors:
[last_variant_tag|tag - last_variant_tag|args]

We subtract last_variant_tag for efficiency of match interpretation.
 *)

let nest_block tag arity cont =
  Kconst (Const_b0 (tag - last_variant_tag)) ::
    Kmakeblock(arity+1, last_variant_tag) :: cont

let code_makeblock ~stack_size ~arity ~tag cont = 
  if tag < last_variant_tag then
    Kmakeblock(arity, tag) :: cont
  else begin
    set_max_stack_size (stack_size + 1);
    Kpush :: nest_block tag arity cont
  end

(* [code_construct] compiles an abstracted constructor dropping parameters and
   updates [fun_code] *)
(* Inv : nparam + arity > 0 *)
let code_construct tag nparams arity cont =
  let f_cont =
      add_pop nparams
      (if Int.equal arity 0 then
	[Kconst (Const_b0 tag); Kreturn 0]
       else if tag < last_variant_tag then
         [Kacc 0; Kpop 1; Kmakeblock(arity, tag); Kreturn 0]
       else
         nest_block tag arity [Kreturn 0])
    in
    let lbl = Label.create() in
    (* No need to grow the stack here, as the function does not push stuff. *)
    fun_code := [Ksequence (add_grab (nparams+arity) lbl f_cont,!fun_code)];
    Kclosure(lbl,0) :: cont

let get_strcst = function
  | Bstrconst sc -> sc
  | _ -> raise Not_found

let rec str_const c =
  match kind_of_term c with
  | Sort s -> Bstrconst (Const_sorts s)
  | Cast(c,_,_) -> str_const c
  | App(f,args) ->
      begin
	match kind_of_term f with
	| Construct(((kn,j),i),u) -> 
            begin
	    let oib = lookup_mind kn !global_env in
	    let oip = oib.mind_packets.(j) in
	    let () = check_compilable oip in
	    let tag,arity = oip.mind_reloc_tbl.(i-1) in
	    let nparams = oib.mind_nparams in
	    if Int.equal (nparams + arity) (Array.length args) then
              (* spiwack: *)
              (* 1/ tries to compile the constructor in an optimal way,
                    it is supposed to work only if the arguments are
                    all fully constructed, fails with Cbytecodes.NotClosed.
                    it can also raise Not_found when there is no special
                    treatment for this constructor
                    for instance: tries to to compile an integer of the
                        form I31 D1 D2 ... D31 to [D1D2...D31] as
                        a processor number (a caml number actually) *)
              try
		try
		  Bstrconst (Retroknowledge.get_vm_constant_static_info
                                              (!global_env).retroknowledge
                                              f args)
                with NotClosed ->
		  (* 2/ if the arguments are not all closed (this is
                        expectingly (and it is currently the case) the only
                        reason why this exception is raised) tries to
                        give a clever, run-time behavior to the constructor.
                        Raises Not_found if there is no special treatment
                        for this integer.
                        this is done in a lazy fashion, using the constructor
                        Bspecial because it needs to know the continuation
                        and such, which can't be done at this time.
                        for instance, for int31: if one of the digit is
                            not closed, it's not impossible that the number
                            gets fully instanciated at run-time, thus to ensure
                            uniqueness of the representation in the vm
                            it is necessary to try and build a caml integer
                            during the execution *)
		  let rargs = Array.sub args nparams arity in
		  let b_args = Array.map str_const rargs in
		  Bspecial ((Retroknowledge.get_vm_constant_dynamic_info
                                           (!global_env).retroknowledge
                                           f),
                           b_args)
              with Not_found ->
		(* 3/ if no special behavior is available, then the compiler
		      falls back to the normal behavior *)
		if Int.equal arity 0 then Bstrconst(Const_b0 tag)
		else
		  let rargs = Array.sub args nparams arity in
		  let b_args = Array.map str_const rargs in
		  try
		    let sc_args = Array.map get_strcst b_args in
		    Bstrconst(const_bn tag sc_args)
		  with Not_found ->
		    Bmakeblock(tag,b_args)
	    else
              let b_args = Array.map str_const args in
	     (* spiwack: tries first to apply the run-time compilation
                behavior of the constructor, as in 2/ above *)
	      try
		Bspecial ((Retroknowledge.get_vm_constant_dynamic_info
                                           (!global_env).retroknowledge
                                           f),
                         b_args)
	      with Not_found ->
	        Bconstruct_app(tag, nparams, arity, b_args)
              end
	| _ -> Bconstr c
      end
  | Ind (ind,u) when Univ.Instance.is_empty u ->
    Bstrconst (Const_ind ind)
  | Construct (((kn,j),i),_) ->
      begin
      (* spiwack: tries first to apply the run-time compilation
           behavior of the constructor, as in 2/ above *)
      try
	Bspecial ((Retroknowledge.get_vm_constant_dynamic_info
                                           (!global_env).retroknowledge
                                           c),
                         [| |])
      with Not_found ->
	let oib = lookup_mind kn !global_env in
	let oip = oib.mind_packets.(j) in
	let () = check_compilable oip in
	let num,arity = oip.mind_reloc_tbl.(i-1) in
	let nparams = oib.mind_nparams in
	if Int.equal (nparams + arity) 0 then Bstrconst(Const_b0 num)
	else Bconstruct_app(num,nparams,arity,[||])
      end
  | _ -> Bconstr c

(* compiling application *)
let comp_args comp_expr reloc args sz cont =
  let nargs_m_1 = Array.length args - 1 in
  let c = ref (comp_expr reloc args.(0) (sz + nargs_m_1) cont) in
  for i = 1 to nargs_m_1 do
    c := comp_expr reloc args.(i) (sz + nargs_m_1 - i) (Kpush :: !c)
  done;
  !c

(* Precondition: args not empty *)
let comp_app comp_fun comp_arg reloc f args sz cont =
  let nargs = Array.length args in
  match is_tailcall cont with
  | Some k ->
      comp_args comp_arg reloc args sz
	(Kpush ::
	 comp_fun reloc f (sz + nargs)
	   (Kappterm(nargs, k + nargs) :: (discard_dead_code cont)))
  | None ->
      if nargs < 4 then
	comp_args comp_arg reloc args sz
	  (Kpush :: (comp_fun reloc f (sz+nargs) (Kapply nargs :: cont)))
      else
	let lbl,cont1 = label_code cont in
	Kpush_retaddr lbl ::
	(comp_args comp_arg reloc args (sz + 3)
	   (Kpush :: (comp_fun reloc f (sz+3+nargs) (Kapply nargs :: cont1))))

(* Compiling free variables *)

let compile_fv_elem reloc fv sz cont =
  match fv with
  | FVrel i -> pos_rel i reloc sz :: cont
  | FVnamed id -> pos_named id reloc :: cont
  | FVuniv_var i -> pos_universe_var i reloc sz :: cont

let rec compile_fv reloc l sz cont =
  match l with
  | [] -> cont
  | [fvn] -> set_max_stack_size (sz + 1); compile_fv_elem reloc fvn sz cont
  | fvn :: tl ->
      compile_fv_elem reloc fvn sz
	(Kpush :: compile_fv reloc tl (sz + 1) cont)


(* Compiling constants *)

let rec get_alias env kn =
  let cb = lookup_constant kn env in
  let tps = cb.const_body_code in
    match tps with
    | None -> kn
    | Some tps ->
       (match Cemitcodes.force tps with
	| BCalias kn' -> get_alias env kn'
	| _ -> kn)

(* sz is the size of the local stack *)
let rec compile_constr reloc c sz cont =
  set_max_stack_size sz;
  match kind_of_term c with
  | Meta _ -> invalid_arg "Cbytegen.compile_constr : Meta"
  | Evar _ -> invalid_arg "Cbytegen.compile_constr : Evar"
  | Proj (p,c) ->
     let kn = Projection.constant p in
     let cb = lookup_constant kn !global_env in
     let pb = Option.get cb.const_proj in
     let n = pb.proj_arg in
     compile_constr reloc c sz (Kproj (n,kn) :: cont)

  | Cast(c,_,_) -> compile_constr reloc c sz cont

  | Rel i -> pos_rel i reloc sz :: cont
  | Var id -> pos_named id reloc :: cont
  | Const (kn,u) -> compile_const reloc kn u [||] sz cont
  | Ind (ind,u) ->
     let bcst = Bstrconst (Const_ind ind) in
    if Univ.Instance.is_empty u then
      compile_str_cst reloc bcst sz cont
    else
      comp_app compile_str_cst compile_universe reloc
	   bcst
	   (Univ.Instance.to_array u)
	   sz
	   cont
  | Sort (Prop _) | Construct _ ->
      compile_str_cst reloc (str_const c) sz cont
  | Sort (Type u) ->
     (* We separate global and local universes in [u]. The former will be part
        of the structured constant, while the later (if any) will be applied as
        arguments. *)
     let open Univ in begin
      let levels = Universe.levels u in
      let global_levels =
	LSet.filter (fun x -> Level.var_index x = None) levels
      in
      let local_levels =
	List.map_filter (fun x -> Level.var_index x)
	  (LSet.elements levels)
      in
      (* We assume that [Universe.type0m] is a neutral element for [Universe.sup] *)
      let uglob =
	LSet.fold (fun lvl u -> Universe.sup u (Universe.make lvl)) global_levels Universe.type0m
      in
      if local_levels = [] then
	compile_str_cst reloc (Bstrconst (Const_sorts (Type uglob))) sz cont
      else
	let compile_get_univ reloc idx sz cont =
          set_max_stack_size sz;
	  compile_fv_elem reloc (FVuniv_var idx) sz cont
	in
        comp_app compile_str_cst compile_get_univ reloc
	  (Bstrconst (Const_type u)) (Array.of_list local_levels) sz cont
    end
  | LetIn(_,xb,_,body) ->
      compile_constr reloc xb sz
	(Kpush ::
	(compile_constr (push_local sz reloc) body (sz+1) (add_pop 1 cont)))
  | Prod(id,dom,codom) ->
      let cont1 =
	Kpush :: compile_constr reloc dom (sz+1) (Kmakeprod :: cont) in
      compile_constr reloc (mkLambda(id,dom,codom)) sz cont1
  | Lambda _ ->
      let params, body = decompose_lam c in
      let arity = List.length params in
      let r_fun = comp_env_fun arity in
      let lbl_fun = Label.create() in
      let cont_fun =
        ensure_stack_capacity (compile_constr r_fun body arity) [Kreturn arity]
      in
      fun_code := [Ksequence(add_grab arity lbl_fun cont_fun,!fun_code)];
      let fv = fv r_fun in
      compile_fv reloc fv.fv_rev sz (Kclosure(lbl_fun,fv.size) :: cont)

  | App(f,args) ->
      begin
	match kind_of_term f with
	| Construct _ -> compile_str_cst reloc (str_const c) sz cont
        | Const (kn,u) -> compile_const reloc kn u args sz cont
	| _ -> comp_app compile_constr compile_constr reloc f args sz cont
      end
  | Fix ((rec_args,init),(_,type_bodies,rec_bodies)) ->
      let ndef = Array.length type_bodies in
      let rfv = ref empty_fv in
      let lbl_types = Array.make ndef Label.no in
      let lbl_bodies = Array.make ndef Label.no in
      (* Compilation des types *)
      let env_type = comp_env_fix_type rfv in
      for i = 0 to ndef - 1 do
        let fcode =
          ensure_stack_capacity (compile_constr env_type type_bodies.(i) 0) [Kstop]
        in
	let lbl,fcode = label_code fcode in
	lbl_types.(i) <- lbl;
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compiling bodies *)
      for i = 0 to ndef - 1 do
	let params,body = decompose_lam rec_bodies.(i) in
	let arity = List.length params in
	let env_body = comp_env_fix ndef i arity rfv in
	let cont1 =
	  ensure_stack_capacity (compile_constr env_body body arity) [Kreturn arity]
        in
	let lbl = Label.create () in
	lbl_bodies.(i) <- lbl;
	let fcode =  add_grabrec rec_args.(i) arity lbl cont1 in
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      let fv = !rfv in
      compile_fv reloc fv.fv_rev sz
	(Kclosurerec(fv.size,init,lbl_types,lbl_bodies) :: cont)

  | CoFix(init,(_,type_bodies,rec_bodies)) ->
      let ndef = Array.length type_bodies in
      let lbl_types = Array.make ndef Label.no in
      let lbl_bodies = Array.make ndef Label.no in
      (* Compiling types *)
      let rfv = ref empty_fv in
      let env_type = comp_env_cofix_type ndef rfv in
      for i = 0 to ndef - 1 do
        let fcode =
          ensure_stack_capacity (compile_constr env_type type_bodies.(i) 0) [Kstop]
        in
	let lbl,fcode = label_code fcode in
	lbl_types.(i) <- lbl;
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compiling bodies *)
      for i = 0 to ndef - 1 do
	let params,body = decompose_lam rec_bodies.(i) in
	let arity = List.length params in
	let env_body = comp_env_cofix ndef arity rfv in
	let lbl = Label.create () in
        let comp arity =
          (* 4 stack slots are needed to update the cofix when forced *)
          set_max_stack_size (arity + 4);
          compile_constr env_body body (arity+1) (cont_cofix arity)
        in
	let cont = ensure_stack_capacity comp arity in
	lbl_bodies.(i) <- lbl;
	fun_code := [Ksequence(add_grab (arity+1) lbl cont,!fun_code)];
      done;
      let fv = !rfv in
      set_max_stack_size (sz + fv.size + ndef + 2);
      compile_fv reloc fv.fv_rev sz
	(Kclosurecofix(fv.size, init, lbl_types, lbl_bodies) :: cont)

  | Case(ci,t,a,branchs) ->
      let ind = ci.ci_ind in
      let mib = lookup_mind (fst ind) !global_env in
      let oib = mib.mind_packets.(snd ind) in
      let () = check_compilable oib in
      let tbl = oib.mind_reloc_tbl in
      let lbl_consts = Array.make oib.mind_nb_constant Label.no in
      let nallblock = oib.mind_nb_args + 1 in (* +1 : accumulate *)
      let nblock = min nallblock (last_variant_tag + 1) in
      let lbl_blocks = Array.make nblock Label.no in
      let neblock = max 0 (nallblock - last_variant_tag) in
      let lbl_eblocks = Array.make neblock Label.no in 
      let branch1,cont = make_branch cont in
      (* Compiling return type *)
      let fcode =
        ensure_stack_capacity (compile_constr reloc t sz) [Kpop sz; Kstop]
      in
      let lbl_typ,fcode = label_code fcode in
      fun_code := [Ksequence(fcode,!fun_code)];
      (* Compiling branches *)
      let lbl_sw = Label.create () in
      let sz_b,branch,is_tailcall =
	match branch1 with
	| Kreturn k ->
	  assert (Int.equal k sz) ;
	  sz, branch1, true
	| _ -> sz+3, Kjump, false
      in

      let c = ref cont in
      (* Perform the extra match if needed (too many block constructors) *)
      if neblock <> 0 then begin
        let lbl_b, code_b = 
          label_code (
            Kpush :: Kfield 0 :: Kswitch(lbl_eblocks, [||]) :: !c) in
        lbl_blocks.(last_variant_tag) <- lbl_b;
        c := code_b
      end;  
      
      (* Compiling regular constructor branches *)
      for i = 0 to Array.length tbl - 1 do
	let tag, arity = tbl.(i) in
	if Int.equal arity 0 then
	  let lbl_b,code_b =
	    label_code(compile_constr reloc branchs.(i) sz_b (branch :: !c)) in
	  lbl_consts.(tag) <- lbl_b;
	  c := code_b
	else
	  let args, body = decompose_lam branchs.(i) in
	  let nargs = List.length args in
         
          let code_b =  
            if Int.equal nargs arity then
	      compile_constr (push_param arity sz_b reloc)
		body (sz_b+arity) (add_pop arity (branch :: !c))
	    else
	      let sz_appterm = if is_tailcall then sz_b + arity else arity in
	      compile_constr reloc branchs.(i) (sz_b+arity)
		(Kappterm(arity,sz_appterm) :: !c) in
          let code_b = 
            if tag < last_variant_tag then begin
                set_max_stack_size (sz_b + arity);
                Kpushfields arity :: code_b
              end
            else begin
                set_max_stack_size (sz_b + arity + 1);
                Kacc 0::Kpop 1::Kpushfields(arity+1)::Kpop 1::code_b
              end
          in
          let lbl_b,code_b = label_code code_b in
          if tag < last_variant_tag then lbl_blocks.(tag) <- lbl_b
          else lbl_eblocks.(tag - last_variant_tag) <- lbl_b;
	  c := code_b
      done;

      let annot =
        {ci = ci; rtbl = tbl; tailcall = is_tailcall;
         max_stack_size = !max_stack_size - sz}
      in

     (* Compiling branch for accumulators *)
      let lbl_accu, code_accu =
        set_max_stack_size (sz+3);
	label_code(Kmakeswitchblock(lbl_typ,lbl_sw,annot,sz) :: branch :: !c)
      in
      lbl_blocks.(0) <- lbl_accu;

      c := Klabel lbl_sw :: Kswitch(lbl_consts,lbl_blocks) :: code_accu;
      let code_sw =
 	match branch1 with
        (* spiwack : branch1 can't be a lbl anymore it's a Branch instead
	| Klabel lbl -> Kpush_retaddr lbl ::  !c *)
        | Kbranch lbl -> Kpush_retaddr lbl ::  !c
	| _ -> !c
      in
      compile_constr reloc a sz
      (try
	let entry = mkInd ind in
	Retroknowledge.get_vm_before_match_info (!global_env).retroknowledge
	                                       entry code_sw
      with Not_found ->
	code_sw)

and compile_str_cst reloc sc sz cont =
  set_max_stack_size sz;
  match sc with
  | Bconstr c -> compile_constr reloc c sz cont
  | Bstrconst sc -> Kconst sc :: cont
  | Bmakeblock(tag,args) ->
      let arity = Array.length args in
      let cont = code_makeblock ~stack_size:(sz+arity-1) ~arity ~tag cont in
      comp_args compile_str_cst reloc args sz cont
  | Bconstruct_app(tag,nparams,arity,args) ->
      if Int.equal (Array.length args) 0 then
        code_construct tag nparams arity cont
      else
	comp_app
	  (fun _ _ _ cont -> code_construct tag nparams arity cont)
	  compile_str_cst reloc () args sz cont
  | Bspecial (comp_fx, args) -> comp_fx reloc args sz cont


(* spiwack : compilation of constants with their arguments.
   Makes a special treatment with 31-bit integer addition *)
and compile_get_global reloc (kn,u) sz cont =
  set_max_stack_size sz;
  let kn = get_alias !global_env kn in
  if Univ.Instance.is_empty u then
    Kgetglobal kn :: cont
  else
    comp_app (fun _ _ _ cont -> Kgetglobal kn :: cont)
      compile_universe reloc () (Univ.Instance.to_array u) sz cont

and compile_universe reloc uni sz cont =
  set_max_stack_size sz;
  match Univ.Level.var_index uni with
  | None -> Kconst (Const_univ_level uni) :: cont
  | Some idx -> pos_universe_var idx reloc sz :: cont

and compile_const reloc kn u args sz cont =
  set_max_stack_size sz;
  let nargs = Array.length args in
  (* spiwack: checks if there is a specific way to compile the constant
              if there is not, Not_found is raised, and the function
              falls back on its normal behavior *)
  try
    Retroknowledge.get_vm_compiling_info (!global_env).retroknowledge
                  (mkConstU (kn,u)) reloc args sz cont
  with Not_found ->
    if Int.equal nargs 0 then
      compile_get_global reloc (kn,u) sz cont
    else
      if Univ.Instance.is_empty u then
        (* normal compilation *)
        comp_app (fun _ _ sz cont ->
            compile_get_global reloc (kn,u) sz cont)
          compile_constr reloc () args sz cont
      else
        let compile_arg reloc constr_or_uni sz cont =
          match constr_or_uni with
          | ArgConstr cst -> compile_constr reloc cst sz cont
          | ArgUniv uni -> compile_universe reloc uni sz cont
        in
	let u = Univ.Instance.to_array u in
	let lu = Array.length u in
	let all =
	  Array.init (lu + Array.length args) 
	    (fun i -> if i < lu then ArgUniv u.(i) else ArgConstr args.(i-lu))
	in
        comp_app (fun _ _ _ cont -> Kgetglobal kn :: cont)
          compile_arg reloc () all sz cont

let is_univ_copy max u =
  let u = Univ.Instance.to_array u in
  if Array.length u = max then
    Array.fold_left_i (fun i acc u ->
        if acc then
          match Univ.Level.var_index u with
          | None -> false
          | Some l -> l = i
        else false) true u
  else
    false

let dump_bytecodes init code fvs =
  let open Pp in
    (str "code =" ++ fnl () ++
     pp_bytecodes init ++ fnl () ++
     pp_bytecodes code ++ fnl () ++
     str "fv = " ++
     prlist_with_sep (fun () -> str "; ") pp_fv_elem fvs ++
     fnl ())

let compile fail_on_error ?universes:(universes=0) env c =
  set_global_env env;
  init_fun_code ();
  Label.reset_label_counter ();
  let cont = [Kstop] in
  try
    let reloc, init_code =
      if Int.equal universes 0 then
        let reloc = empty_comp_env () in
        reloc, ensure_stack_capacity (compile_constr reloc c 0) cont
      else
        (* We are going to generate a lambda, but merge the universe closure
         * with the function closure if it exists.
         *)
        let reloc = empty_comp_env () in
        let arity , body =
          match kind_of_term c with
          | Lambda _ ->
            let params, body = decompose_lam c in
            List.length params , body
          | _ -> 0 , c
        in
        let full_arity = arity + universes in
        let r_fun = comp_env_fun ~univs:universes arity in
        let lbl_fun = Label.create () in
        let cont_fun =
          ensure_stack_capacity (compile_constr r_fun body full_arity)
                         [Kreturn full_arity]
        in
        fun_code := [Ksequence(add_grab full_arity lbl_fun cont_fun,!fun_code)];
        let fv = fv r_fun in
        let init_code =
          ensure_stack_capacity (compile_fv reloc fv.fv_rev 0)
                         (Kclosure(lbl_fun,fv.size) :: cont)
        in
        reloc, init_code
    in
    let fv = List.rev (!(reloc.in_env).fv_rev) in
    (if !Flags.dump_bytecode then
      Feedback.msg_debug (dump_bytecodes init_code !fun_code fv)) ;
    Some (init_code,!fun_code, Array.of_list fv)
  with TooLargeInductive tname ->
    let fn = if fail_on_error then CErrors.user_err ?loc:None ~hdr:"compile" else
	       (fun x -> Feedback.msg_warning x) in
      (Pp.(fn
	   (str "Cannot compile code for virtual machine as it uses inductive " ++
	    Id.print tname ++ str str_max_constructors));
       None)

let compile_constant_body fail_on_error env univs = function
  | Undef _ | OpaqueDef _ -> Some BCconstant
  | Def sb ->
      let body = Mod_subst.force_constr sb in
      let instance_size =
        match univs with
        | Monomorphic_const _ -> 0
        | Polymorphic_const univ -> Univ.AUContext.size univ
      in
      match kind_of_term body with
	| Const (kn',u) when is_univ_copy instance_size u ->
	    (* we use the canonical name of the constant*)
	    let con= constant_of_kn (canonical_con kn') in
	      Some (BCalias (get_alias env con))
	| _ ->
	    let res = compile fail_on_error ~universes:instance_size env body in
	      Option.map (fun x -> BCdefined (to_memory x)) res

(* Shortcut of the previous function used during module strengthening *)

let compile_alias kn = BCalias (constant_of_kn (canonical_con kn))

(* spiwack: additional function which allow different part of compilation of the
      31-bit integers *)

let make_areconst n else_lbl cont =
  if n <= 0 then
    cont
  else
    Kareconst (n, else_lbl)::cont


(* try to compile int31 as a const_b0. Succeed if all the arguments are closed
   fails otherwise by raising NotClosed*)
let compile_structured_int31 fc args =
  if not fc then raise Not_found else
  Const_b0
    (Array.fold_left
       (fun temp_i -> fun t -> match kind_of_term t with
          | Construct ((_,d),_) -> 2*temp_i+d-1
          | _ -> raise NotClosed)
       0 args
    )

(* this function is used for the compilation of the constructor of
   the int31, it is used when it appears not fully applied, or
   applied to at least one non-closed digit *)
let dynamic_int31_compilation fc reloc args sz cont =
  if not fc then raise Not_found else
    let nargs = Array.length args in
      if Int.equal nargs 31 then
	let (escape,labeled_cont) = make_branch cont in
	let else_lbl = Label.create() in
	  comp_args compile_str_cst reloc args sz
            ( Kisconst else_lbl::Kareconst(30,else_lbl)::Kcompint31::escape::Klabel else_lbl::Kmakeblock(31, 1)::labeled_cont)
      else
	let code_construct cont = (* spiwack: variant of the global code_construct
                                     which handles dynamic compilation of
                                     integers *)
          let f_cont =
            let else_lbl = Label.create () in
	      [Kacc 0; Kpop 1; Kisconst else_lbl; Kareconst(30,else_lbl);
               Kcompint31; Kreturn 0; Klabel else_lbl; Kmakeblock(31, 1); Kreturn 0]
	  in
	  let lbl = Label.create() in
	    fun_code := [Ksequence (add_grab 31 lbl f_cont,!fun_code)];
	    Kclosure(lbl,0) :: cont
	in
	  if Int.equal nargs 0 then
	    code_construct cont
	  else
	    comp_app (fun _ _ _ cont -> code_construct cont)
              compile_str_cst reloc () args sz cont

(*(* template compilation for 2ary operation, it probably possible
   to make a generic such function with arity abstracted *)
let op2_compilation op =
  let code_construct normal cont =  (*kn cont =*)
     let f_cont =
         let else_lbl = Label.create () in
         Kareconst(2, else_lbl):: Kacc 0:: Kpop 1::
          op:: Kreturn 0:: Klabel else_lbl::
         (* works as comp_app with nargs = 2 and tailcall cont [Kreturn 0]*)
          (*Kgetglobal (get_alias !global_env kn):: *)
          normal::
          Kappterm(2, 2):: [] (* = discard_dead_code [Kreturn 0] *)
     in
     let lbl = Label.create () in
     fun_code := [Ksequence (add_grab 2 lbl f_cont, !fun_code)];
     Kclosure(lbl, 0)::cont
  in
  fun normal fc _ reloc args sz cont ->
  if not fc then raise Not_found else
  let nargs = Array.length args in
  if nargs=2 then (*if it is a fully applied addition*)
    let (escape, labeled_cont) = make_branch cont in
    let else_lbl = Label.create () in
      comp_args compile_constr reloc args sz
	(Kisconst else_lbl::(make_areconst 1  else_lbl
           (*Kaddint31::escape::Klabel else_lbl::Kpush::*)
           (op::escape::Klabel else_lbl::Kpush::
           (* works as comp_app with nargs = 2 and non-tailcall cont*)
           (*Kgetglobal (get_alias !global_env kn):: *)
           normal::
           Kapply 2::labeled_cont)))
  else if nargs=0 then
    code_construct normal cont
  else
    comp_app (fun _ _ _ cont -> code_construct normal cont)
      compile_constr reloc () args sz cont *)

(*template for n-ary operation, invariant: n>=1,
  the operations does the following :
  1/ checks if all the arguments are constants (i.e. non-block values)
  2/ if they are, uses the "op" instruction to execute
  3/ if at least one is not, branches to the normal behavior:
      Kgetglobal (get_alias !global_env kn) *)
let op_compilation n op =
  let code_construct reloc kn sz cont =
     let f_cont =
         let else_lbl = Label.create () in
         Kareconst(n, else_lbl):: Kacc 0:: Kpop 1::
          op:: Kreturn 0:: Klabel else_lbl::
         (* works as comp_app with nargs = n and tailcall cont [Kreturn 0]*)
          compile_get_global reloc kn sz (
            Kappterm(n, n):: []) (* = discard_dead_code [Kreturn 0] *)
     in
     let lbl = Label.create () in
     fun_code := [Ksequence (add_grab n lbl f_cont, !fun_code)];
     Kclosure(lbl, 0)::cont
  in
  fun kn fc reloc args sz cont ->
  if not fc then raise Not_found else
  let nargs = Array.length args in
  if Int.equal nargs n then (*if it is a fully applied addition*)
    let (escape, labeled_cont) = make_branch cont in
    let else_lbl = Label.create () in
      comp_args compile_constr reloc args sz
	(Kisconst else_lbl::(make_areconst (n-1) else_lbl
           (*Kaddint31::escape::Klabel else_lbl::Kpush::*)
           (op::escape::Klabel else_lbl::Kpush::
           (* works as comp_app with nargs = n and non-tailcall cont*)
           compile_get_global reloc kn sz (Kapply n::labeled_cont))))
  else if Int.equal nargs 0 then
    code_construct reloc kn sz cont
  else
    comp_app (fun reloc _ sz cont -> code_construct reloc kn sz cont)
      compile_constr reloc () args sz cont

let int31_escape_before_match fc cont =
  if not fc then
    raise Not_found
  else
    let escape_lbl, labeled_cont = label_code cont in
      (Kisconst escape_lbl)::Kdecompint31::labeled_cont
