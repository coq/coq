(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Author: Benjamin Grégoire as part of the bytecode-based virtual reduction
   machine, Oct 2004 *)
(* Extension: Arnaud Spiwack (support for native arithmetic), May 2005 *)

open Util
open Names
open Vmvalues
open Cbytecodes
open Cemitcodes
open Clambda
open Constr
open Declarations
open Environ


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
(* (note that [ai'] is a pointer to the closure, passed as argument)      *)
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

module Fv_elem =
struct
type t = fv_elem

let compare e1 e2 = match e1, e2 with
| FVnamed id1, FVnamed id2 -> Id.compare id1 id2
| FVnamed _, (FVrel _ | FVuniv_var _ | FVevar _) -> -1
| FVrel _, FVnamed _ -> 1
| FVrel r1, FVrel r2 -> Int.compare r1 r2
| FVrel _, (FVuniv_var _ | FVevar _) -> -1
| FVuniv_var i1, FVuniv_var i2 -> Int.compare i1 i2
| FVuniv_var _, (FVnamed _ | FVrel _) -> 1
| FVuniv_var _, FVevar _ -> -1
| FVevar _, (FVnamed _ | FVrel _ | FVuniv_var _) -> 1
| FVevar e1, FVevar e2 -> Evar.compare e1 e2

end

module FvMap = Map.Make(Fv_elem)

(*spiwack: both type have been moved from Cbytegen because I needed then
  for the retroknowledge *)
type vm_env = {
    size : int;              (* longueur de la liste [n] *)
    fv_rev : fv_elem list;   (* [fvn; ... ;fv1] *)
    fv_fwd : int FvMap.t;    (* reverse mapping *)
  }


type comp_env = {
    arity : int;                 (* arity of the current function, 0 if none *)
    nb_uni_stack : int ;         (* number of universes on the stack,      *)
                                 (* universes are always at the bottom.    *)
    nb_stack : int;              (* number of variables on the stack       *)
    in_stack : int list;         (* position in the stack                  *)
    nb_rec : int;                (* number of mutually recursive functions *)
    pos_rec  : instruction list; (* instruction d'acces pour les variables *)
                                 (*  de point fix ou de cofix              *)
    offset : int;
    in_env : vm_env ref          (* The free variables of the expression   *)
  }

module Config = struct
  let stack_threshold = 256 (* see byterun/coq_memory.h *)
  let stack_safety_margin = 15
end

type argument = ArgLambda of lambda | ArgUniv of Univ.Level.t

let empty_fv = { size= 0;  fv_rev = []; fv_fwd = FvMap.empty }
let push_fv d e = {
  size = e.size + 1;
  fv_rev = d :: e.fv_rev;
  fv_fwd = FvMap.add d e.size e.fv_fwd;
}

let fv r = !(r.in_env)

let empty_comp_env ()=
  { arity = 0;
    nb_uni_stack = 0;
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
  { arity;
    nb_uni_stack = univs ;
    nb_stack = arity;
    in_stack = add_param arity 0 [];
    nb_rec = 0;
    pos_rec = [];
    offset = 1;
    in_env = ref empty_fv
  }


let comp_env_fix_type  rfv =
  { arity = 0;
    nb_uni_stack = 0;
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
   { arity;
     nb_uni_stack = 0;
     nb_stack = arity;
     in_stack = add_param arity 0 [];
     nb_rec = ndef;
     pos_rec = !prec;
     offset = 2 * (ndef - curr_pos - 1)+1;
     in_env = rfv
   }

let comp_env_cofix_type ndef rfv =
  { arity = 0;
    nb_uni_stack = 0;
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
   { arity;
     nb_uni_stack = 0;
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
  (* Compilation of a universe variable can happen either at toplevel (the
  current closure correspond to a constant and has local universes) or in a
  local closure (which has no local universes). *)
  if r.nb_uni_stack != 0 then
    (* Universe variables are represented by De Bruijn levels (not indices),
    starting at 0. The shape of the stack will be [v1|..|vn|u1..up|arg1..argq]
    with size = n + p + q, and q = r.arity. So Kacc (sz - r.arity - 1) will access
    the last universe. *)
    Kacc (sz - r.arity - (r.nb_uni_stack - i))
  else
    let env = !(r.in_env) in
    let db = FVuniv_var i in
    try Kenvacc (r.offset + find_at db env)
    with Not_found ->
      let pos = env.size in
      r.in_env := push_fv db env;
      Kenvacc(r.offset + pos)

let pos_evar evk r =
  let env = !(r.in_env) in
  let cid = FVevar evk in
  try Kenvacc(r.offset + find_at cid env)
  with Not_found ->
    let pos = env.size in
    r.in_env := push_fv cid env;
    Kenvacc (r.offset + pos)

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


(* Code of closures *)
let fun_code = ref []

let init_fun_code () = fun_code := []

(* Compilation of constructors and inductive types *)


(*
If [tag] hits the OCaml limitation for non constant constructors, we switch to
another representation for the remaining constructors:
[last_variant_tag|tag - Obj.last_non_constant_constructor_tag|args]

We subtract Obj.last_non_constant_constructor_tag for efficiency of match interpretation.
 *)

let nest_block tag arity cont =
  Kconst (Const_b0 (tag - Obj.last_non_constant_constructor_tag)) ::
    Kmakeblock(arity+1, Obj.last_non_constant_constructor_tag) :: cont

let code_makeblock ~stack_size ~arity ~tag cont = 
  if tag < Obj.last_non_constant_constructor_tag then
    Kmakeblock(arity, tag) :: cont
  else begin
    set_max_stack_size (stack_size + 1);
    Kpush :: nest_block tag arity cont
  end

let compile_structured_constant _cenv sc sz cont =
  set_max_stack_size sz;
  Kconst sc :: cont

(* compiling application *)
let comp_args comp_expr cenv args sz cont =
  let nargs_m_1 = Array.length args - 1 in
  let c = ref (comp_expr cenv args.(0) (sz + nargs_m_1) cont) in
  for i = 1 to nargs_m_1 do
    c := comp_expr cenv args.(i) (sz + nargs_m_1 - i) (Kpush :: !c)
  done;
  !c

let comp_app comp_fun comp_arg cenv f args sz cont =
  let nargs = Array.length args in
  if Int.equal nargs 0 then comp_fun cenv f sz cont
  else
  match is_tailcall cont with
  | Some k ->
      comp_args comp_arg cenv args sz
	(Kpush ::
         comp_fun cenv f (sz + nargs)
	   (Kappterm(nargs, k + nargs) :: (discard_dead_code cont)))
  | None ->
      if nargs <= 4 then
        comp_args comp_arg cenv args sz
          (Kpush :: (comp_fun cenv f (sz+nargs) (Kapply nargs :: cont)))
      else
	let lbl,cont1 = label_code cont in
	Kpush_retaddr lbl ::
        (comp_args comp_arg cenv args (sz + 3)
           (Kpush :: (comp_fun cenv f (sz+3+nargs) (Kapply nargs :: cont1))))

(* Compiling free variables *)

let compile_fv_elem cenv fv sz cont =
  match fv with
  | FVrel i -> pos_rel i cenv sz :: cont
  | FVnamed id -> pos_named id cenv :: cont
  | FVuniv_var i -> pos_universe_var i cenv sz :: cont
  | FVevar evk -> pos_evar evk cenv :: cont

let rec compile_fv cenv l sz cont =
  match l with
  | [] -> cont
  | [fvn] -> set_max_stack_size (sz + 1); compile_fv_elem cenv fvn sz cont
  | fvn :: tl ->
      compile_fv_elem cenv fvn sz
        (Kpush :: compile_fv cenv tl (sz + 1) cont)


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
let rec compile_lam env cenv lam sz cont =
  set_max_stack_size sz;
  match lam with
  | Lrel(_, i) -> pos_rel i cenv sz :: cont

  | Lint i -> compile_structured_constant cenv (Const_b0 i) sz cont

  | Lval v -> compile_structured_constant cenv (Const_val v) sz cont

  | Luint i -> compile_structured_constant cenv (Const_uint i) sz cont

  | Lproj (p,arg) ->
     compile_lam env cenv arg sz (Kproj p :: cont)

  | Lvar id -> pos_named id cenv :: cont

  | Levar (evk, args) ->
      if Array.is_empty args then
        compile_fv_elem cenv (FVevar evk) sz cont
      else
        (** Arguments are reversed in evar instances *)
        let args = Array.copy args in
        let () = Array.rev args in
        comp_app compile_fv_elem (compile_lam env) cenv (FVevar evk) args sz cont

  | Lconst (kn,u) -> compile_constant env cenv kn u [||] sz cont

  | Lind (ind,u) ->
    if Univ.Instance.is_empty u then
      compile_structured_constant cenv (Const_ind ind) sz cont
    else comp_app compile_structured_constant compile_universe cenv
        (Const_ind ind) (Univ.Instance.to_array u) sz cont

  | Lsort (Sorts.Prop | Sorts.Set as s) ->
    compile_structured_constant cenv (Const_sort s) sz cont
  | Lsort (Sorts.Type u) ->
    (* We represent universes as a global constant with local universes
       "compacted", i.e. as [u arg0 ... argn] where we will substitute (after
       evaluation) [Var 0,...,Var n] with values of [arg0,...,argn] *)
    let u,s = Univ.compact_univ u in
    let compile_get_univ cenv idx sz cont =
      set_max_stack_size sz;
      compile_fv_elem cenv (FVuniv_var idx) sz cont
    in
    if List.is_empty s then
      compile_structured_constant cenv (Const_sort (Sorts.Type u)) sz cont
    else
      comp_app compile_structured_constant compile_get_univ cenv
        (Const_sort (Sorts.Type u)) (Array.of_list s) sz cont

  | Llet (_id,def,body) ->
      compile_lam env cenv def sz
        (Kpush ::
         compile_lam env (push_local sz cenv) body (sz+1) (add_pop 1 cont))

  | Lprod (dom,codom) ->
     let cont1 =
       Kpush :: compile_lam env cenv dom (sz+1) (Kmakeprod :: cont) in
     compile_lam env cenv codom sz cont1

  | Llam (ids,body) ->
     let arity = Array.length ids in
     let r_fun = comp_env_fun arity in
     let lbl_fun = Label.create() in
     let cont_fun =
       ensure_stack_capacity (compile_lam env r_fun body arity) [Kreturn arity]
     in
     fun_code := [Ksequence(add_grab arity lbl_fun cont_fun,!fun_code)];
     let fv = fv r_fun in
     compile_fv cenv fv.fv_rev sz (Kclosure(lbl_fun,fv.size) :: cont)

  | Lapp (f, args) ->
    begin match f with
    | Lconst (kn,u) -> compile_constant env cenv kn u args sz cont
    | _ -> comp_app (compile_lam env) (compile_lam env) cenv f args sz cont
    end

  | Lfix ((rec_args, init), (_decl, types, bodies)) ->
      let ndef = Array.length types in
      let rfv = ref empty_fv in
      let lbl_types = Array.make ndef Label.no in
      let lbl_bodies = Array.make ndef Label.no in
      (* Compiling types *)
      let env_type = comp_env_fix_type rfv in
      for i = 0 to ndef - 1 do
        let fcode =
          ensure_stack_capacity (compile_lam env env_type types.(i) 0) [Kstop]
        in
        let lbl,fcode = label_code fcode in
        lbl_types.(i) <- lbl;
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compiling bodies *)
      for i = 0 to ndef - 1 do
        let params,body = decompose_Llam bodies.(i) in
        let arity = Array.length params in
	let env_body = comp_env_fix ndef i arity rfv in
        let cont1 =
          ensure_stack_capacity (compile_lam env env_body body arity) [Kreturn arity]
        in
	let lbl = Label.create () in
	lbl_bodies.(i) <- lbl;
	let fcode =  add_grabrec rec_args.(i) arity lbl cont1 in
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      let fv = !rfv in
      compile_fv cenv fv.fv_rev sz
	(Kclosurerec(fv.size,init,lbl_types,lbl_bodies) :: cont)


  | Lcofix(init, (_decl,types,bodies)) ->
      let ndef = Array.length types in
      let lbl_types = Array.make ndef Label.no in
      let lbl_bodies = Array.make ndef Label.no in
      (* Compiling types *)
      let rfv = ref empty_fv in
      let env_type = comp_env_cofix_type ndef rfv in
      for i = 0 to ndef - 1 do
        let fcode =
          ensure_stack_capacity (compile_lam env env_type types.(i) 0) [Kstop]
        in
        let lbl,fcode = label_code fcode in
        lbl_types.(i) <- lbl;
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compiling bodies *)
      for i = 0 to ndef - 1 do
        let params,body = decompose_Llam bodies.(i) in
        let arity = Array.length params in
	let env_body = comp_env_cofix ndef arity rfv in
	let lbl = Label.create () in
        let comp arity =
          (* 4 stack slots are needed to update the cofix when forced *)
          set_max_stack_size (arity + 4);
          compile_lam env env_body body (arity+1) (cont_cofix arity)
        in
	let cont = ensure_stack_capacity comp arity in
	lbl_bodies.(i) <- lbl;
	fun_code := [Ksequence(add_grab (arity+1) lbl cont,!fun_code)];
      done;
      let fv = !rfv in
      set_max_stack_size (sz + fv.size + ndef + 2);
      compile_fv cenv fv.fv_rev sz
	(Kclosurecofix(fv.size, init, lbl_types, lbl_bodies) :: cont)

  | Lif(t, bt, bf) ->
      let branch, cont = make_branch cont in
      let lbl_true =  Label.create() in
      let lbl_false = Label.create() in
      compile_lam env cenv t sz
        (Kswitch([|lbl_true;lbl_false|],[||]) ::
         Klabel lbl_false ::
         compile_lam env cenv bf sz
           (branch ::
            Klabel lbl_true ::
            compile_lam env cenv bt sz cont))

  | Lcase(ci,rtbl,t,a,branches) ->
      let ind = ci.ci_ind in
      let mib = lookup_mind (fst ind) env in
      let oib = mib.mind_packets.(snd ind) in
      let lbl_consts = Array.make oib.mind_nb_constant Label.no in
      let nallblock = oib.mind_nb_args + 1 in (* +1 : accumulate *)
      let nconst = Array.length branches.constant_branches in
      let nblock = min nallblock (Obj.last_non_constant_constructor_tag + 1) in
      let lbl_blocks = Array.make nblock Label.no in
      let neblock = max 0 (nallblock - Obj.last_non_constant_constructor_tag) in
      let lbl_eblocks = Array.make neblock Label.no in 
      let branch1, cont = make_branch cont in
      (* Compilation of the return type *)
      let fcode =
        ensure_stack_capacity (compile_lam env cenv t sz) [Kpop sz; Kstop]
      in
      let lbl_typ,fcode = label_code fcode in
      fun_code := [Ksequence(fcode,!fun_code)];
      (* Compilation of the branches *)
      let lbl_sw = Label.create () in
      let sz_b,branch,is_tailcall =
        match branch1 with
        | Kreturn k ->
          assert (Int.equal k sz) ;
          sz, branch1, true
        | Kbranch _ -> sz+3, Kjump, false
        | _ -> assert false
      in

      let c = ref cont in
      (* Perform the extra match if needed (too many block constructors) *)
      if neblock <> 0 then begin
        let lbl_b, code_b = 
          label_code (
            Kpush :: Kfield 0 :: Kswitch(lbl_eblocks, [||]) :: !c) in
        lbl_blocks.(Obj.last_non_constant_constructor_tag) <- lbl_b;
        c := code_b
      end;

      (* Compilation of constant branches *)
      for i = nconst - 1 downto 0 do
        let aux =
          compile_lam env cenv branches.constant_branches.(i) sz_b (branch::!c)
        in
        let lbl_b,code_b = label_code aux in
        lbl_consts.(i) <- lbl_b;
        c := code_b
      done;
      (* -1 for accu branch *)
      for i = nallblock - 2 downto 0 do
        let tag = i + 1 in
        let (ids, body) = branches.nonconstant_branches.(i) in
        let arity = Array.length ids in
        let code_b =
          compile_lam env (push_param arity sz_b cenv)
            body (sz_b+arity) (add_pop arity (branch::!c)) in
        let code_b =
            if tag < Obj.last_non_constant_constructor_tag then begin
                set_max_stack_size (sz_b + arity);
                Kpushfields arity :: code_b
              end
            else begin
                set_max_stack_size (sz_b + arity + 1);
                Kacc 0::Kpop 1::Kpushfields(arity+1)::Kpop 1::code_b
              end
        in
        let lbl_b, code_b = label_code code_b in
        if tag < Obj.last_non_constant_constructor_tag then lbl_blocks.(tag) <- lbl_b
          else lbl_eblocks.(tag - Obj.last_non_constant_constructor_tag) <- lbl_b;
        c := code_b
      done;

      let annot =
        {ci = ci; rtbl = rtbl; tailcall = is_tailcall;
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
      compile_lam env cenv a sz code_sw

  | Lmakeblock (tag,args) ->
    let arity = Array.length args in
    let cont = code_makeblock ~stack_size:(sz+arity-1) ~arity ~tag cont in
    comp_args (compile_lam env) cenv args sz cont

  | Lprim (kn, op, args) ->
    comp_args (compile_lam env) cenv args sz (Kprim(op, kn)::cont)

and compile_get_global cenv (kn,u) sz cont =
  set_max_stack_size sz;
  if Univ.Instance.is_empty u then
    Kgetglobal kn :: cont
  else
    comp_app (fun _ _ _ cont -> Kgetglobal kn :: cont)
      compile_universe cenv () (Univ.Instance.to_array u) sz cont

and compile_universe cenv uni sz cont =
  set_max_stack_size sz;
  match Univ.Level.var_index uni with
  | None -> compile_structured_constant cenv (Const_univ_level uni) sz cont
  | Some idx -> pos_universe_var idx cenv sz :: cont

and compile_constant env cenv kn u args sz cont =
  set_max_stack_size sz;
  if Univ.Instance.is_empty u then
    (* normal compilation *)
    comp_app (fun _ _ sz cont ->
        compile_get_global cenv (kn,u) sz cont)
      (compile_lam env) cenv () args sz cont
  else
    let compile_arg cenv constr_or_uni sz cont =
      match constr_or_uni with
      | ArgLambda t -> compile_lam env cenv t sz cont
      | ArgUniv uni -> compile_universe cenv uni sz cont
    in
    let u = Univ.Instance.to_array u in
    let lu = Array.length u in
    let all =
      Array.init (lu + Array.length args)
        (fun i -> if i < lu then ArgUniv u.(i) else ArgLambda args.(i-lu))
    in
    comp_app (fun _ _ _ cont -> Kgetglobal kn :: cont)
      compile_arg cenv () all sz cont

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

let dump_bytecode = ref false

let dump_bytecodes init code fvs =
  let open Pp in
    (str "code =" ++ fnl () ++
     pp_bytecodes init ++ fnl () ++
     pp_bytecodes code ++ fnl () ++
     str "fv = " ++
     prlist_with_sep (fun () -> str "; ") pp_fv_elem fvs ++
     fnl ())

let compile ~fail_on_error ?universes:(universes=0) env c =
  init_fun_code ();
  Label.reset_label_counter ();
  let cont = [Kstop] in
  try
    let cenv, init_code =
      if Int.equal universes 0 then
        let lam = lambda_of_constr ~optimize:true env c in
        let cenv = empty_comp_env () in
        cenv, ensure_stack_capacity (compile_lam env cenv lam 0) cont
      else
        (* We are going to generate a lambda, but merge the universe closure
         * with the function closure if it exists.
         *)
        let lam = lambda_of_constr ~optimize:true env c in
        let params, body = decompose_Llam lam in
        let arity = Array.length params in
        let cenv = empty_comp_env () in
        let full_arity = arity + universes in
        let r_fun = comp_env_fun ~univs:universes arity in
        let lbl_fun = Label.create () in
        let cont_fun =
          ensure_stack_capacity (compile_lam env r_fun body full_arity)
                         [Kreturn full_arity]
        in
        fun_code := [Ksequence(add_grab full_arity lbl_fun cont_fun,!fun_code)];
        let fv = fv r_fun in
        let init_code =
          ensure_stack_capacity (compile_fv cenv fv.fv_rev 0)
                         (Kclosure(lbl_fun,fv.size) :: cont)
        in
        cenv, init_code
    in
    let fv = List.rev (!(cenv.in_env).fv_rev) in
    (if !dump_bytecode then
      Feedback.msg_debug (dump_bytecodes init_code !fun_code fv)) ;
    Some (init_code,!fun_code, Array.of_list fv)
  with TooLargeInductive msg ->
    let fn = if fail_on_error then CErrors.user_err ?loc:None ~hdr:"compile" else
        (fun x -> Feedback.msg_warning x) in
    fn msg; None

let compile_constant_body ~fail_on_error env univs = function
  | Undef _ | OpaqueDef _ | Primitive _ -> Some BCconstant
  | Def sb ->
      let body = Mod_subst.force_constr sb in
      let instance_size =
        match univs with
        | Monomorphic_const _ -> 0
        | Polymorphic_const univ -> Univ.AUContext.size univ
      in
      match kind body with
	| Const (kn',u) when is_univ_copy instance_size u ->
	    (* we use the canonical name of the constant*)
	    let con= Constant.make1 (Constant.canonical kn') in
	      Some (BCalias (get_alias env con))
	| _ ->
            let res = compile ~fail_on_error ~universes:instance_size env body in
	      Option.map (fun x -> BCdefined (to_memory x)) res

(* Shortcut of the previous function used during module strengthening *)

let compile_alias kn = BCalias (Constant.make1 (Constant.canonical kn))
