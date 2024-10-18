(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Vmbytecodes
open Vmemitcodes
open Genlambda
open Vmlambda
open Constr
open Declarations
open Environ


(* Compilation of variables + computing free variables                    *)

(* The virtual machine doesn't distinguish closures and their environment *)

(* Representation of function environments :                              *)
(*        [clos_t | code | envofs=2 | fv1 | fv2 | ... | fvn ]             *)
(*                ^                                                       *)
(*  The offset for accessing free variables is 2 (we must skip the code   *)
(*  pointer and the environment offset).                                  *)
(*  While compiling, free variables are stored in [in_env] in order       *)
(*  opposite to machine representation, so we can add new free variables  *)
(*  easily (i.e. without changing the position of previous variables)     *)
(* Function arguments are on the stack in the same order as the           *)
(* application :  f arg1 ... argn                                         *)
(*   - the stack is then :                                                *)
(*        arg1 : ... argn : extra args : return addr : ...                *)
(* In the function body [arg1] is represented by de Bruijn [n], and       *)
(* [argn] by de Bruijn [1]                                                *)

(* Representation of environments of mutual fixpoints :                   *)
(* [clos_t|C1|envofs1| ... |infix_t|Ci|envofsi| ... |infix_t|Cnbr|envofsnbr=2| fv1 | fv2 | .... | fvn | type] *)
(*                                 ^                                      *)
(* type = [Ct1 | .... | Ctn]                                              *)
(* Ci is the code pointer of the i-th body                                *)
(* At runtime, a fixpoint environment (which is the same as the fixpoint  *)
(* itself) is a pointer to the field holding its code pointer.            *)
(* In each fixpoint body, de Bruijn [nbr] represents the first fixpoint   *)
(* and de Bruijn [1] the last one.                                        *)
(* Access to these variables is performed by the [Koffsetclosure n]       *)
(* instruction that shifts the environment pointer by [n] closuress.      *)

(* This allows representing mutual fixpoints in just one block.           *)
(* [Ct1 | ... | Ctn] is an array holding code pointers of the fixpoint    *)
(* types. They are used in conversion tests (which requires that          *)
(* fixpoint types must be convertible). Their environment is the one of   *)
(* the last fixpoint :                                                    *)
(* [clos_t|C1| ... |infix_t|Ci| ... |infix_t|Cnbr|envofsnbr=2| fv1 | fv2 | .... | fvn | type] *)
(*                                          ^                             *)

(* Representation of mutual cofix :                                       *)
(*  a1 =   [A_t | accumulate | [Cfx_t | fcofix1 ] ]                       *)
(*                ...                                                     *)
(*  anbr = [A_t | accumulate | [Cfx_t | fcofixnbr ] ]                     *)
(*                                                                        *)
(*  fcofix1   = [clos_t | code1   | envofs=2 | a1 |...| anbr | fv1 |...| fvn | type] *)
(*                      ^                                                 *)
(*                ...                                                     *)
(*  fcofixnbr = [clos_t | codenbr | envofs=2 | a1 |...| anbr | fv1 |...| fvn | type] *)
(*                      ^                                                 *)
(* The [ai] blocks are functions that accumulate their arguments:         *)
(*           ai arg1  argp --->                                           *)
(*    ai' = [A_t | accumulate | envofs | [Cfx_t | fcofixi] | arg1 | ... | argp ] *)
(* If such a block is matched against, we have to force evaluation,       *)
(* function [fcofixi] is then applied to [ai'] [arg1] ... [argp]          *)
(* (note that [ai'] is a pointer to the closure, passed as argument)      *)
(* Once evaluation is completed [ai'] is updated with the result:         *)
(*  ai' <--                                                               *)
(*   [A_t | accumulate | envofs | [Cfxe_t |fcofixi|result] | arg1 | ... | argp ] *)
(* This representation is nice because the application of the cofix is    *)
(* evaluated only once (it simulates a lazy evaluation)                   *)
(* Moreover, when cofix don't have arguments, it is possible to create    *)
(* a cycle, e.g.:                                                         *)
(*   cofix one := cons 1 one                                              *)
(*   a1 = [A_t | accumulate | envofs | [Cfx_t|fcofix1] ]                  *)
(*   fcofix1 = [clos_t | code | envofs | a1]                              *)
(* The result of evaluating [a1] is [cons_t | 1 | a1].                    *)
(* When [a1] is updated :                                                 *)
(*  a1 = [A_t | accumulate | envofs | [Cfxe_t | fcofix1 | [cons_t | 1 | a1]] ] *)
(* The cycle is created ...                                               *)
(*                                                                        *)
(* In Cfxe_t accumulators, we need to store [fcofixi] for testing         *)
(* conversion of cofixpoints (which is intentional).                      *)

module Fv_elem =
struct
type t = fv_elem

let compare e1 e2 = match e1, e2 with
| FVnamed id1, FVnamed id2 -> Id.compare id1 id2
| FVnamed _, (FVrel _) -> -1
| FVrel _, FVnamed _ -> 1
| FVrel r1, FVrel r2 -> Int.compare r1 r2

end

module FvMap = Map.Make(Fv_elem)

type fv_or_univ =
| FUniv
| FV of fv_elem

(*spiwack: both type have been moved from Vmbytegen because I needed then
  for the retroknowledge *)
type vm_env = {
    size : int;               (* longueur de la liste [n] *)
    fv_rev : fv_or_univ list; (* [fvn; ... ;fv1] *)
    fv_fwd : int FvMap.t;     (* reverse mapping *)
    fv_unv : int option;      (* position of the universe instance *)
  }


type comp_env = {
    arity : int;                 (* arity of the current function, 0 if none *)
    toplevel_univs : bool;       (* is the toplevel instance on the stack  *)
                                 (* universes are always at the bottom.    *)
    nb_stack : int;              (* number of variables on the stack       *)
    in_stack : int Range.t;      (* position in the stack                  *)
    pos_rec : instruction array; (* instruction to access mutually-defined functions *)
    offset : int;
    in_env : vm_env ref;         (* The free variables of the expression   *)
    max_stack_size : int ref;
    (* Maximal stack size reached during the current function body. Used to
       reallocate the stack if we lack space. *)
  }

type glob_env = {
  env : Environ.env;
  uinst_len : int * int; (** Size of the toplevel universe instance *)
  mutable fun_code : instruction list; (** Code of closures *)
}

let push_fun env c =
  env.fun_code <- Ksequence c :: env.fun_code

module Config = struct
  let stack_threshold = 256 (* see byterun/rocq_memory.h *)
  let stack_safety_margin = 15
end

type argument = ArgLambda of lambda | ArgInstance of UVars.Instance.t

let empty_fv = { size= 0;  fv_rev = []; fv_fwd = FvMap.empty; fv_unv = None }
let push_fv d e = {
  size = e.size + 1;
  fv_rev = (FV d) :: e.fv_rev;
  fv_fwd = FvMap.add d e.size e.fv_fwd;
  fv_unv = e.fv_unv;
}

let fv r = !(r.in_env)

let empty_comp_env ()=
  { arity = 0;
    toplevel_univs = false;
    nb_stack = 0;
    in_stack = Range.empty;
    pos_rec = [||];
    offset = 0;
    in_env = ref empty_fv;
    max_stack_size = ref 0;
  }

let set_max_stack_size (cenv : comp_env) stack_size =
  if stack_size > cenv.max_stack_size.contents then
    cenv.max_stack_size := stack_size

let ensure_stack_capacity (cenv : comp_env) code =
  let used_safe =
    cenv.max_stack_size.contents + Config.stack_safety_margin
  in
  if used_safe > Config.stack_threshold then
    Kensurestackcapacity used_safe :: code
  else code

(*i Creation functions for comp_env *)

let rec add_param n sz l =
  if Int.equal n 0 then l else add_param (n - 1) sz (Range.cons (n+sz) l)

let comp_env_fun ?(univs=false) arity =
  { arity;
    toplevel_univs = univs;
    nb_stack = arity;
    in_stack = add_param arity 0 Range.empty;
    pos_rec = [||];
    offset = 0;
    in_env = ref empty_fv;
    max_stack_size = ref 0;
  }


let comp_env_fix_type  rfv =
  { arity = 0;
    toplevel_univs = false;
    nb_stack = 0;
    in_stack = Range.empty;
    pos_rec = [||];
    offset = 0;
    in_env = rfv;
    max_stack_size = ref 0;
  }

let comp_env_fix ndef arity rfv =
   { arity;
     toplevel_univs = false;
     nb_stack = arity;
     in_stack = add_param arity 0 Range.empty;
     pos_rec = Array.init ndef (fun i -> Koffsetclosure i);
     offset = 0;
     in_env = rfv;
     max_stack_size = ref 0;
   }

let comp_env_cofix_type ndef rfv =
  { arity = 0;
    toplevel_univs = false;
    nb_stack = 0;
    in_stack = Range.empty;
    pos_rec = [||];
    offset = ndef;
    in_env = rfv;
    max_stack_size = ref 0;
  }

let comp_env_cofix ndef arity rfv =
   { arity;
     toplevel_univs = false;
     nb_stack = arity;
     in_stack = add_param arity 0 Range.empty;
     pos_rec = Array.init ndef (fun i -> Kenvacc (ndef - 1 - i));
     offset = ndef;
     in_env = rfv;
     max_stack_size = ref 0;
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
    in_stack = Range.cons (sz + 1) r.in_stack }

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
    Kacc(sz - (Range.get r.in_stack (i-1)))
  else
    let i = i - r.nb_stack in
    let nb_rec = Array.length r.pos_rec in
    if i <= nb_rec then
      r.pos_rec.(i - 1)
    else
      let i = i - nb_rec in
      let db = FVrel(i) in
      let env = !(r.in_env) in
      try Kenvacc(r.offset + find_at db env)
      with Not_found ->
        let pos = env.size in
        r.in_env := push_fv db env;
        Kenvacc(r.offset + pos)

let pos_instance r sz =
  (* Compilation of a universe variable can happen either at toplevel (the
  current closure correspond to a constant and has local universes) or in a
  local closure (which has no local universes). *)
  if r.toplevel_univs then
    (* Universe variables are represented by De Bruijn levels (not indices),
    starting at 0. The shape of the stack will be [v1|..|vn|inst|arg1..argp]
    with size = n + p + 1, and p = r.arity. So Kacc (sz - r.arity - 1) will access
    the instance. *)
    Kacc (sz - r.arity - 1)
  else
    let env = !(r.in_env) in
    let pos = match env.fv_unv with
    | None ->
      let pos = env.size in
      let env = {
        size = pos + 1;
        fv_rev = FUniv :: env.fv_rev;
        fv_fwd = env.fv_fwd;
        fv_unv = Some pos;
      }
      in
      let () = r.in_env := env in
      pos
    | Some p -> p
    in
    Kenvacc (r.offset + pos)

let is_toplevel_inst env u =
  UVars.eq_sizes env.uinst_len (UVars.Instance.length u)
  && let qs, us = UVars.Instance.to_array u in
  Array.for_all_i (fun i q -> Sorts.Quality.equal q (Sorts.Quality.var i)) 0 qs
  && Array.for_all_i (fun i l -> Univ.Level.equal l (Univ.Level.var i)) 0 us

let is_closed_inst u =
  let qs, us = UVars.Instance.to_array u in
  Array.for_all (fun q -> Option.is_empty (Sorts.Quality.var_index q)) qs
  && Array.for_all (fun l -> Option.is_empty (Univ.Level.var_index l)) us

(*i  Examination of the continuation *)

(* Discard all instructions up to the next label.                        *)
(* This function is to be applied to the continuation before adding a    *)
(* non-terminating instruction (branch, raise, return, appterm)          *)
(* in front of it.                                                       *)

let rec discard_dead_code = function
  | [] -> []
  | (Klabel _ | Krestart ) :: _ as cont -> cont
  | _ :: cont -> discard_dead_code cont

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

(* Extension of the continuation *)

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
    (* ai   = [At|accumulate|envofs|[Cfx_t|fcofix]|args]                  *)
  [ Kpush;
    Kpush;        (*                 stk = res::res::ai::args::ra::...    *)
    Kacc 2;
    Kfield 2;
    Kfield 0;
    Kmakeblock(2, cofix_evaluated_tag);
    Kpush;        (*  stk = [Cfxe_t|fcofix|res]::res::ai::args::ra::...*)
    Kacc 2;
    Ksetfield 2;  (*   ai = [At|accumulate|envofs|[Cfxe_t|fcofix|res]|args] *)
                  (*  stk = res::ai::args::ra::...                        *)
    Kacc 0;       (* accu = res                                           *)
    Kreturn (arity+2) ]

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

let code_makeblock cenv ~stack_size ~arity ~tag cont =
  if tag < Obj.last_non_constant_constructor_tag then
    Kmakeblock(arity, tag) :: cont
  else begin
    set_max_stack_size cenv (stack_size + 1);
    Kpush :: nest_block tag arity cont
  end

let compile_structured_constant cenv sc sz cont =
  set_max_stack_size cenv sz;
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
          (Kpush :: (comp_fun cenv f (sz+nargs) (Kshort_apply nargs :: cont)))
      else
        let lbl,cont1 = label_code cont in
        Kpush_retaddr lbl ::
        (comp_args comp_arg cenv args (sz + 3)
           (Kpush :: (comp_fun cenv f (sz+3+nargs) (Kapply nargs :: cont1))))

(* Compiling free variables *)

let compile_fv_elem cenv fv sz cont =
  match fv with
  | FV (FVrel i) -> pos_rel i cenv sz :: cont
  | FV (FVnamed id) -> pos_named id cenv :: cont
  | FUniv -> pos_instance cenv sz :: cont

let rec compile_fv cenv l sz cont =
  match l with
  | [] -> cont
  | [fvn] ->
    let () = set_max_stack_size cenv (sz + 1) in
    compile_fv_elem cenv fvn sz cont
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
       (match tps with
        | BCalias kn' -> get_alias env kn'
        | _ -> kn)

(* Some primitives are not implemented natively by the VM, but calling OCaml
   code instead *)
let get_caml_prim = let open CPrimitives in function
  | Arraymake -> Some CAML_Arraymake
  | Arrayget -> Some CAML_Arrayget
  | Arraydefault -> Some CAML_Arraydefault
  | Arrayset -> Some CAML_Arrayset
  | Arraycopy -> Some CAML_Arraycopy
  | Arraylength -> Some CAML_Arraylength
  | Stringmake -> Some CAML_Stringmake
  | Stringlength -> Some CAML_Stringlength
  | Stringget -> Some CAML_Stringget
  | Stringsub -> Some CAML_Stringsub
  | Stringcat -> Some CAML_Stringcat
  | Stringcompare -> Some CAML_Stringcompare
  | _ -> None

(* sz is the size of the local stack *)
let rec compile_lam env cenv lam sz cont =
  let () = set_max_stack_size cenv sz in
  match lam with
  | Lrel(_, i) -> pos_rel i cenv sz :: cont

  | Lint i -> compile_structured_constant cenv (Const_b0 i) sz cont

  | Lval v -> compile_structured_constant cenv (Const_val (get_lval v)) sz cont

  | Luint i -> compile_structured_constant cenv (Const_uint i) sz cont

  | Lfloat f -> compile_structured_constant cenv (Const_float f) sz cont

  | Lstring s -> compile_structured_constant cenv (Const_string s) sz cont

  | Lproj (p,arg) ->
     compile_lam env cenv arg sz (Kproj (Projection.Repr.arg p) :: cont)

  | Lvar id -> pos_named id cenv :: cont

  | Levar (evk, args) ->
      if Array.is_empty args then
        compile_structured_constant cenv (Const_evar evk) sz cont
      else
        (** Arguments are reversed in evar instances *)
        let args = Array.copy args in
        let () = Array.rev args in
        comp_app compile_structured_constant (compile_lam env) cenv (Const_evar evk) args sz cont

  | Lconst (kn,u) -> compile_constant env cenv kn u [||] sz cont

  | Lind (ind,u) ->
    if UVars.Instance.is_empty u then
      compile_structured_constant cenv (Const_ind ind) sz cont
    else comp_app compile_structured_constant (compile_instance env) cenv
        (Const_ind ind) [|u|] sz cont

  | Lsort s ->
    (* We represent universes as a global constant with local universes
       passed as the local universe instance, where we will substitute (after
       evaluation) [Var 0,...,Var n] with values of [arg0,...,argn] *)
    let has_var = match s with
    | Sorts.Set | Sorts.Prop | Sorts.SProp -> false
    | Sorts.Type u ->
      Univ.Universe.exists (fun (l, _) -> Option.has_some (Univ.Level.var_index l)) u
    | Sorts.QSort (q, u) ->
      Option.has_some (Sorts.QVar.var_index q)
      || Univ.Universe.exists (fun (l, _) -> Option.has_some (Univ.Level.var_index l)) u
    in
    let compile_instance cenv () sz cont =
      let () = set_max_stack_size cenv sz in
      pos_instance cenv sz :: cont
    in
    if not has_var then
      compile_structured_constant cenv (Const_sort s) sz cont
    else
      comp_app compile_structured_constant compile_instance cenv
        (Const_sort s) [|()|] sz cont

  | Llet (_id,def,body) ->
      compile_lam env cenv def sz
        (Kpush ::
         compile_lam env (push_local sz cenv) body (sz+1) (add_pop 1 cont))

  | Lprod (dom,codom) ->
     let cont1 =
       Kpush :: compile_lam env cenv dom (sz+1) (Kmakeblock (2,0) :: cont) in
     compile_lam env cenv codom sz cont1

  | Llam (ids,body) ->
     let arity = Array.length ids in
     let r_fun = comp_env_fun arity in
     let lbl_fun = Label.create() in
     let cont_fun = compile_lam env r_fun body arity [Kreturn arity] in
     let cont_fun = ensure_stack_capacity r_fun cont_fun in
     let () = push_fun env (add_grab arity lbl_fun cont_fun) in
     let fv = fv r_fun in
     compile_fv cenv fv.fv_rev sz (Kclosure(lbl_fun,fv.size) :: cont)

  | Lapp (f, args) ->
    begin match f with
    | Lconst (kn,u) -> compile_constant env cenv kn u args sz cont
    | _ -> comp_app (compile_lam env) (compile_lam env) cenv f args sz cont
    end

  | Lfix ((rec_args, _, init), (_decl, types, bodies)) ->
      let ndef = Array.length types in
      let rfv = ref empty_fv in
      let lbl_types = Array.make ndef Label.no in
      let lbl_bodies = Array.make ndef Label.no in
      (* Compiling types *)
      for i = 0 to ndef - 1 do
        let env_type = comp_env_fix_type rfv in
        let fcode = compile_lam env env_type types.(i) 0 [Kstop] in
        let fcode = ensure_stack_capacity env_type fcode in
        let lbl,fcode = label_code fcode in
        lbl_types.(i) <- lbl;
        push_fun env fcode
      done;
      (* Compiling bodies *)
      for i = 0 to ndef - 1 do
        let params,body = decompose_Llam bodies.(i) in
        let arity = Array.length params in
        let env_body = comp_env_fix ndef arity rfv in
        let cont1 = compile_lam env env_body body arity [Kreturn arity] in
        let cont1 = ensure_stack_capacity env_body cont1 in
        let lbl = Label.create () in
        lbl_bodies.(i) <- lbl;
        let fcode =  add_grabrec rec_args.(i) arity lbl cont1 in
        push_fun env fcode
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
      for i = 0 to ndef - 1 do
        let env_type = comp_env_cofix_type ndef rfv in
        let fcode = compile_lam env env_type types.(i) 0 [Kstop] in
        let fcode = ensure_stack_capacity env_type fcode in
        let lbl,fcode = label_code fcode in
        lbl_types.(i) <- lbl;
        push_fun env fcode
      done;
      (* Compiling bodies *)
      for i = 0 to ndef - 1 do
        let params,body = decompose_Llam bodies.(i) in
        let arity = Array.length params in
        let env_body = comp_env_cofix ndef arity rfv in
        let lbl = Label.create () in
        (* 4 stack slots are needed to update the cofix when forced *)
        let () = set_max_stack_size env_body (arity + 4) in
        let cont = compile_lam env env_body body (arity+1) (cont_cofix arity) in
        let cont = ensure_stack_capacity env_body cont in
        lbl_bodies.(i) <- lbl;
        push_fun env (add_grab (arity+1) lbl cont)
      done;
      let fv = !rfv in
      let () = set_max_stack_size cenv (sz + fv.size + ndef + 2) in
      compile_fv cenv fv.fv_rev sz
        (Kclosurecofix(fv.size, init, lbl_types, lbl_bodies) :: cont)

  | Lcase ((ci, rtbl, _), t, a, branches) ->
      let ind = ci.ci_ind in
      let mib = lookup_mind (fst ind) env.env in
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
      let ret_env = { cenv with max_stack_size = ref 0 } in
      let fcode = compile_lam env ret_env t sz [Kpop sz; Kstop] in
      let fcode = ensure_stack_capacity ret_env fcode in
      let lbl_typ,fcode = label_code fcode in
      let () = push_fun env fcode in
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

      let cont = discard_dead_code cont in
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
                set_max_stack_size cenv (sz_b + arity);
                Kpushfields arity :: code_b
              end
            else begin
                set_max_stack_size cenv (sz_b + arity + 1);
                Kacc 0::Kpop 1::Kpushfields(arity+1)::Kpop 1::code_b
              end
        in
        let lbl_b, code_b = label_code code_b in
        if tag < Obj.last_non_constant_constructor_tag then lbl_blocks.(tag) <- lbl_b
          else lbl_eblocks.(tag - Obj.last_non_constant_constructor_tag) <- lbl_b;
        c := code_b
      done;

      let annot =
        {rtbl = rtbl; tailcall = is_tailcall;
         Vmvalues.max_stack_size = cenv.max_stack_size.contents - sz}
      in

     (* Compiling branch for accumulators *)
      let lbl_accu, code_accu =
        set_max_stack_size cenv (sz+3);
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

  | Lmakeblock (_, tag, args) ->
    let arity = Array.length args in
    let cont = code_makeblock cenv ~stack_size:(sz+arity-1) ~arity ~tag cont in
    if Int.equal arity 0 then cont
    else comp_args (compile_lam env) cenv args sz cont

  | Lparray (args, def) ->
    (* Hack: brutally pierce through the abstraction of PArray *)
    let dummy = KerName.make (ModPath.MPfile DirPath.empty) (Names.Label.of_id @@ Id.of_string "dummy") in
    let dummy = (MutInd.make1 dummy, 0) in
    let ar, cont = match Vmlambda.as_value 0 args with
    | None ->
      (* build the ocaml array *)
      Lmakeblock (dummy, 0, args), cont
    | Some v ->
      (* dump the blob as is, but copy the resulting parray afterwards so that
         the blob is left untouched by modifications to the resulting parray *)
      let lbl = Label.create () in
      (* dummy label, the array will never be an accumulator *)
      Lval v, Klabel lbl :: Kcamlprim (CAML_Arraycopy, lbl) :: cont
    in
    let kind = Lmakeblock (dummy, 0, [|ar; def|]) in (* Parray.Array *)
    let v = Lmakeblock (dummy, 0, [|kind|]) (* the reference *) in
    compile_lam env cenv v sz cont

  | Lprim (kn, op, args) ->

    begin match get_caml_prim op with
    | Some cop ->
      let arity = CPrimitives.arity op in
      let nparams = CPrimitives.nparams op in
      let nargs = arity - nparams in
      assert (arity = Array.length args && arity <= 4 && nargs >= 1);
      let (jump, cont) = make_branch cont in
      let lbl_default = Label.create () in
      let default =
        let cont = [Kshort_apply arity; jump] in
        let cont = Kpush :: compile_get_global env cenv kn (sz + arity) cont in
        let cont =
          if Int.equal nparams 0 then cont
          else
            let params = Array.sub args 0 nparams in
            Kpush :: comp_args (compile_lam env) cenv params (sz + nargs) cont in
        Klabel lbl_default :: cont in
      let () = push_fun env default in
      let cont = Kcamlprim (cop, lbl_default) :: cont in
      comp_args (compile_lam env) cenv (Array.sub args nparams nargs) sz cont
    | None ->
      comp_args (compile_lam env) cenv args sz (Kprim(op, kn)::cont)
    end

and compile_get_global env cenv (kn,u) sz cont =
  let () = set_max_stack_size cenv sz in
  if UVars.Instance.is_empty u then
    Kgetglobal kn :: cont
  else
    comp_app (fun _ _ _ cont -> Kgetglobal kn :: cont)
      (compile_instance env) cenv () [|u|] sz cont

and compile_instance env cenv u sz cont =
  let () = set_max_stack_size cenv sz in
  if is_toplevel_inst env u then
    (* Optimization: do not reallocate the same instance *)
    pos_instance cenv sz :: cont
  else if is_closed_inst u then
    (* Optimization: allocate closed instances globally *)
    compile_structured_constant cenv (Const_univ_instance u) sz cont
  else
    pos_instance cenv sz :: Ksubstinstance u :: cont

and compile_constant env cenv kn u args sz cont =
  let () = set_max_stack_size cenv sz in
  if UVars.Instance.is_empty u then
    (* normal compilation *)
    comp_app (fun _ _ sz cont ->
        compile_get_global env cenv (kn,u) sz cont)
      (compile_lam env) cenv () args sz cont
  else
    let compile_arg cenv constr_or_uni sz cont =
      match constr_or_uni with
      | ArgLambda t -> compile_lam env cenv t sz cont
      | ArgInstance u -> compile_instance env cenv u sz cont
    in
    let all =
      Array.init (Array.length args + 1)
        (fun i -> if Int.equal i 0 then ArgInstance u else ArgLambda args.(i - 1))
    in
    comp_app (fun _ _ _ cont -> Kgetglobal kn :: cont)
      compile_arg cenv () all sz cont

let rocq_subst_instance : UVars.Instance.t -> UVars.Instance.t -> UVars.Instance.t =
  UVars.subst_instance_instance

let () = Callback.register "rocq_subst_instance" rocq_subst_instance

let is_univ_copy (maxq,maxu) u =
  let qs,us = UVars.Instance.to_array u in
  let check_array max var_index a =
    Array.length a = max
    && Array.for_all_i (fun i x -> Option.equal Int.equal (var_index x) (Some i)) 0 a
  in
  check_array maxq Sorts.Quality.var_index qs
  && check_array maxu Univ.Level.var_index us

let dump_bytecode = ref false

let dump_bytecodes init code fvs =
  let open Pp in
    (str "code =" ++ fnl () ++
     pp_bytecodes init ++ fnl () ++
     pp_bytecodes code ++ fnl () ++
     str "fv = " ++
     prlist_with_sep (fun () -> str "; ") pp_fv_elem fvs ++
     fnl ())

let skip_suffix l =
  let rec aux = function
  | [] -> None
  | b :: l ->
    match aux l with
    | None -> if b then None else Some [b]
    | Some l -> Some (b :: l)
  in
  match aux l with None -> [] | Some l -> l

let compile ?universes:(universes=(0,0)) env sigma c =
  Label.reset_label_counter ();
  let lam = lambda_of_constr env sigma c in
  let params, body = decompose_Llam lam in
  let arity = Array.length params in
  let mask =
    let rels = Genlambda.free_rels body in
    let init i = Int.Set.mem (arity - i) rels in
    let mask = List.init arity init in
    Array.of_list @@ skip_suffix mask
  in
  let cont = [Kstop] in
    let cenv, init_code, fun_code =
      if UVars.eq_sizes universes (0,0) then
        let cenv = empty_comp_env () in
        let env = { env; fun_code = []; uinst_len = (0,0) } in
        let cont = compile_lam env cenv lam 0 cont in
        let cont = ensure_stack_capacity cenv cont in
        cenv, cont, env.fun_code
      else
        (* We are going to generate a lambda, but merge the universe closure
         * with the function closure if it exists.
         *)
        let cenv = empty_comp_env () in
        let full_arity = arity + 1 in
        let r_fun = comp_env_fun ~univs:true arity in
        let lbl_fun = Label.create () in
        let env = { env; fun_code = []; uinst_len = universes } in
        let cont_fun = compile_lam env r_fun body full_arity [Kreturn full_arity] in
        let cont_fun = ensure_stack_capacity r_fun cont_fun in
        let () = push_fun env (add_grab full_arity lbl_fun cont_fun) in
        let fv = fv r_fun in
        let init_code = compile_fv cenv fv.fv_rev 0 (Kclosure(lbl_fun,fv.size) :: cont) in
        let init_code = ensure_stack_capacity cenv init_code in
        cenv, init_code, env.fun_code
    in
    let map_fv = function
    | FV fv -> fv
    | FUniv -> assert false
    in
    let fv = List.rev_map map_fv (!(cenv.in_env).fv_rev) in
    (if !dump_bytecode then
      Feedback.msg_debug (dump_bytecodes init_code fun_code fv)) ;
    let res = init_code @ fun_code in
    let code, patch = to_memory (Array.of_list fv) res in
    mask, code, patch

let warn_compile_error =
  CWarnings.create ~name:"bytecode-compiler-failed-compilation" ~category:CWarnings.CoreCategories.bytecode_compiler
    Vmerrors.pr_error

let compile ~fail_on_error ?universes env sigma c =
  try NewProfile.profile "vm_compile" (fun () -> Some (compile ?universes env sigma c)) ()
  with Vmerrors.CompileError msg as exn ->
    let exn = Exninfo.capture exn in
    if fail_on_error then
      Exninfo.iraise exn
    else begin
      warn_compile_error msg;
      None
    end

let compile_constant_body ~fail_on_error env univs = function
  | Undef _ | OpaqueDef _ -> Some BCconstant
  | Primitive _ | Symbol _ -> None
  | Def body ->
      let instance_size = UVars.AbstractContext.size (Declareops.universes_context univs) in
      let alias =
        match kind body with
        | Const (kn',u) when is_univ_copy instance_size u ->
            (* we use the canonical name of the constant*)
            let con = Constant.make1 (Constant.canonical kn') in
            let kn = get_alias env con in
            let cb = lookup_constant kn env in
            begin match cb.const_body with
            | Primitive _ -> None
            | _ -> Some kn
            end
        | _ -> None in
      match alias with
      | Some kn -> Some (BCalias kn)
      | _ ->
        let res = compile ~fail_on_error ~universes:instance_size env (empty_evars env) body in
        Option.map (fun (mask, code, patch) -> BCdefined (mask, code, patch)) res

(* Shortcut of the previous function used during module strengthening *)

let compile_alias kn = BCalias (Constant.make1 (Constant.canonical kn))
