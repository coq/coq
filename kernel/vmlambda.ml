open Util
open Esubst
open Declarations
open Genlambda
open Vmvalues

type lval = int * structured_values (* keep the hash *)
type lambda = lval Genlambda.lambda

let get_lval (_, v) = v

(** Simplification of lambda expression *)

(* TODO: make the VM and native agree *)
let can_subst lam =
  match lam with
  | Lrel _ | Lvar _ | Lconst _ | Luint _
  | Lval _ | Lsort _ | Lind _ -> true
  | _ -> false

let simplify subst lam = simplify can_subst subst lam

(*s Translation from [constr] to [lambda] *)

(* Translation of constructor *)

let is_value lc =
  match lc with
  | Lval _ | Lint _ | Luint _ -> true
  | _ -> false

let get_value lc =
  match lc with
  | Luint i -> val_of_uint i
  | Lval (_, v) -> v
  | Lint i -> val_of_int i
  | _ -> assert false

let hash_block tag args =
  let open Hashset.Combine in
  let fold accu v =
    let h = match v with
    | Luint i -> Uint63.hash i
    | Lint i -> Hashtbl.hash (i : int)
    | Lval (h, _) -> h
    | _ -> assert false
    in
    combine accu h
  in
  combine tag (Array.fold_left fold 0 args)

module HashBlock =
struct
  type t = int * structured_values array * structured_values (* tag, block, value *)
  let eq (tag1, args1, _) (tag2, args2, _) =
    Int.equal tag1 tag2 && CArray.equal (==) args1 args2
end

module HashsetBlock = Hashset.Make(HashBlock)

let block_table = HashsetBlock.create 97

let as_value tag args =
  if Array.for_all is_value args then
    let h = hash_block tag args in
    let args = Array.map get_value args in
    if tag < Obj.last_non_constant_constructor_tag then
      let block = val_of_block tag args in
      let (_, _, block) = HashsetBlock.repr h (tag, args, block) block_table in
      Some (h, block)
    else
      let args = Array.append [| val_of_int (tag - Obj.last_non_constant_constructor_tag) |] args in
      let block = val_of_block Obj.last_non_constant_constructor_tag args in
      let (_, _, block) = HashsetBlock.repr h (tag, args, block) block_table in
      Some (h, block)
  else None

module Val =
struct
  type value = int * structured_values
  let as_value = as_value
  let check_inductive (_, i) mb =
    let { mind_typename=name; mind_nb_args; mind_nb_constant; _ } = mb.mind_packets.(i) in
    Vmerrors.check_compilable_ind ~name ~mind_nb_args ~mind_nb_constant
end

module Lambda = Genlambda.Make(Val)

(*********************************)
let dump_lambda = ref false

let optimize_lambda lam =
  let subst_id = subs_id 0 in
  let lam = simplify subst_id lam in
  remove_let subst_id lam

let lambda_of_constr ~optimize env sigma c =
  let lam = Lambda.lambda_of_constr env sigma c in
  let lam = if optimize then optimize_lambda lam else lam in
  if !dump_lambda then
    Feedback.msg_debug (pp_lam lam);
  lam
