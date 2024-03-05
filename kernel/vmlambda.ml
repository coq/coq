open Util
open Esubst
open Declarations
open Genlambda
open Vmvalues

type lambda = structured_values Genlambda.lambda

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
  | Lval v -> v
  | Lint i -> val_of_int i
  | _ -> raise Not_found

let as_value tag args =
  if Array.for_all is_value args then
    if tag < Obj.last_non_constant_constructor_tag then
      Some (val_of_block tag (Array.map get_value args))
    else
      let args = Array.map get_value args in
      let args = Array.append [| val_of_int (tag - Obj.last_non_constant_constructor_tag) |] args in
      Some (val_of_block Obj.last_non_constant_constructor_tag args)
  else None

module Val =
struct
  type value = structured_values
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
