open Util
open Names
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

(* Limitation due to OCaml's representation of non-constant
  constructors: limited to 245 + 1 (0 tag) cases. *)

exception TooLargeInductive of Pp.t

let max_nb_const = 0x1000000
let max_nb_block = 0x1000000 + Obj.last_non_constant_constructor_tag - 1

let str_max_constructors =
  Format.sprintf
    " which has more than %i constant constructors or more than %i non-constant constructors" max_nb_const max_nb_block

let check_compilable ib =

  if not (ib.mind_nb_args <= max_nb_block && ib.mind_nb_constant <= max_nb_const) then
    let msg =
      Pp.(str "Cannot compile code for virtual machine as it uses inductive "
          ++ Id.print ib.mind_typename ++ str str_max_constructors)
    in
    raise (TooLargeInductive msg)

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
  let check_inductive (_, i) mb = check_compilable mb.mind_packets.(i)
  let get_constant knu _ = Lconst knu
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
