(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util
open Decl_kinds
open Term
open Declare
open Entries
open Names
open Nametab
open Libnames
open Pp
open Coqlib
open Declarations
open Termops
open Environ
open Inductiveops
open Reductionops

(* From extraction *)

open Table

(* Coq values *)

let intextr_modules = init_modules @ [["Coq"; "Lists"; "List"]; ["Coq"; "intextr"; "Ml"]]
let constant = gen_constant_in_modules "Intextr" intextr_modules

let coq_O = lazy (constant "O")
let coq_S = lazy (constant "S")

let coq_nil = lazy (constant "nil")
let coq_cons = lazy (constant "cons")

let coq_term = lazy (constant "term")
let coq_TDummy = lazy (constant "TDummy")
let coq_TVar = lazy (constant "TVar")
let coq_TLet = lazy (constant "TLet")
let coq_TFun = lazy (constant "TFun")
let coq_TFix = lazy (constant "TFix")
let coq_TApply = lazy (constant "TApply")
let coq_TMatch = lazy (constant "TMatch")
let coq_TConstr = lazy (constant "TConstr")

let coq_pat = lazy (constant "pat")
let coq_Patc = lazy (constant "Patc")


(* A toy example *)

let id_term =
  mkLambda (Anonymous, mkSort mk_Set,
            mkLambda (Anonymous, mkRel 1,
                      mkRel 1))

(* OCaml counterpart for mini-ML/Coq terms *)

type term =
  | TDummy
  | TConstant of constr
  | TVar of int
  | TLet of term * term
  | TFun of term
  | TFix of term
  | TApply of term * term
  | TConstr of int * (term list)
  | TMatch of term * (pat list)
and pat =
  | Patc of int * term

let rec mkNat = function
  | 0 -> Lazy.force coq_O
  | n -> mkApp (Lazy.force coq_S, [| mkNat (n-1) |])

let rec mkTerm = function
  | TDummy ->
      Lazy.force coq_TDummy
  | TConstant c ->
      c
  | TVar i ->
      mkApp (Lazy.force coq_TVar, [| mkNat i |])
  | TLet (a, b) ->
      mkApp (Lazy.force coq_TLet, [| mkTerm a; mkTerm b |])
  | TFun a ->
      mkApp (Lazy.force coq_TFun, [| mkTerm a |])
  | TFix a ->
      mkApp (Lazy.force coq_TFix, [| mkTerm a |])
  | TApply (a, b) ->
      mkApp (Lazy.force coq_TApply, [| mkTerm a; mkTerm b |])
  | TConstr (i, la) ->
      mkApp (Lazy.force coq_TConstr, [| mkNat i; mkTermList la |])
  | TMatch (a, lp) ->
      mkApp (Lazy.force coq_TMatch, [| mkTerm a; mkPatList lp |])

and mkPat (Patc (c, b)) =
  mkApp (Lazy.force coq_Patc, [| mkNat c; mkTerm b |])

and mkPatList = function
  | [] -> mkApp (Lazy.force coq_nil, [| Lazy.force coq_pat |])
  | a::q -> mkApp (Lazy.force coq_cons,
                   [| Lazy.force coq_pat; mkPat a; mkPatList q |])

and mkTermList = function
  | [] -> mkApp (Lazy.force coq_nil, [| Lazy.force coq_term |])
  | a::q -> mkApp (Lazy.force coq_cons,
                   [| Lazy.force coq_term; mkTerm a; mkTermList q |])

(* Some useful functions *)

let none = Evd.empty
let type_of env c = Retyping.get_type_of env none (strip_outer_cast c)
let sort_of env c = Retyping.get_sort_family_of env none (strip_outer_cast c)

(*s [discard env t] is true if a term of type [t] must be discarded. *)

let rec discard env t =
  let t = whd_betadeltaiota env none t in
  match kind_of_term t with
    | Prod (x, t, c) -> discard (push_rel (x, None, t) env) c
    | Sort _ -> true
    | _ -> sort_of env t = InProp

(*s [add_lambda t n] adds [n] leading lambdas to [t]. *)

let rec add_lambda t = function
  | 0 -> t
  | n -> add_lambda (TFun t) (n-1)

(*s [del_lambda t n] removes the [n] leading lambdas from [t].
  We suppose [t] starts with at least [n] lambdas. *)
let rec del_lambda t = function
  | 0 -> t
  | n -> match t with
      | TFun a -> del_lambda a (n-1)
      | _ -> assert false

(*S Extraction of a term applied to arguments. *)

let rec extract_term env c args =
  if discard env (type_of env c) then
    (* It could simply be TDummy, but we conserve the structure here. *)
    extract_app env TDummy args
  else match kind_of_term c with
    | App (f, a) ->
        extract_term env f (Array.to_list a @ args)
    | Lambda (_, t, d) ->
        let env' = push_rel_assum (Anonymous, t) env in
        extract_app env (TFun (extract_term env' d [])) args
    | LetIn (n, c1, t1, c2) ->
	let env' = push_rel (Anonymous, Some c1, t1) env in
        extract_app env (TLet (extract_term env c1 [], extract_term env' c2 [])) args
    | Const kn ->
        extract_cst_app env kn args
    | Construct cp ->
	extract_cons_app env cp args
    | Rel n ->
	extract_app env (TVar (n-1)) args
    | Case ({ci_ind=ip}, _, c0, br) ->
 	extract_app env (extract_case env (ip, c0, br)) args
    | Fix ((_, i), recd) ->
 	extract_app env (extract_fix env i recd) args
    | CoFix (i, recd) ->
 	extract_app env (extract_fix env i recd) args
    | Cast (c, _, _) -> extract_term env c args
    | Ind _ | Prod _ | Sort _ | Meta _ | Evar _ | Var _ -> assert false

(*s Generic way to deal with an application. *)

and extract_app env head args =
  if args = [] then
    head
  else
    let mlargs = List.map (fun c -> extract_term env c []) args in
    List.fold_left (fun t a -> TApply (t, a)) head mlargs

(*s Extraction of a constant applied to arguments. *)

and extract_cst_app env kn args =
  let _, _, name = repr_con kn in
  let name = string_of_label name in
  let name__extr = name ^ "__extr" in
  let id = make_short_qualid (id_of_string name__extr) in
  let kn__extr =
    try
      TConstant (mkConst (locate_constant id))
    with Not_found ->
      msgnl
        (str
           (Printf.sprintf
              "WARNING: %s does not exist, %s has been replaced by TDummy!"
              name__extr name));
      TDummy
  in
  extract_app env kn__extr args

(*s Extraction of an inductive constructor applied to arguments. *)

and extract_cons_app env ((_, j) as cp) args =
  (* First, we determine the number of arguments expected by the constructor. *)
  let nb_args = mis_constructor_nargs_env env cp in
  (* Then, we build the closure accordingly. *)
  let missing = nb_args - List.length args in
  assert (missing >= 0);
  (* Otherwise, the constructor is applied to too many arguments. *)
  let rec add_argument args = function
    | 0 -> args
    | n -> add_argument (args @ [TVar (n-1)]) (n-1) (* bad complexity *)
  in
  let mlargs = List.map (fun c -> extract_term env c []) args in
  add_lambda (TConstr (j-1, add_argument mlargs missing)) missing

(*S Extraction of a case. *)

and extract_case env ((kn, i) as ip, c, br) =
  (* [br]: bodies of each branch (in functional form) *)
  (* [ni]: number of arguments without parameters in each branch *)
  let ni = mis_constr_nargs_env env ip in
  assert (Array.length ni = Array.length br);
  let br = Array.mapi
    (fun i b ->
       let nb = ni.(i) in
       let branch = extract_term env b [] in
       Patc (nb, del_lambda branch nb)) br in
  TMatch (extract_term env c [], Array.to_list br)

(*s Extraction of a (co)-fixpoint. *)

and extract_fix env i (_, _, ci as recd) =
  (* for now, we don't deal with mutually inductive functions *)
  assert (Array.length ci = 1 && i = 0);
  let env = push_rec_types recd env in
  let ei = Array.map (fun c -> extract_term env c []) ci in
  let body = match ei.(0) with
    | TFun(a) -> a
    | _ -> assert false (* a fixpoint is a function *)
  in TFix body

(*s Extraction of a constant in the global environment. *)

let extract_constant c =
  let env =  Global.env () in
  let cb = Environ.lookup_constant c env in
  let term = mkTerm (match cb.const_body with
    | None -> msgnl (str "Axiom extracted as TDummy!"); TDummy
    | Some body -> extract_term env (force body) [])
  in
  let entry =
    { const_entry_body = term;
      const_entry_type = None;
      const_entry_opaque = false;
      const_entry_boxed = false }
  in
  let _, _, name = repr_con c in
  let new_name = (string_of_label name) ^ "__extr" in
  msgnl (str ("The constant "^new_name^" has been created by extraction."));
  ignore (declare_constant (id_of_string new_name)
            (DefinitionEntry entry, IsDefinition Definition))


let internal_extraction qid =
  Coqlib.check_required_library ["Coq"; "Lists"; "List"];
  Coqlib.check_required_library ["Coq"; "intextr"; "Ml"];
  check_inside_section ();
  check_inside_module ();
  match Nametab.global qid with
    | VarRef _ -> assert false
    | ConstRef c -> extract_constant c
    | _ -> assert false
