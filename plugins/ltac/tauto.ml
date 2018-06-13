(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open EConstr
open Hipattern
open Names
open Geninterp
open Ltac_plugin
open Tacexpr
open Tacinterp
open Util
open Tacticals.New
open Proofview.Notations

let tauto_plugin = "tauto_plugin"
let () = Mltop.add_known_module tauto_plugin

let assoc_var s ist =
  let v = Id.Map.find (Names.Id.of_string s) ist.lfun in
  match Value.to_constr v with
    | Some c -> c
    | None -> failwith "tauto: anomaly"

(** Parametrization of tauto *)

type tauto_flags = {

(* Whether conjunction and disjunction are restricted to binary connectives *)
  binary_mode : bool;

(* Whether compatibility for buggy detection of binary connective is on *)
  binary_mode_bugged_detection : bool;

(* Whether conjunction and disjunction are restricted to the connectives *)
(* having the structure of "and" and "or" (up to the choice of sorts) in *)
(* contravariant position in an hypothesis *)
  strict_in_contravariant_hyp : bool;

(* Whether conjunction and disjunction are restricted to the connectives *)
(* having the structure of "and" and "or" (up to the choice of sorts) in *)
(* an hypothesis and in the conclusion *)
  strict_in_hyp_and_ccl : bool;

(* Whether unit type includes equality types *)
  strict_unit : bool;
}

let tag_tauto_flags : tauto_flags Val.typ = Val.create "tauto_flags"

let assoc_flags ist : tauto_flags =
  let Val.Dyn (tag, v) = Id.Map.find (Names.Id.of_string "tauto_flags") ist.lfun in
  match Val.eq tag tag_tauto_flags with
  | None -> assert false
  | Some Refl -> v

(* Whether inner not are unfolded *)
let negation_unfolding = ref true

open Goptions
let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "unfolding of not in intuition";
      optkey   = ["Intuition";"Negation";"Unfolding"];
      optread  = (fun () -> !negation_unfolding);
      optwrite = (:=) negation_unfolding }

(** Base tactics *)

let idtac = Proofview.tclUNIT ()
let fail = Proofview.tclINDEPENDENT (tclFAIL 0 (Pp.mt ()))

let intro = Tactics.intro

let assert_ ?by c =
  let tac = match by with
  | None -> None
  | Some tac -> Some (Some tac)
  in
  Proofview.tclINDEPENDENT (Tactics.forward true tac None c)

let apply c = Tactics.apply c

let clear id = Tactics.clear [id]

let assumption = Tactics.assumption

let split = Tactics.split_with_bindings false [Tactypes.NoBindings]

(** Test *)

let is_empty _ ist =
  Proofview.tclEVARMAP >>= fun sigma ->
  if is_empty_type sigma (assoc_var "X1" ist) then idtac else fail

(* Strictly speaking, this exceeds the propositional fragment as it
   matches also equality types (and solves them if a reflexivity) *)
let is_unit_or_eq _ ist =
  Proofview.tclEVARMAP >>= fun sigma ->
  let flags = assoc_flags ist in
  let test = if flags.strict_unit then is_unit_type else is_unit_or_eq_type in
  if test sigma (assoc_var "X1" ist) then idtac else fail

let bugged_is_binary sigma t =
  isApp sigma t &&
  let (hdapp,args) = decompose_app sigma t in
    match EConstr.kind sigma hdapp with
    | Ind (ind,u)  ->
        let (mib,mip) = Global.lookup_inductive ind in
         Int.equal mib.Declarations.mind_nparams 2
    | _ -> false

(** Dealing with conjunction *)

let is_conj _ ist =
  Proofview.tclEVARMAP >>= fun sigma ->
  let flags = assoc_flags ist in
  let ind = assoc_var "X1" ist in
    if (not flags.binary_mode_bugged_detection || bugged_is_binary sigma ind) &&
       is_conjunction sigma
         ~strict:flags.strict_in_hyp_and_ccl
         ~onlybinary:flags.binary_mode ind
    then idtac
    else fail

let flatten_contravariant_conj _ ist =
  Proofview.tclEVARMAP >>= fun sigma ->
  let flags = assoc_flags ist in
  let typ = assoc_var "X1" ist in
  let c = assoc_var "X2" ist in
  let hyp = assoc_var "id" ist in
  match match_with_conjunction sigma
          ~strict:flags.strict_in_contravariant_hyp
          ~onlybinary:flags.binary_mode typ
  with
  | Some (_,args) ->
    let newtyp = List.fold_right mkArrow args c in
    let intros = tclMAP (fun _ -> intro) args in
    let by = tclTHENLIST [intros; apply hyp; split; assumption] in
    tclTHENLIST [assert_ ~by newtyp; clear (destVar sigma hyp)]
  | _ -> fail

(** Dealing with disjunction *)

let is_disj _ ist =
  Proofview.tclEVARMAP >>= fun sigma ->
  let flags = assoc_flags ist in
  let t = assoc_var "X1" ist in
  if (not flags.binary_mode_bugged_detection || bugged_is_binary sigma t) &&
     is_disjunction sigma
       ~strict:flags.strict_in_hyp_and_ccl
       ~onlybinary:flags.binary_mode t
  then idtac
  else fail

let flatten_contravariant_disj _ ist =
  Proofview.tclEVARMAP >>= fun sigma ->
  let flags = assoc_flags ist in
  let typ = assoc_var "X1" ist in
  let c = assoc_var "X2" ist in
  let hyp = assoc_var "id" ist in
  match match_with_disjunction sigma
          ~strict:flags.strict_in_contravariant_hyp
          ~onlybinary:flags.binary_mode
          typ with
  | Some (_,args) ->
      let map i arg =
        let typ = mkArrow arg c in
        let ci = Tactics.constructor_tac false None (succ i) Tactypes.NoBindings in
        let by = tclTHENLIST [intro; apply hyp; ci; assumption] in
        assert_ ~by typ
      in
      let tacs = List.mapi map args in
      let tac0 = clear (destVar sigma hyp) in
      tclTHEN (tclTHENLIST tacs) tac0
  | _ -> fail

let make_unfold name =
  let dir = DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"]) in
  let const = Constant.make2 (ModPath.MPfile dir) (Label.make name) in
  Locus.(AllOccurrences, ArgArg (EvalConstRef const, None))

let u_not = make_unfold "not"

let reduction_not_iff _ ist =
  let make_reduce c = TacAtom (Loc.tag @@ TacReduce (Genredexpr.Unfold c, Locusops.allHypsAndConcl)) in
  let tac = match !negation_unfolding with
    | true -> make_reduce [u_not]
    | false -> TacId []
  in
  eval_tactic_ist ist tac

let coq_nnpp_path =
  let dir = List.map Id.of_string ["Classical_Prop";"Logic";"Coq"] in
  Libnames.make_path (DirPath.make dir) (Id.of_string "NNPP")

let apply_nnpp _ ist =
  Proofview.tclBIND
    (Proofview.tclUNIT ())
    begin fun () -> try
      Tacticals.New.pf_constr_of_global (Nametab.global_of_path coq_nnpp_path) >>= apply
    with Not_found -> tclFAIL 0 (Pp.mt ())
    end

(* This is the uniform mode dealing with ->, not, iff and types isomorphic to
   /\ and *, \/ and +, False and Empty_set, True and unit, _and_ eq-like types.
   For the moment not and iff are still always unfolded. *)
let tauto_uniform_unit_flags = {
  binary_mode = true;
  binary_mode_bugged_detection = false;
  strict_in_contravariant_hyp = true;
  strict_in_hyp_and_ccl = true;
  strict_unit = false
}

(* This is the compatibility mode (not used) *)
let _tauto_legacy_flags = {
  binary_mode = true;
  binary_mode_bugged_detection = true;
  strict_in_contravariant_hyp = true;
  strict_in_hyp_and_ccl = false;
  strict_unit = false
}

(* This is the improved mode *)
let tauto_power_flags = {
  binary_mode = false; (* support n-ary connectives *)
  binary_mode_bugged_detection = false;
  strict_in_contravariant_hyp = false; (* supports non-regular connectives *)
  strict_in_hyp_and_ccl = false;
  strict_unit = false
}

let with_flags flags _ ist =
  let f = CAst.make @@ Id.of_string "f" in
  let x = CAst.make @@ Id.of_string "x" in
  let arg = Val.Dyn (tag_tauto_flags, flags) in
  let ist = { ist with lfun = Id.Map.add x.CAst.v arg ist.lfun } in
  eval_tactic_ist ist (TacArg (Loc.tag @@ TacCall (Loc.tag (Locus.ArgVar f, [Reference (Locus.ArgVar x)]))))

let register_tauto_tactic tac name0 args =
  let ids = List.map (fun id -> Id.of_string id) args in
  let ids = List.map (fun id -> Name id) ids in
  let name = { mltac_plugin = tauto_plugin; mltac_tactic = name0; } in
  let entry = { mltac_name = name; mltac_index = 0 } in
  let () = Tacenv.register_ml_tactic name [| tac |] in
  let tac = TacFun (ids, TacML (Loc.tag (entry, []))) in
  let obj () = Tacenv.register_ltac true true (Id.of_string name0) tac in
  Mltop.declare_cache_obj obj tauto_plugin

let () = register_tauto_tactic is_empty "is_empty" ["tauto_flags"; "X1"]
let () = register_tauto_tactic is_unit_or_eq "is_unit_or_eq" ["tauto_flags"; "X1"]
let () = register_tauto_tactic is_disj "is_disj" ["tauto_flags"; "X1"]
let () = register_tauto_tactic is_conj "is_conj" ["tauto_flags"; "X1"]
let () = register_tauto_tactic flatten_contravariant_disj "flatten_contravariant_disj" ["tauto_flags"; "X1"; "X2"; "id"]
let () = register_tauto_tactic flatten_contravariant_conj "flatten_contravariant_conj" ["tauto_flags"; "X1"; "X2"; "id"]
let () = register_tauto_tactic apply_nnpp "apply_nnpp" []
let () = register_tauto_tactic reduction_not_iff "reduction_not_iff" []
let () = register_tauto_tactic (with_flags tauto_uniform_unit_flags) "with_uniform_flags" ["f"]
let () = register_tauto_tactic (with_flags tauto_power_flags) "with_power_flags" ["f"]
