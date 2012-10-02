(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Term
open Hipattern
open Names
open Globnames
open Pp
open Tacticals
open Tacinterp
open Tactics
open Errors
open Util

let assoc_var s ist =
  match List.assoc (Names.id_of_string s) ist.lfun with
    | VConstr ([],c) -> c
    | _ -> failwith "tauto: anomaly"

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

(* Whether inner not are unfolded *)
let negation_unfolding = ref true

(* Whether inner iff are unfolded *)
let iff_unfolding = ref false

let unfold_iff () = !iff_unfolding || Flags.version_less_or_equal Flags.V8_2

open Goptions
let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "unfolding of not in intuition";
      optkey   = ["Intuition";"Negation";"Unfolding"];
      optread  = (fun () -> !negation_unfolding);
      optwrite = (:=) negation_unfolding }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "unfolding of iff in intuition";
      optkey   = ["Intuition";"Iff";"Unfolding"];
      optread  = (fun () -> !iff_unfolding);
      optwrite = (:=) iff_unfolding }

(** Test *)

let is_empty ist =
  if is_empty_type (assoc_var "X1" ist) then
    <:tactic<idtac>>
  else
    <:tactic<fail>>

(* Strictly speaking, this exceeds the propositional fragment as it
   matches also equality types (and solves them if a reflexivity) *)
let is_unit_or_eq flags ist =
  let test = if flags.strict_unit then is_unit_type else is_unit_or_eq_type in
  if test (assoc_var "X1" ist) then
    <:tactic<idtac>>
  else
    <:tactic<fail>>

let is_record t =
  let (hdapp,args) = decompose_app t in
    match (kind_of_term hdapp) with
      | Ind ind  ->
          let (mib,mip) = Global.lookup_inductive ind in
	    mib.Declarations.mind_record
      | _ -> false

let bugged_is_binary t =
  isApp t &&
  let (hdapp,args) = decompose_app t in
    match (kind_of_term hdapp) with
    | Ind ind  ->
        let (mib,mip) = Global.lookup_inductive ind in
         mib.Declarations.mind_nparams = 2
    | _ -> false

let iter_tac tacl =
  List.fold_right (fun tac tacs -> <:tactic< $tac; $tacs >>) tacl

(** Dealing with conjunction *)

let is_conj flags ist =
  let ind = assoc_var "X1" ist in
    if (not flags.binary_mode_bugged_detection || bugged_is_binary ind) &&
       is_conjunction
         ~strict:flags.strict_in_hyp_and_ccl
         ~onlybinary:flags.binary_mode ind
    then
      <:tactic<idtac>>
    else
      <:tactic<fail>>

let flatten_contravariant_conj flags ist =
  let typ = assoc_var "X1" ist in
  let c = assoc_var "X2" ist in
  let hyp = assoc_var "id" ist in
  match match_with_conjunction
          ~strict:flags.strict_in_contravariant_hyp
          ~onlybinary:flags.binary_mode typ
  with
  | Some (_,args) ->
      let newtyp = valueIn (VConstr ([],List.fold_right mkArrow args c)) in
      let hyp = valueIn (VConstr ([],hyp)) in
      let intros =
	iter_tac (List.map (fun _ -> <:tactic< intro >>) args)
	<:tactic< idtac >> in
      <:tactic<
        let newtyp := $newtyp in
        let hyp := $hyp in
	assert newtyp by ($intros; apply hyp; split; assumption);
	clear hyp
      >>
  | _ ->
      <:tactic<fail>>

(** Dealing with disjunction *)

let is_disj flags ist =
  let t = assoc_var "X1" ist in
  if (not flags.binary_mode_bugged_detection || bugged_is_binary t) &&
     is_disjunction
       ~strict:flags.strict_in_hyp_and_ccl
       ~onlybinary:flags.binary_mode t
  then
    <:tactic<idtac>>
  else
    <:tactic<fail>>

let flatten_contravariant_disj flags ist =
  let typ = assoc_var "X1" ist in
  let c = assoc_var "X2" ist in
  let hyp = assoc_var "id" ist in
  match match_with_disjunction
          ~strict:flags.strict_in_contravariant_hyp
          ~onlybinary:flags.binary_mode
          typ with
  | Some (_,args) ->
      let hyp = valueIn (VConstr ([],hyp)) in
      iter_tac (List.map_i (fun i arg ->
	let typ = valueIn (VConstr ([],mkArrow arg c)) in
	let i = Tacexpr.Integer i in
	<:tactic<
          let typ := $typ in
          let hyp := $hyp in
	  let i := $i in
	  assert typ by (intro; apply hyp; constructor i; assumption)
	>>) 1 args) <:tactic< let hyp := $hyp in clear hyp >>
  | _ ->
      <:tactic<fail>>


(** Main tactic *)

let not_dep_intros ist =
  <:tactic<
  repeat match goal with
  | |- (forall (_: ?X1), ?X2) => intro
  | |- (Coq.Init.Logic.not _) => unfold Coq.Init.Logic.not at 1; intro
  end >>

let axioms flags ist =
  let t_is_unit_or_eq = tacticIn (is_unit_or_eq flags)
  and t_is_empty = tacticIn is_empty in
    <:tactic<
    match reverse goal with
      | |- ?X1 => $t_is_unit_or_eq; constructor 1
      | _:?X1 |- _ => $t_is_empty; elimtype X1; assumption
      | _:?X1 |- ?X1 => assumption
    end >>


let simplif flags ist =
  let t_is_unit_or_eq = tacticIn (is_unit_or_eq flags)
  and t_is_conj = tacticIn (is_conj flags)
  and t_flatten_contravariant_conj = tacticIn (flatten_contravariant_conj flags)
  and t_flatten_contravariant_disj = tacticIn (flatten_contravariant_disj flags)
  and t_is_disj = tacticIn (is_disj flags)
  and t_not_dep_intros = tacticIn not_dep_intros in
  <:tactic<
    $t_not_dep_intros;
    repeat
       (match reverse goal with
        | id: ?X1 |- _ => $t_is_conj; elim id; do 2 intro; clear id
        | id: (Coq.Init.Logic.iff _ _) |- _ => elim id; do 2 intro; clear id
        | id: (Coq.Init.Logic.not _) |- _ => red in id
        | id: ?X1 |- _ => $t_is_disj; elim id; intro; clear id
        | id0: (forall (_: ?X1), ?X2), id1: ?X1|- _ =>
	    (* generalize (id0 id1); intro; clear id0 does not work
	       (see Marco Maggiesi's bug PR#301)
	    so we instead use Assert and exact. *)
	    assert X2; [exact (id0 id1) | clear id0]
        | id: forall (_ : ?X1), ?X2|- _ =>
          $t_is_unit_or_eq; cut X2;
	    [ intro; clear id
	    | (* id : forall (_: ?X1), ?X2 |- ?X2 *)
	      cut X1; [exact id| constructor 1; fail]
	    ]
        | id: forall (_ : ?X1), ?X2|- _ =>
          $t_flatten_contravariant_conj
	  (* moved from "id:(?A/\?B)->?X2|-" to "?A->?B->?X2|-" *)
        | id: forall (_: Coq.Init.Logic.iff ?X1 ?X2), ?X3|- _ =>
          assert (forall (_: forall _:X1, X2), forall (_: forall _: X2, X1), X3)
	    by (do 2 intro; apply id; split; assumption);
            clear id
        | id: forall (_:?X1), ?X2|- _ =>
          $t_flatten_contravariant_disj
	  (* moved from "id:(?A\/?B)->?X2|-" to "?A->?X2,?B->?X2|-" *)
        | |- ?X1 => $t_is_conj; split
        | |- (Coq.Init.Logic.iff _ _) => split
        | |- (Coq.Init.Logic.not _) => red
        end;
        $t_not_dep_intros) >>

let rec tauto_intuit flags t_reduce solver ist =
  let t_axioms = tacticIn (axioms flags)
  and t_simplif = tacticIn (simplif flags)
  and t_is_disj = tacticIn (is_disj flags)
  and t_tauto_intuit = tacticIn (tauto_intuit flags t_reduce solver) in
  let t_solver = globTacticIn (fun _ist -> solver) in
  <:tactic<
   ($t_simplif;$t_axioms
   || match reverse goal with
      | id:forall(_: forall (_: ?X1), ?X2), ?X3|- _ =>
	  cut X3;
	    [ intro; clear id; $t_tauto_intuit
	    | cut (forall (_: X1), X2);
		[ exact id
		| generalize (fun y:X2 => id (fun x:X1 => y)); intro; clear id;
		  solve [ $t_tauto_intuit ]]]
      | id:forall (_:not ?X1), ?X3|- _ =>
	  cut X3;
	    [ intro; clear id; $t_tauto_intuit
	    | cut (not X1); [ exact id | clear id; intro; solve [$t_tauto_intuit ]]]
      | |- ?X1 =>
          $t_is_disj; solve [left;$t_tauto_intuit | right;$t_tauto_intuit]
      end
    ||
    (* NB: [|- _ -> _] matches any product *)
    match goal with | |- forall (_ : _),  _ => intro; $t_tauto_intuit
    |  |- _  => $t_reduce;$t_solver
    end
    ||
    $t_solver
   ) >>

let reduction_not_iff _ist =
  match !negation_unfolding, unfold_iff () with
    | true, true -> <:tactic< unfold Coq.Init.Logic.not, Coq.Init.Logic.iff in * >>
    | true, false -> <:tactic< unfold Coq.Init.Logic.not in * >>
    | false, true -> <:tactic< unfold Coq.Init.Logic.iff in * >>
    | false, false -> <:tactic< idtac >>

let t_reduction_not_iff = tacticIn reduction_not_iff

let intuition_gen flags tac =
  interp (tacticIn (tauto_intuit flags t_reduction_not_iff tac))

let tauto_intuitionistic flags g =
  try intuition_gen flags <:tactic<fail>> g
  with
    Refiner.FailError _ | UserError _ ->
      errorlabstrm "tauto" (str "tauto failed.")

let coq_nnpp_path =
  let dir = List.map id_of_string ["Classical_Prop";"Logic";"Coq"] in
  Libnames.make_path (make_dirpath dir) (id_of_string "NNPP")

let tauto_classical flags nnpp g =
  try tclTHEN (apply nnpp) (tauto_intuitionistic flags) g
  with UserError _ -> errorlabstrm "tauto" (str "Classical tauto failed.")

let tauto_gen flags g =
  try
    let nnpp = constr_of_global (Nametab.global_of_path coq_nnpp_path) in
    (* try intuitionistic version first to avoid an axiom if possible *)
    tclORELSE (tauto_intuitionistic flags) (tauto_classical flags nnpp) g
  with Not_found ->
    tauto_intuitionistic flags g

let default_intuition_tac = <:tactic< auto with * >>

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
let tauto_legacy_flags = {
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

let tauto = tauto_gen tauto_uniform_unit_flags
let dtauto = tauto_gen tauto_power_flags

TACTIC EXTEND tauto
| [ "tauto" ] -> [ tauto ]
END

TACTIC EXTEND dtauto
| [ "dtauto" ] -> [ dtauto ]
END

TACTIC EXTEND intuition
| [ "intuition" ] -> [ intuition_gen tauto_uniform_unit_flags default_intuition_tac ]
| [ "intuition" tactic(t) ] -> [ intuition_gen tauto_uniform_unit_flags t ]
END

TACTIC EXTEND dintuition
| [ "dintuition" ] -> [ intuition_gen tauto_power_flags default_intuition_tac ]
| [ "dintuition" tactic(t) ] -> [ intuition_gen tauto_power_flags t ]
END
