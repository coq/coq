(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*i $Id$ i*)

open Term
open Hipattern
open Names
open Libnames
open Pp
open Proof_type
open Tacticals
open Tacinterp
open Tactics
open Util

let assoc_var s ist =
  match List.assoc (Names.id_of_string s) ist.lfun with
    | VConstr c -> c
    | _ -> failwith "tauto: anomaly"

(** Parametrization of tauto *)

(* Whether conjunction and disjunction are restricted to binary connectives *)
(* (this is the compatibility mode) *)
let binary_mode = true

(* Whether conjunction and disjunction are restricted to the connectives *)
(* having the structure of "and" and "or" (up to the choice of sorts) in *)
(* contravariant position in an hypothesis (this is the compatibility mode) *)
let strict_in_contravariant_hyp = true

(* Whether conjunction and disjunction are restricted to the connectives *)
(* having the structure of "and" and "or" (up to the choice of sorts) in *)
(* an hypothesis and in the conclusion *)
let strict_in_hyp_and_ccl = false

(* Whether unit type includes equality types *)
let strict_unit = false

(* Whether inner iff are unfolded *)
let iff_unfolding = ref false

open Goptions
let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "unfolding of iff and not in intuition";
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
let is_unit_or_eq ist =
  let test = if strict_unit then is_unit_type else is_unit_or_eq_type in
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

let is_binary t =
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

let is_conj ist =
  let ind = assoc_var "X1" ist in
    if (not binary_mode || is_binary ind) (* && not (is_record ind) *)
      && is_conjunction ~strict:strict_in_hyp_and_ccl ind
    then
      <:tactic<idtac>>
    else
      <:tactic<fail>>

let flatten_contravariant_conj ist =
  let typ = assoc_var "X1" ist in
  let c = assoc_var "X2" ist in
  match match_with_conjunction ~strict:strict_in_contravariant_hyp typ with
  | Some (_,args) ->
      let i = List.length args in
      if not binary_mode || i = 2 then 
	let newtyp = valueIn (VConstr (List.fold_right mkArrow args c)) in
	let intros =
	  iter_tac (List.map (fun _ -> <:tactic< intro >>) args) 
	  <:tactic< idtac >> in
	<:tactic<
          let newtyp := $newtyp in
	  assert newtyp by ($intros; apply id; split; assumption);
	  clear id
	>>
      else
	<:tactic<fail>>
  | _ ->
      <:tactic<fail>>

(** Dealing with disjunction *)

let is_disj ist =
  let t = assoc_var "X1" ist in
  if (not binary_mode || is_binary t) &&
    is_disjunction ~strict:strict_in_hyp_and_ccl t
  then
    <:tactic<idtac>>
  else
    <:tactic<fail>>

let flatten_contravariant_disj ist =
  let typ = assoc_var "X1" ist in
  let c = assoc_var "X2" ist in
  match match_with_disjunction ~strict:strict_in_contravariant_hyp typ with
  | Some (_,args) ->
      let i = List.length args in
      if not binary_mode || i = 2 then 
	iter_tac (list_map_i (fun i arg ->
	  let typ = valueIn (VConstr (mkArrow arg c)) in
	  <:tactic< 
            let typ := $typ in
	    assert typ by (intro; apply id; constructor $i; assumption)
	  >>) 1 args) <:tactic< clear id >>
      else
	<:tactic<fail>>
  | _ ->
      <:tactic<fail>>


(** Main tactic *)

let not_dep_intros ist =
  <:tactic<
  repeat match goal with
  | |- (?X1 -> ?X2) => intro
  | |- (Coq.Init.Logic.not _)   => unfold Coq.Init.Logic.not at 1
  | H:(Coq.Init.Logic.not _)|-_    => unfold Coq.Init.Logic.not at 1 in H
  | H:(Coq.Init.Logic.not _)->_|-_    => unfold Coq.Init.Logic.not at 1 in H
  end >>
				      
let axioms ist =
  let t_is_unit_or_eq = tacticIn is_unit_or_eq
  and t_is_empty = tacticIn is_empty in
    <:tactic<
    match reverse goal with
      | |- ?X1 => $t_is_unit_or_eq; constructor 1
      | _:?X1 |- _ => $t_is_empty; elimtype X1; assumption
      | _:?X1 |- ?X1 => assumption
    end >>


let simplif ist =
  let t_is_unit_or_eq = tacticIn is_unit_or_eq
  and t_is_conj = tacticIn is_conj
  and t_flatten_contravariant_conj = tacticIn flatten_contravariant_conj
  and t_flatten_contravariant_disj = tacticIn flatten_contravariant_disj
  and t_is_disj = tacticIn is_disj
  and t_not_dep_intros = tacticIn not_dep_intros in
  <:tactic<
    $t_not_dep_intros;
    repeat
       (match reverse goal with
        | id: ?X1 |- _ => $t_is_conj; elim id; do 2 intro; clear id
        | id: (Coq.Init.Logic.iff _ _) |- _ => elim id; do 2 intro; clear id
        | id: (Coq.Init.Logic.not _) |- _ => red in id
        | id: ?X1 |- _ => $t_is_disj; elim id; intro; clear id
        | id0: ?X1 -> ?X2, id1: ?X1|- _ =>
	    (* generalize (id0 id1); intro; clear id0 does not work
	       (see Marco Maggiesi's bug PR#301)
	    so we instead use Assert and exact. *)
	    assert X2; [exact (id0 id1) | clear id0]
        | id: ?X1 -> ?X2|- _ =>
          $t_is_unit_or_eq; cut X2;
	    [ intro; clear id
	    | (* id : ?X1 -> ?X2 |- ?X2 *)
	      cut X1; [exact id| constructor 1; fail]
	    ]
        | id: ?X1 -> ?X2|- _ =>
          $t_flatten_contravariant_conj
	  (* moved from "id:(?A/\?B)->?X2|-" to "?A->?B->?X2|-" *)
        | id: (Coq.Init.Logic.iff ?X1 ?X2) -> ?X3|- _ =>
          assert ((X1 -> X2) -> (X2 -> X1) -> X3)
	    by (do 2 intro; apply id; split; assumption);
            clear id
        | id: ?X1 -> ?X2|- _ =>
          $t_flatten_contravariant_disj
	  (* moved from "id:(?A\/?B)->?X2|-" to "?A->?X2,?B->?X2|-" *)
        | |- ?X1 => $t_is_conj; split
        | |- (Coq.Init.Logic.iff _ _) => split
        | |- (Coq.Init.Logic.not _) => red
        end;
        $t_not_dep_intros) >>

let rec tauto_intuit t_reduce solver ist =
  let t_axioms = tacticIn axioms
  and t_simplif = tacticIn simplif
  and t_is_disj = tacticIn is_disj
  and t_tauto_intuit = tacticIn (tauto_intuit t_reduce solver) in
  let t_solver = globTacticIn (fun _ist -> solver) in
  <:tactic<
   ($t_simplif;$t_axioms
   || match reverse goal with
      | id:(?X1 -> ?X2)-> ?X3|- _ =>
	  cut X3;
	    [ intro; clear id; $t_tauto_intuit 
	    | cut (X1 -> X2);
		[ exact id
		| generalize (fun y:X2 => id (fun x:X1 => y)); intro; clear id;
		  solve [ $t_tauto_intuit ]]]
      | |- ?X1 =>
          $t_is_disj; solve [left;$t_tauto_intuit | right;$t_tauto_intuit]
      end
    ||
    (* NB: [|- _ -> _] matches any product *)
    match goal with | |- _ -> _ => intro; $t_tauto_intuit
    |  |- _  => $t_reduce;$t_solver
    end
    ||
    $t_solver
   ) >>

let reduction_not _ist =
  if !iff_unfolding then
    <:tactic< unfold Coq.Init.Logic.not, Coq.Init.Logic.iff in * >>
  else
    <:tactic< unfold Coq.Init.Logic.not in * >>

let t_reduction_not = tacticIn reduction_not

let intuition_gen tac =
  interp (tacticIn (tauto_intuit t_reduction_not tac))

let simplif_gen = interp (tacticIn simplif)

let tauto_intuitionistic g =
  try intuition_gen <:tactic<fail>> g
  with
    Refiner.FailError _ | UserError _ ->
      errorlabstrm "tauto" (str "tauto failed.")

let coq_nnpp_path =
  let dir = List.map id_of_string ["Classical_Prop";"Logic";"Coq"] in
  Libnames.make_path (make_dirpath dir) (id_of_string "NNPP")

let tauto_classical nnpp g =
  try tclTHEN (apply nnpp) tauto_intuitionistic g
  with UserError _ -> errorlabstrm "tauto" (str "Classical tauto failed.")

let tauto g =
  try 
    let nnpp = constr_of_global (Nametab.global_of_path coq_nnpp_path) in
    (* try intuitionistic version first to avoid an axiom if possible *)
    tclORELSE tauto_intuitionistic (tauto_classical nnpp) g
  with Not_found ->
    tauto_intuitionistic g


let default_intuition_tac = <:tactic< auto with * >>

TACTIC EXTEND tauto
| [ "tauto" ] -> [ tauto ]
END

TACTIC EXTEND intuition
| [ "intuition" ] -> [ intuition_gen default_intuition_tac ]
| [ "intuition" tactic(t) ] -> [ intuition_gen (fst t) ]
END
