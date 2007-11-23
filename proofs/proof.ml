(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* This module implements the actual proof datatype. It enforces strong
   invariants, and it is the only module that should access the module
   Subproof.
   Actually from outside the proofs/ subdirectory, this is the only module
   that should be used directly. *)

(* arnaud: rajouter le blabla sur la  théorie du module ici *)

open Term

type ('a,+'b) subproof = ('a,'b) Subproof.subproof 
     (* rather than opening Subproof *)

open Transactional_stack



(* We define a type of stored mutations of subproof pointers. 
   We actually define it as a pair of a [pointer] and a [subproof].
   The intended use of a stored mutation is to set the [pointer]
   content as being the [subproof].
   Stored mutations are used in the undo mechanism. The undo stacks 
   stores basically series of such mutations to execute in case an
   undo is required. *)

(** Encoding the type
     exists 'b 'c.{ sp : ('b,'c) subproof ; pt : ('b,'c) Subproof.pointer }
   trick from Benjamin Pierce and Daniel Bünzli 
   
(cf: http://caml.inria.fr/pub/ml-archives/caml-list/2004/01/52732867110697f55650778d883ae5e9.en.html ) 

**)
type ('b,+'c) mutation = { sp : ('b,'c) subproof ; pt : ('b,'c) Subproof.pointer }
type 't mutation_scope = { bind_mutation:'b 'c.('b,'c) mutation -> 't }
type packed_mutation = { open_mutation : 't. 't mutation_scope -> 't }


(* makes a packed_mutation out of mutation *)
let pack_mutation mutn =
  { open_mutation = fun scope -> scope.bind_mutation mutn }

(* uses a scoped function on a packed mutation *)
let unpack_mutation pck scp =
  pck.open_mutation scp

(* execute a packed mutation with its expected behavior: sets  the content
   of the pointer [pt] as [sp] *)
let do_packed_mutation =
  let scoped_mutate = 
    { bind_mutation = fun mtn -> Subproof.mutate mtn.pt mtn.sp }
  in
  fun pck ->
    unpack_mutation pck scoped_mutate





type 'a proof = { (* The root of the proof *)
		  mutable root : ('a,[ `Subproof | `Resolved ]) Subproof.pointer;
		  (* The list of focusings to be able to backtrack.
		     The current focusing is the head of the list.
		     The empty list means that the root is focused *)
                  mutable focus : (constr,[ `Subproof | `Resolved | `Open ]) 
		                                            Subproof.pointer list;
		  (* The undo stack *)
		  undo_stack : 'a undo_action transactional_stack;
		  (* The dependent goal heap *)
		  mutable dependent_goals : 
		          ((constr,[ `Subproof | `Resolved | `Open ]) Subproof.pointer, Evd.evar) Biassoc.biassoc;
                  mutable eenv : Evd.evar_defs
		}
and 'a undo_action = 
    | MutateBack of packed_mutation
    | Unfocus of 'a proof
    | Focus of 'a proof * (constr,[`Subproof|`Resolved|`Open]) Subproof.pointer



(* Gives the type of a proof action *)
(* arnaud: compléter les commentaires *)
type 'a _action = 'a proof -> 'a undo_action transaction -> unit
type 'a action = 'a _action Sequence.sequence

let primitive = Sequence.element
let compose = Sequence.append



(*** The following functions give more abstract methods to access
     the data of a proof ***)

(* This function gives the position of the focus if the proof is
   focused, [None] otherwise *)
let get_focus pr =
  match pr.focus with
  | [] -> None
  | pos::_ -> Some pos

(* The following function gives the content of the root *)
let get_root pr =
  pr.root



(*** The following functions are somewhat unsafe, they are meant to 
     be used by other functions later. They shouldn't be declared in
     the .mli ***)


(* This function performs a focusing on a given position
   with no safety check nor caring of undos *)
let unsafe_focus pr pos =
  pr.focus <- pos::pr.focus

(* This function unfocuses the proof [pr] with no safety
   check nor caring of undos *)
let unsafe_unfocus pr =
  pr.focus <- List.tl pr.focus





(*** The following functions define the basic safety mechanism of the
     proof system, they may be unsafe if not used carefully. There is
     currently no reason to export them in the .mli ***)


(* This function interpetes (and execute) a single [undo_action] *)
let execute_undo_action = function
  | MutateBack pck -> do_packed_mutation pck
  | Unfocus pr -> unsafe_unfocus pr
  | Focus(pr, pt) -> unsafe_focus pr pt
				

(* This function interpetes a list of undo action, starting with
   the one on the head. *)
let execute_undo_sequence l =
  List.iter execute_undo_action l

(* This function gives the rollback procedure on unsuccessful commands .
   tr is the current transaction. *)
let rollback tr =
  Transactional_stack.rollback execute_undo_sequence tr





(* exception which represent a failure in a command *)
exception Failure of Pp.std_ppcmds

(* function to raise a failure less verbosely *)
let fail msg = raise (Failure msg)



(*** The functions that come below are meant to be used as 
     atomic actions, they raise [Failure] when they fail
     and they push an [undo_action] to revert themselves.
     They come in two flavors, [_name] is meant to be used in
     complex primitive actions, [name] is the exported version, 
     of type ['a action] ***)

(* This action does nothing, it may be used to end any continuation based action, like tacticals *)
let null_action = primitive ( fun _ _ -> () )

(* This function performs sound mutation at a given position.
   That is a mutation which stores an undo_action into the 
   transaction [tr] *)

let _mutate pt sp tr =
  push (MutateBack (pack_mutation {sp=sp;pt=pt})) tr;
  Subproof.mutate pt sp

let mutate =
  primitive _mutate


(* This function focuses the proof [pr] at position [pt] and 
   pushes an [undo_action] into the transaction [tr]. *)
let _focus pt pr tr =
  push (Unfocus pr) tr;
  unsafe_focus pr pt

let focus =
  primitive _focus

(* This function unfocuses the proof [pr], fails if 
   [pr] is not focused (i.e. if it shows its root). It
   pushed an [undo_action] into the transaction [tr] *)
let _unfocus pr tr =
  match pr.focus with
  | [] -> fail (Pp.str "This proof is not focused")
  | pt::_ -> push (Focus (pr,pt)) tr; unsafe_unfocus pr

let unfocus =
  primitive _unfocus

(*** The following function are complex or composed actions ***)

(* arnaud: repasser sur les commentaires *)
(* This pair of functions tries percolate the resolved subgoal as much
   as possible. It unfocuses the proof as much as needed so that it
   is not focused on a resolved proof *)
(* only [resolve] is meant to be used later on *)
(* [deep_resolve] takes care of the non-root cases *)
(* arnaud: rajouter les instanciations de métavariables *)
let resolve =
  (* This function unfocuses a proof until it is totally unfocused or
     is focused on a non-resolved subproof *)
  let rec unfocus_until_sound pr tr = 
    match get_focus pr with
    | None -> ()
    | Some pt -> if Subproof.is_resolved (Subproof.get pt) then
	           (_unfocus pr tr;
                    unfocus_until_sound pr tr)
                 else 
                   ()  
  in
  let resolve_iterator_fun tr pt =
    try 
      let res = Subproof.resolve (Subproof.get pt) in
      _mutate pt res tr
    with Subproof.Unresolved ->
      ()
  in
  let resolve_iterator tr = 
    { Subproof.iterator = fun pt -> resolve_iterator_fun tr pt }
  in
  primitive (fun pr tr ->
              Subproof.percolate (resolve_iterator tr) (get_root pr);
              unfocus_until_sound pr tr)

(*** The following function takes an action and makes it into 
     a command ***)

let do_action actions pr = 
  let tr = start_transaction pr.undo_stack in
  try 
    let actions = compose actions resolve in (* arnaud:really need a resolve here ? *)
    Sequence.iter (fun action -> action pr tr) actions;
    commit tr
  with e -> (* arnaud: traitement particulier de Failure ? *)
    rollback tr;
    raise e
  

(*** The functions below are actually commands that can be used,
     They cannot be used as a part of a compound transformation ***)

(* This function gives the semantics of the "undo" command.
   [pr] is the current proof *)
let undo pr = 
  Transactional_stack.pop execute_undo_sequence (pr.undo_stack)


(*** The following functions define the tactic machinery. They 
     transform a tactical expression into a sequence of actions. ***)

type 'a tactical = 'a action -> 'a action

(* 'a tactical -> 'a action *)
let close_tactical t = t null_action
  

(* apply_one *)
(* apply_all *)
(* apply_array *)
(* apply_extend *)
