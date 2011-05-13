(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(***********************************************************************)
(*                                                                     *)
(*      This module defines proof facilities relevant to the           *)
(*      toplevel. In particular it defines the global proof            *)
(*      environment.                                                   *)
(*                                                                     *)
(***********************************************************************)

open Pp
open Names

(*** Proof Modes ***)

(* Type of proof modes :
    - A function [set] to set it *from standard mode*
    - A function [reset] to reset the *standard mode* from it *)
type proof_mode = {
  name : string ;
  set : unit -> unit ;
  reset : unit -> unit
}

let proof_modes = Hashtbl.create 6
let register_proof_mode ({ name = n } as m) = Hashtbl.add proof_modes n m
(* initial mode: standard mode *)
let standard = { name = "No" ; set = (fun ()->()) ; reset = (fun () -> ()) }
let _ = register_proof_mode standard

(* Default proof mode, to be set at the beginning of proofs. *)
let default_proof_mode = ref standard

let _ =
  Goptions.declare_string_option {Goptions.
    optsync = true ;
    optname = "default proof mode" ;
    optkey = ["Default";"Proof";"Mode"] ;
    optread = begin fun () -> 
                               let { name = name } = !default_proof_mode in name 
                     end;
    optwrite = begin fun n -> 
                                default_proof_mode := Hashtbl.find proof_modes n
                      end
  }

(*** Proof Global Environment ***)

(* local shorthand *)
type nproof = identifier*Proof.proof

(* Extra info on proofs. *)
type lemma_possible_guards = int list list
type proof_info = { 
  strength : Decl_kinds.goal_kind ;
  compute_guard :  lemma_possible_guards; 
  hook :Tacexpr.declaration_hook ;
  mode : proof_mode
}

(* Invariant: a proof is at most in one of current_proof and suspended. And the 
   domain of proof_info is the union of that of current_proof and suspended.*)
(* The head of [!current_proof] is the actual current proof, the other ones are to
    be resumed when the current proof is closed, aborted or suspended. *)
let current_proof = ref ([]:nproof list)
let suspended = ref ([] : nproof list)
let proof_info = ref (Idmap.empty : proof_info Idmap.t)

(* Current proof_mode, for bookkeeping *)
let current_proof_mode = ref !default_proof_mode

(* combinators for proof modes *)
let update_proof_mode () = 
  match !current_proof with
  | (id,_)::_ ->  
      let { mode = m } = Idmap.find id !proof_info in
      !current_proof_mode.reset ();
      current_proof_mode := m;
      !current_proof_mode.set ()
  | _ -> 
      !current_proof_mode.reset (); 
      current_proof_mode := standard

(* combinators for the current_proof and suspended lists *)
let push a l = l := a::!l;
  update_proof_mode ()

exception NoSuchProof
let _ = Errors.register_handler begin function
  | NoSuchProof -> Util.error "No such proof."
  | _ -> raise Errors.Unhandled
end
let rec extract id l = 
  let rec aux = function
    | ((id',_) as np)::l when id_ord id id' = 0 -> (np,l)
    | np::l -> let (np', l) = aux l in (np' , np::l)
    | [] -> raise NoSuchProof
  in
  let (np,l') = aux !l in
  l := l';
  update_proof_mode ();
  np

exception NoCurrentProof
let _ = Errors.register_handler begin function
  | NoCurrentProof -> Util.error "No focused proof (No proof-editing in progress)."
  | _ -> raise Errors.Unhandled
end
let extract_top l =
  match !l with
  | np::l' -> l := l' ; update_proof_mode (); np
  | [] -> raise NoCurrentProof	
let find_top l =
  match !l with
  | np::_ -> np
  | [] -> raise NoCurrentProof

let rotate_top l1 l2 =
  let np = extract_top l1 in
  push np l2

let rotate_find id l1 l2 =
  let np = extract id l1 in
  push np l2
  

(* combinators for the proof_info map *)
let add id info m =
  m := Idmap.add id info !m
let remove id m =
  m := Idmap.remove id !m

(*** Proof Global manipulation ***)

let get_all_proof_names () =
    List.map fst !current_proof @
    List.map fst !suspended

let give_me_the_proof () = 
  snd (find_top current_proof)

let get_current_proof_name () =
  fst (find_top current_proof)

(* spiwack: it might be considered to move error messages away.
    Or else to remove special exceptions from Proof_global.
    Arguments for the former: there is no reason Proof_global is only
    accessed directly through vernacular commands. Error message should be 
   pushed to external layers, and so we should be able to have a finer
   control on error message on complex actions. *)
let msg_proofs use_resume =
  match get_all_proof_names () with
    | [] -> (spc () ++ str"(No proof-editing in progress).")
    | l ->  (str"." ++ fnl () ++ str"Proofs currently edited:" ++ spc () ++
               (Util.prlist_with_sep Util.pr_spc Nameops.pr_id l) ++
	       str"." ++
               (if use_resume then (fnl () ++ str"Use \"Resume\" first.")
              	else (mt ()))
	    )


let there_is_a_proof () = !current_proof <> []
let there_are_suspended_proofs () = !suspended <> []
let there_are_pending_proofs () = 
  there_is_a_proof () || 
  there_are_suspended_proofs ()
let check_no_pending_proof () = 
  if not (there_are_pending_proofs ()) then
    ()
  else begin
    pp_with Format.str_formatter
      (str"Proof editing in progress" ++ (msg_proofs false) ++ fnl() ++
       str"Use \"Abort All\" first or complete proof(s).")   ;
    Util.error (Format.flush_str_formatter ())
  end


let suspend () =
  rotate_top current_proof suspended

let resume_last () =
  rotate_top suspended current_proof

let resume id =
  rotate_find id suspended current_proof

let discard_gen id =
  try 
    ignore (extract id current_proof);
    remove id proof_info
  with NoSuchProof -> ignore (extract id suspended)

let discard (loc,id) = 
  try
    discard_gen id
  with NoSuchProof ->
    Util.user_err_loc
      (loc,"Pfedit.delete_proof",str"No such proof" ++ msg_proofs false)

let discard_current () =
  let (id,_) = extract_top current_proof in
  remove id proof_info
 
let discard_all () =
  current_proof := []; 
  suspended := [];
  proof_info := Idmap.empty

(* [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
(* Core component.
    No undo handling.
    Applies to proof [id], and proof mode [m]. *)
let set_proof_mode m id = 
  let info = Idmap.find id !proof_info in
  let info = { info with mode = m } in
  proof_info := Idmap.add id info !proof_info;
  update_proof_mode ()
(* Complete function.
    Handles undo.
    Applies to current proof, and proof mode name [mn]. *)
let set_proof_mode mn =
  let m = Hashtbl.find proof_modes mn in
  let id = get_current_proof_name () in
  let pr = give_me_the_proof () in
  Proof.add_undo begin let curr = !current_proof_mode in fun () ->
    set_proof_mode curr id ; update_proof_mode ()
  end pr ;
  set_proof_mode m id

(* [start_proof s str env t hook tac] starts a proof of name [s] and
    conclusion [t]; [hook] is optionally a function to be applied at
    proof end (e.g. to declare the built constructions as a coercion
    or a setoid morphism); init_tac is possibly a tactic to
    systematically apply at initialization time (e.g. to start the
    proof of mutually dependent theorems).
    It raises exception [ProofInProgress] if there is a proof being
    currently edited. *)
let start_proof  id str goals ?(compute_guard=[]) hook =
  (* arnaud: ajouter une vérification pour la présence de id dans le proof_global *)
  let p = Proof.start goals in
  add id { strength=str ; 
	        compute_guard=compute_guard ; 
		hook=hook ;
	        mode = ! default_proof_mode } proof_info ;
  push (id,p) current_proof

(* arnaud: à enlever *)
let run_tactic tac = 
  let p = give_me_the_proof () in
  let env = Global.env () in
  Proof.run_tactic env tac p

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac =
  let p = give_me_the_proof () in
  Proof.set_endline_tactic tac p

let with_end_tac tac =
  let p = give_me_the_proof () in
  Proof.with_end_tac p tac

let close_proof () =
  (* spiwack: for now close_proof doesn't actually discard the proof, it is done
      by [Command.save]. *)
  try 
    let id = get_current_proof_name () in
    let p = give_me_the_proof () in
    let proofs_and_types = Proof.return p in
    let entries = List.map
      (fun (c,t) -> { Entries.const_entry_body = c ;
                      const_entry_type  = Some t;
		      const_entry_opaque = true })
      proofs_and_types
    in
    let { compute_guard=cg ; strength=str ; hook=hook } =
      Idmap.find id !proof_info
    in
    (id, (entries,cg,str,hook))
  with 
    |  Proof.UnfinishedProof ->
	 Util.error "Attempt to save an incomplete proof"
    | Proof.HasUnresolvedEvar ->
	Util.error "Attempt to save a proof with existential variables still non-instantiated"


(**********************************************************)
(*                                                                                                  *)
(*                              Utility functions                                          *)
(*                                                                                                  *)
(**********************************************************)

let maximal_unfocus k p =
  begin try while Proof.no_focused_goal p do
    Proof.unfocus k p
  done
  with Proof.FullyUnfocused -> ()
  end


(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

module Bullet = struct

  open Store.Field


  type t = 
    | Dash
    | Star
    | Plus

  type behavior = {
    name : string;
    put : Proof.proof -> t -> unit
  }

  let behaviors = Hashtbl.create 4
  let register_behavior b = Hashtbl.add behaviors b.name b

  (*** initial modes ***)
  let none = {
    name = "None";
    put = fun _ _ -> ()
  }
  let _ = register_behavior none

  module Strict = struct
    (* spiwack: we need only one focus kind as we keep a stack of (distinct!) bullets *)
    let bullet_kind = Proof.new_focus_kind () 
    let bullet_cond = Proof.done_cond bullet_kind
    let (get_bullets,set_bullets) =
      let bullets = Store.field () in
      begin fun pr -> Option.default [] (bullets.get (Proof.get_proof_info pr)) end ,
      begin fun bs pr -> Proof.set_proof_info (bullets.set bs (Proof.get_proof_info pr)) pr end

    let has_bullet bul pr =
      let rec has_bullet = function
	| b'::_ when bul=b' -> true
	| _::l -> has_bullet l
	| [] -> false
      in
      has_bullet (get_bullets pr)

    (* precondition: the stack is not empty *)
    let pop pr =
      match get_bullets pr with
      | b::stk -> 
	Proof.unfocus bullet_kind pr ;
	set_bullets stk pr ;
	b
      | [] -> Util.anomaly "Tried to pop bullet from an empty stack"

    let push b pr =
      Proof.focus bullet_cond () 1 pr ;
      set_bullets (b::get_bullets pr) pr

    let put p bul =
      if has_bullet bul p then
	begin 
	  while bul <> pop p do () done;
	  push bul p
	end
      else 
	push bul p

    let strict = {
      name = "Strict Subproofs";
      put = put
    }
    let _ = register_behavior strict
  end

  (* Current bullet behavior, controled by the option *)
  let current_behavior = ref Strict.strict
    
  let _ =
    Goptions.declare_string_option {Goptions.
      optsync = true;
      optname = "bullet behavior";
      optkey = ["Bullet";"Behavior"];
      optread = begin fun () ->
	(!current_behavior).name
      end;
      optwrite = begin fun n ->
	current_behavior := Hashtbl.find behaviors n
      end
    }

  let put p b =
    (!current_behavior).put p b
end


module V82 = struct
  let get_current_initial_conclusions () =
    let p = give_me_the_proof () in
    let id = get_current_proof_name () in
    let { strength=str ; hook=hook } = 
      Idmap.find id !proof_info
    in
    (id,(Proof.V82.get_initial_conclusions p, str, hook))
end

