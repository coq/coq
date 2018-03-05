(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file defines the datatypes used as internal states by the
    tactic monad, and specialises the [Logic_monad] to these type. *)

(** {6 Trees/forest for traces} *)

module Trace = struct

  (** The intent is that an ['a forest] is a list of messages of type
      ['a]. But messages can stand for a list of more precise
      messages, hence the structure is organised as a tree. *)
  type 'a forest = 'a tree list
  and  'a tree   = Seq of 'a * 'a forest

  (** To build a trace incrementally, we use an intermediary data
      structure on which we can define an S-expression like language
      (like a simplified xml except the closing tags do not carry a
      name). Note that nodes are built from right to left in ['a
      incr], the result is mirrored when returning so that in the
      exposed interface, the forest is read from left to right.

      Concretely, we want to add a new tree to a forest: and we are
      building it by adding new trees to the left of its left-most
      subtrees which is built the same way. *)
  type 'a incr = { head:'a forest ; opened: 'a tree list }

  (** S-expression like language as ['a incr] transformers. It is the
      responsibility of the library builder not to use [close] when no
      tag is open. *)
  let empty_incr = { head=[] ; opened=[] }
  let opn a { head ; opened } = { head ; opened = Seq(a,[])::opened }
  let close { head ; opened } =
    match opened with
    | [a] -> { head = a::head ; opened=[] }
    | a::Seq(b,f)::opened -> { head ; opened=Seq(b,a::f)::opened }
    | [] -> assert false
  let leaf a s = close (opn a s)

  (** Returning a forest. It is the responsibility of the library
      builder to close all the tags. *)
  (* spiwack: I may want to close the tags instead, to deal with
     interruptions. *)
  let rec mirror f = List.rev_map mirror_tree f
  and mirror_tree (Seq(a,f)) = Seq(a,mirror f)

  let to_tree = function
    | { head ; opened=[] } -> mirror head
    | { head ; opened=_::_} -> assert false

end



(** {6 State types} *)

(** We typically label nodes of [Trace.tree] with messages to
    print. But we don't want to compute the result. *)
type lazy_msg = unit -> Pp.t
let pr_lazy_msg msg = msg ()

(** Info trace. *)
module Info = struct

  (** The type of the tags for [info]. *)
  type tag =
    | Msg of lazy_msg (** A simple message *)
    | Tactic of lazy_msg (** A tactic call *)
    | Dispatch  (** A call to [tclDISPATCH]/[tclEXTEND] *)
    | DBranch  (** A special marker to delimit individual branch of a dispatch. *)

  type state = tag Trace.incr
  type tree = tag Trace.forest



  let pr_in_comments m = Pp.(str"(* "++pr_lazy_msg m++str" *)")

  let unbranch = function
    | Trace.Seq (DBranch,brs) -> brs
    | _ -> assert false


  let is_empty_branch = let open Trace in function
    | Seq(DBranch,[]) -> true
    | _ -> false

  (** Dispatch with empty branches are (supposed to be) equivalent to
      [idtac] which need not appear, so they are removed from the
      trace. *)
  let dispatch brs =
    let open Trace in
    if CList.for_all is_empty_branch brs then None
    else Some (Seq(Dispatch,brs))

  let constr = let open Trace in function
    | Dispatch -> dispatch
    | t -> fun br -> Some (Seq(t,br))

  let rec compress_tree = let open Trace in function
    | Seq(t,f) -> constr t (compress f)
  and compress f =
    CList.map_filter compress_tree f

  (** [with_sep] is [true] when [Tactic m] must be printed with a
      trailing semi-colon. *)
  let rec pr_tree with_sep = let open Trace in function
    | Seq (Msg m,[]) -> pr_in_comments m
    | Seq (Tactic m,_) ->
        let tail = if with_sep then Pp.str";" else Pp.mt () in
        Pp.(pr_lazy_msg m ++ tail)
    | Seq (Dispatch,brs) ->
        let tail = if with_sep then Pp.str";" else Pp.mt () in
        Pp.(pr_dispatch brs++tail)
    | Seq (Msg _,_::_) | Seq (DBranch,_) -> assert false
  and pr_dispatch brs =
    let open Pp in
    let brs = List.map unbranch brs in
    match brs with
    | [br] -> pr_forest br
    | _ ->
        let sep () = spc()++str"|"++spc() in
        let branches = prlist_with_sep sep pr_forest brs in
        str"[>"++spc()++branches++spc()++str"]"
  and pr_forest = function
    | [] -> Pp.mt ()
    | [tr] -> pr_tree false tr
    | tr::l -> Pp.(pr_tree true tr ++ pr_forest l)

  let print f =
    pr_forest (compress f)

  let rec collapse_tree n t =
    let open Trace in
    match n , t with
    | 0 , t -> [t]
    | _ , (Seq(Tactic _,[]) as t) -> [t]
    | n , Seq(Tactic _,f) -> collapse (pred n) f
    | n , Seq(Dispatch,brs) -> [Seq(Dispatch, (collapse n brs))]
    | n , Seq(DBranch,br) -> [Seq(DBranch, (collapse n br))]
    | _ , (Seq(Msg _,_) as t) -> [t]
  and collapse n f =
    CList.map_append (collapse_tree n) f
end

module StateStore = Store.Make(struct end)

(* let (set_state, get_state) = StateDyn.Easy.make_dyn "goal_state" *)

type goal = Evar.t
type goal_with_state = Evar.t * StateStore.t

let drop_state = fst
let get_state = snd
let goal_with_state g s = (g, s)
let with_empty_state g = (g, StateStore.empty)
let map_goal_with_state f (g, s) = (f g, s)

(** Type of proof views: current [evar_map] together with the list of
    focused goals. *)
type proofview = {
  solution : Evd.evar_map;
  comb : goal_with_state list;
  shelf : goal list;
}

(** {6 Instantiation of the logic monad} *)

(** Parameters of the logic monads *)
module P = struct

  type s = proofview * Environ.env

  (** Recording info trace (true) or not. *)
  type e = bool

  (** Status (safe/unsafe) * shelved goals * given up *)
  type w = bool * goal list

  let wunit = true , []
  let wprod (b1, g1) (b2, g2) = b1 && b2 , g1@g2

  type u = Info.state

  let uunit = Trace.empty_incr

end

module Logical = Logic_monad.Logical(P)


(** {6 Lenses to access to components of the states} *)

module type State = sig
  type t
  val get : t Logical.t
  val set : t -> unit Logical.t
  val modify : (t->t) -> unit Logical.t
end

module type Writer = sig
  type t
  val put : t -> unit Logical.t
end

module Pv : State with type t := proofview = struct
  let get = Logical.(map fst get)
  let set p = Logical.modify (fun (_,e) -> (p,e))
  let modify f= Logical.modify (fun (p,e) -> (f p,e))
end

module Solution : State with type t := Evd.evar_map = struct
  let get = Logical.map (fun {solution} -> solution) Pv.get
  let set s = Pv.modify (fun pv -> { pv with solution = s })
  let modify f = Pv.modify (fun pv -> { pv with solution = f pv.solution })
end

module Comb : State with type t = goal_with_state list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = goal_with_state list
  let get = Logical.map (fun {comb} -> comb) Pv.get
  let set c = Pv.modify (fun pv -> { pv with comb = c })
  let modify f = Pv.modify (fun pv -> { pv with comb = f pv.comb })
end

module Env : State with type t := Environ.env = struct
  let get = Logical.(map snd get)
  let set e = Logical.modify (fun (p,_) -> (p,e))
  let modify f = Logical.modify (fun (p,e) -> (p,f e))
end

module Status : Writer with type t := bool = struct
  let put s = Logical.put (s, [])
end

module Shelf : State with type t = goal list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = goal list
  let get = Logical.map (fun {shelf} -> shelf) Pv.get
  let set c = Pv.modify (fun pv -> { pv with shelf = c })
  let modify f = Pv.modify (fun pv -> { pv with shelf = f pv.shelf })
end

module Giveup : Writer with type t = goal list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = goal list
  let put gs = Logical.put (true, gs)
end

(** Lens and utilies pertaining to the info trace *)
module InfoL = struct
  let recording = Logical.current
  let if_recording t =
    let open Logical in
    recording >>= fun r ->
    if r then t else return ()

  let record_trace t = Logical.local true t

  let raw_update = Logical.update
  let update f = if_recording (raw_update f)
  let opn a = update (Trace.opn a)
  let close = update Trace.close
  let leaf a = update (Trace.leaf a)

  let tag a t =
    let open Logical in
    recording >>= fun r ->
    if r then begin
      raw_update (Trace.opn a) >>
      t >>= fun a ->
      raw_update Trace.close >>
      return a
    end else
      t
end
