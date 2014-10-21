(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines the datatypes used as internal states by the
    tactic monad, and specialises the [Logic_monad] to these type. *)

(** {6 State types} *)

(** Type of proof views: current [evar_map] together with the list of
    focused goals. *)
type proofview = { solution : Evd.evar_map; comb : Goal.goal list }


(** {6 Instantiation of the logic monad} *)

(** Parameters of the logic monads *)
module P = struct

  type s = proofview * Environ.env

  type e = unit
  (* spiwack: nothing read-only anymore but it's free so I'll leave a place holder. *)

  (** Status (safe/unsafe) * shelved goals * given up *)
  type w = bool * Evar.t list * Evar.t list

  let wunit = true , [] , []
  let wprod (b1,s1,g1) (b2,s2,g2) = b1 && b2 , s1@s2 , g1@g2

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

module Comb : State with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
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
  let put s = Logical.put (s,[],[])
end

module Shelf : Writer with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
  let put sh = Logical.put (true,sh,[])
end

module Giveup : Writer with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
  let put gs = Logical.put (true,[],gs)
end
