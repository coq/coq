(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Proofview
open Tac2ffi

(* Local shortcuts. *)
type v = Tac2val.valexpr
type 'r of_v = v -> 'r
type 'r to_v = 'r -> v
type 'a with_env = Environ.env -> Evd.evar_map -> 'a

(* We use two levels of GADT to get rid of the third type parameter, which has
   to be give for this type definition to be accepted. If we remove it, we get
   an error: "a type variable cannot be deduced from the type parameters". *)
type (_, _, _) spec_aux =
  | T : 'r to_v -> (v tactic, 'r tactic, 'r) spec_aux
  | V : 'r to_v -> (v tactic, 'r, 'r) spec_aux
  | E : 'r to_v -> (v tactic, 'r with_env, 'r) spec_aux
  | G : 'r to_v -> (v tactic, Goal.t -> 'r, 'r) spec_aux
  | F : 'a of_v * ('t, 'f, 'r) spec_aux -> (v -> 't , 'a -> 'f, 'r) spec_aux

type (_,_) spec = S : ('v,'f,'r) spec_aux -> ('v,'f) spec [@@unboxed]

let tac : type r. r repr -> (v tactic, r tactic) spec = fun r ->
  S (T (repr_of r))

let tac': type r. r to_v -> (v tactic, r tactic) spec = fun tr ->
  S (T tr)

let ret : type r. r repr -> (v tactic, r) spec = fun r ->
  S (V (repr_of r))

let ret': type r. r to_v -> (v tactic, r) spec = fun tr ->
  S (V tr)

let eret : type r. r repr -> (v tactic, r with_env) spec = fun r ->
  S (E (repr_of r))

let eret': type r. r to_v -> (v tactic, r with_env) spec = fun tr ->
  S (E tr)

let gret : type r. r repr -> (v tactic, Goal.t -> r) spec = fun r ->
  S (G (repr_of r))

let gret': type r. r to_v -> (v tactic, Goal.t -> r) spec = fun tr ->
  S (G tr)

let (@->) : type a t f. a repr -> (t,f) spec -> (v -> t, a -> f) spec =
  fun r (S ar) -> S (F (repr_to r, ar))

let (@-->): type a t f. a of_v -> (t,f) spec -> (v -> t, a -> f) spec =
  fun of_v (S ar) -> S (F (of_v, ar))

let rec interp_spec : type v f. (v,f) spec -> f -> v = fun (S ar) f ->
  let open Proofview.Notations in
  match ar with
  | T tr -> f >>= fun v -> tclUNIT (tr v)
  | V tr -> tclUNIT (tr f)
  | E tr -> tclENV >>= fun e -> tclEVARMAP >>= fun s -> tclUNIT (tr (f e s))
  | G tr -> Goal.enter_one @@ fun g -> tclUNIT (tr (f g))
  | F (tr,ar) -> fun v -> interp_spec (S ar) (f (tr v))

let rec arity_of : type v f. (v,f) spec -> v Tac2val.arity = fun (S ar) ->
  match ar with
  | F (_, T _) -> Tac2val.arity_one
  | F (_, V _) -> Tac2val.arity_one
  | F (_, E _) -> Tac2val.arity_one
  | F (_, G _) -> Tac2val.arity_one
  | F (_, ar) -> Tac2val.arity_suc (arity_of (S ar))
  | _ -> invalid_arg "Tac2def.arity_of: not a function spec"

let define : type v f. _ -> (v,f) spec -> f -> unit = fun n ar v ->
  let v =
    match ar with
    | S (V tr) -> tr v
    | S (F _) ->
      let arity = arity_of ar in
      let v = interp_spec ar v in
      let v = Tac2val.purify_closure arity v in
      let cl = Tac2val.mk_closure arity v in
      Tac2ffi.of_closure cl
    | _ -> invalid_arg "Tac2def.define: not a pure value"
  in
  Tac2env.define_primitive n v
