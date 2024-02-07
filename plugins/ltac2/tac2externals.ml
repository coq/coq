(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
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
  | T : 'r to_v annotated -> (v tactic, 'r tactic, 'r) spec_aux
  | V : 'r to_v annotated -> (v tactic, 'r, 'r) spec_aux
  | E : 'r to_v annotated -> (v tactic, 'r with_env, 'r) spec_aux
  | G : 'r to_v annotated -> (v tactic, Goal.t -> 'r, 'r) spec_aux
  | F : 'a of_v annotated * ('t, 'f, 'r) spec_aux -> (v -> 't , 'a -> 'f, 'r) spec_aux

type (_,_) spec = S : ('v,'f,'r) spec_aux -> ('v,'f) spec [@@unboxed]

let tac : type r. r repr annotated -> (v tactic, r tactic) spec = fun r ->
  S (T (on_fst repr_of r))

let tac': type r. r to_v annotated -> (v tactic, r tactic) spec = fun tr ->
  S (T tr)

let ret : type r. r repr annotated -> (v tactic, r) spec = fun r ->
  S (V (on_fst repr_of r))

let ret': type r. r to_v annotated -> (v tactic, r) spec = fun tr ->
  S (V tr)

let eret : type r. r repr annotated -> (v tactic, r with_env) spec = fun r ->
  S (E (on_fst repr_of r))

let eret': type r. r to_v annotated -> (v tactic, r with_env) spec = fun tr ->
  S (E tr)

let gret : type r. r repr annotated -> (v tactic, Goal.t -> r) spec = fun r ->
  S (G (on_fst repr_of r))

let gret': type r. r to_v annotated -> (v tactic, Goal.t -> r) spec = fun tr ->
  S (G tr)

let (@->) : type a t f. a repr annotated -> (t,f) spec -> (v -> t, a -> f) spec =
  fun r (S ar) -> S (F (on_fst repr_to r, ar))

let (@-->): type a t f. a of_v annotated -> (t,f) spec -> (v -> t, a -> f) spec =
  fun of_v (S ar) -> S (F (of_v, ar))

let rec interp_spec : type v f. (v,f) spec -> f -> v = fun (S ar) f ->
  let open Proofview.Notations in
  match ar with
  | T tr -> f >>= fun v -> tclUNIT (fst tr v)
  | V tr -> tclUNIT (fst tr f)
  | E tr -> tclENV >>= fun e -> tclEVARMAP >>= fun s -> tclUNIT (fst tr (f e s))
  | G tr -> Goal.enter_one @@ fun g -> tclUNIT (fst tr (f g))
  | F (tr,ar) -> fun v -> interp_spec (S ar) (f (fst tr v))

let rec arity_of : type v f. (v,f) spec -> v Tac2val.arity = fun (S ar) ->
  match ar with
  | F (_, T _) -> Tac2val.arity_one
  | F (_, V _) -> Tac2val.arity_one
  | F (_, E _) -> Tac2val.arity_one
  | F (_, G _) -> Tac2val.arity_one
  | F (_, ar) -> Tac2val.arity_suc (arity_of (S ar))
  | _ -> invalid_arg "Tac2def.arity_of: not a function spec"

let rec type_of_spec : type v f. (v,f) spec -> Types.t = fun (S ar) ->
  let of_annot (_,t) = Option.default Types.any t in
  match ar with
  | T tr -> of_annot tr
  | V tr -> of_annot tr
  | E tr -> of_annot tr
  | G tr -> of_annot tr
  | F (tr,ar) -> Types.(of_annot tr @-> type_of_spec (S ar))

let define : type v f. _ -> (v,f) spec -> f -> unit = fun n ar v ->
  let v =
    match ar with
    | S (V tr) -> fst tr v
    | S (F _) ->
        let cl = Tac2val.mk_closure (arity_of ar) (interp_spec ar v) in
        Tac2ffi.of_closure cl
    | _ -> invalid_arg "Tac2def.define: not a pure value"
  in
  let ty = Some (Types.as_scheme @@ type_of_spec ar) in
  Tac2env.define_primitive n ty v
