(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Proof

type t =
    | Dash of int
    | Star of int
    | Plus of int

let bullet_eq b1 b2 = match b1, b2 with
| Dash n1, Dash n2 -> n1 = n2
| Star n1, Star n2 -> n1 = n2
| Plus n1, Plus n2 -> n1 = n2
| _ -> false

let pr_bullet b =
  match b with
  | Dash n -> Pp.(str (String.make n '-'))
  | Star n -> Pp.(str (String.make n '*'))
  | Plus n -> Pp.(str (String.make n '+'))


type behavior = {
  name : string;
  put : Proof.t -> t -> Proof.t;
  suggest: Proof.t -> Pp.t
}

let behaviors = Hashtbl.create 4
let register_behavior b = Hashtbl.add behaviors b.name b

(*** initial modes ***)
let none = {
  name = "None";
  put = (fun x _ -> x);
  suggest = (fun _ -> Pp.mt ())
}
let _ = register_behavior none

module Strict = struct
  type suggestion =
  | Suggest of t (* this bullet is mandatory here *)
  | Unfinished of t (* no mandatory bullet here, but this bullet is unfinished *)
  | NoBulletInUse (* No mandatory bullet (or brace) here, no bullet pending,
               some focused goals exists. *)
  | NeedClosingBrace (* Some unfocussed goal exists "{" needed to focus them *)
  | ProofFinished (* No more goal anywhere *)

  (* give a message only if more informative than the standard rocq message *)
  let suggest_on_solved_goal sugg =
    match sugg with
    | NeedClosingBrace -> Pp.(str"Try unfocusing with \"}\".")
    | NoBulletInUse -> Pp.mt ()
    | ProofFinished -> Pp.mt ()
    | Suggest b -> Pp.(str"Focus next goal with bullet " ++ pr_bullet b ++ str".")
    | Unfinished b -> Pp.(str"The current bullet " ++ pr_bullet b ++ str" is unfinished.")

  (* give always a message. *)
  let suggest_on_error sugg =
    match sugg with
    | NeedClosingBrace -> Pp.(str"Try unfocusing with \"}\".")
    | NoBulletInUse -> assert false (* This should never raise an error. *)
    | ProofFinished -> Pp.(str"No more goals.")
    | Suggest b -> Pp.(str"Expecting " ++ pr_bullet b ++ str".")
    | Unfinished b -> Pp.(str"Current bullet " ++ pr_bullet b ++ str" is not finished.")

  exception FailedBullet of t * suggestion

  let _ =
    CErrors.register_handler
      (function
      | FailedBullet (b,sugg) ->
        let prefix = Pp.(str"Wrong bullet " ++ pr_bullet b ++ str": ") in
        Some Pp.(str "[Focus]" ++ spc () ++ prefix ++ suggest_on_error sugg)
      | _ -> None)


  (* spiwack: we need only one focus kind as we keep a stack of (distinct!) bullets *)
  let bullet_kind = (new_focus_kind "bullet_kind" : t list focus_kind)
  let bullet_cond = done_cond ~loose_end:true bullet_kind

  (* spiwack: as it is bullets are reset (locally) by *any* non-bullet focusing command
     experience will tell if this is the right discipline of if we want to be finer and
     reset them only for a choice of bullets. *)
  let get_bullets pr =
    if is_last_focus bullet_kind pr then
      get_at_focus bullet_kind pr
    else
      []

  let has_bullet bul pr =
    let rec has_bullet = function
      | b'::_ when bullet_eq bul b' -> true
      | _::l -> has_bullet l
      | [] -> false
    in
    has_bullet (get_bullets pr)

  (* pop a bullet from proof [pr]. There should be at least one
     bullet in use. If pop impossible (pending proofs on this level
     of bullet or higher) then raise [Proof.CannotUnfocusThisWay]. *)
  let pop pr =
    match get_bullets pr with
    | b::_ -> Some (unfocus bullet_kind pr (), b)
    | _ -> None

  let push (b:t) pr =
    focus bullet_cond (b::get_bullets pr) 1 pr

  let suggest_bullet (prf : Proof.t): suggestion =
    if is_done prf then ProofFinished
    else if not (no_focused_goal prf)
    then (* No suggestion if a bullet is not mandatory, look for an unfinished bullet *)
      match get_bullets prf with
      | b::_ -> Unfinished b
      | _ -> NoBulletInUse
    else (* There is no goal under focus but some are unfocussed,
            let us look at the bullet needed. *)
      let rec loop prf =
        match pop prf with
        | Some (prf, b) ->
          (* pop went well, this means that there are no more goals
           *under this* bullet b, see if a new b can be pushed. *)
          begin
            try ignore (push b prf); Suggest b
            with e when CErrors.noncritical e ->
              (* b could not be pushed, so we must look for a outer bullet *)
              loop prf
          end
        | None ->
          (* No pop was possible, but there are still
             subgoals somewhere: there must be a "}" to use. *)
          NeedClosingBrace
      in
      loop prf

  let rec pop_until (prf : Proof.t) bul : Proof.t =
    let prf', b = Option.get (pop prf) in
    if bullet_eq bul b then prf'
    else pop_until prf' bul

  let put p bul =
    try
      if not (has_bullet bul p) then
        (* bullet is not in use, so pushing it is always ok unless
           no goal under focus. *)
        push bul p
      else
        match suggest_bullet p with
        | Suggest suggested_bullet when bullet_eq bul suggested_bullet
            -> (* suggested_bullet is mandatory and you gave the right one *)
          let p' = pop_until p bul in
          push bul p'
      (* the bullet you gave is in use but not the right one *)
        | sugg -> raise (FailedBullet (bul,sugg))
    with NoSuchGoals _ -> (* push went bad *)
      raise (FailedBullet (bul,suggest_bullet p))

  let strict = {
    name = "Strict Subproofs";
    put = put;
    suggest = (fun prf -> suggest_on_solved_goal (suggest_bullet prf))

  }
  let _ = register_behavior strict
end

(* Current bullet behavior, controlled by the option *)
let { Goptions.get = current_behavior } =
  Goptions.declare_interpreted_string_option_and_ref
    ~key:["Bullet";"Behavior"]
    ~value:Strict.strict
    (fun n ->
      try Hashtbl.find behaviors n
      with Not_found ->
        CErrors.user_err Pp.(str ("Unknown bullet behavior: \"" ^ n ^ "\".")))
    (fun v -> v.name)
    ()

let put p b =
  (current_behavior ()).put p b

let suggest p =
  (current_behavior ()).suggest p

let _ = CErrors.register_handler begin function
    | Proof.SuggestNoSuchGoals(n,proof) ->
      let suffix = suggest proof in
      Some (Pp.(str "No such " ++ str (CString.plural n "goal") ++ str "." ++
                pr_non_empty_arg (fun x -> x) suffix))
    | _ -> None
  end
