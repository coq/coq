(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* The proofview datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a proofview which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with 
   one another, which represents the various subnodes of the proof. Together
   with a comb: a datastructure that gives some order to some of these nodes, 
   namely the (focused) open goals. 
   The natural candidate for the solution is an {!Evd.evar_map}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the proofview
   to be able to return information about the proofview. *)

open Pp
open Util
open Proofview_monad

(* Type of proofviews. *)
type proofview = { solution : Evd.evar_map; comb : Goal.goal list }

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

(** Definition of the tactic monad *)
module Proof = Logical(P)

(** Lenses to access to components of the states *)
module type State = sig
  type t
  val get : t Proof.t
  val set : t -> unit Proof.t
  val modify : (t->t) -> unit Proof.t
end

module type Writer = sig
  type t
  val put : t -> unit Proof.t
end

module Pv : State with type t := proofview = struct
  let get = Proof.(map fst get)
  let set p = Proof.modify (fun (_,e) -> (p,e))
  let modify f= Proof.modify (fun (p,e) -> (f p,e))
end

module Solution : State with type t := Evd.evar_map = struct
  let get = Proof.map (fun {solution} -> solution) Pv.get
  let set s = Pv.modify (fun pv -> { pv with solution = s })
  let modify f = Pv.modify (fun pv -> { pv with solution = f pv.solution })
end

module Comb : State with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
  let get = Proof.map (fun {comb} -> comb) Pv.get
  let set c = Pv.modify (fun pv -> { pv with comb = c })
  let modify f = Pv.modify (fun pv -> { pv with comb = f pv.comb })
end

module Env : State with type t := Environ.env = struct
  let get = Proof.(map snd get)
  let set e = Proof.modify (fun (p,_) -> (p,e))
  let modify f = Proof.modify (fun (p,e) -> (p,f e))
end

module Status : Writer with type t := bool = struct
  let put s = Proof.put (s,[],[])
end

module Shelf : Writer with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
  let put sh = Proof.put (true,sh,[])
end

module Giveup : Writer with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
  let put gs = Proof.put (true,[],gs)
end


module Monad = Monad.Make(struct type 'a t = 'a Proof.t let (>>=) = Proof.bind let (>>) = Proof.seq let map = Proof.map let return = Proof.ret end)

type entry = (Term.constr * Term.types) list

let proofview p =
  p.comb , p.solution

type telescope =
  | TNil of Evd.evar_map
  | TCons of Environ.env * Evd.evar_map * Term.types * (Evd.evar_map -> Term.constr -> telescope)

let dependent_init =
  let rec aux = function
  | TNil sigma -> [], { solution = sigma; comb = []; }
  | TCons (env, sigma, typ, t) ->
    let src = (Loc.ghost,Evar_kinds.GoalEvar) in
    let (sigma, econstr ) = Evarutil.new_evar env sigma ~src typ in
    let ret, { solution = sol; comb = comb } = aux (t sigma econstr) in
    let (gl, _) = Term.destEvar econstr in
    let entry = (econstr, typ) :: ret in
    entry, { solution = sol; comb = gl :: comb; }
  in
  fun t ->
    let entry, v = aux t in
    (* Marks all the goal unresolvable for typeclasses. *)
    let solution = Typeclasses.mark_unresolvables v.solution in
    (* The created goal are not to be shelved. *)
    let solution = Evd.reset_future_goals solution in
    entry, { v with solution }

(* Initialises a proofview, the argument is a list of environement,
   conclusion types, and optional names, creating that many initial goals. *)
let init =
  let rec aux sigma = function
    | [] -> TNil sigma
    | (env,g)::l -> TCons (env,sigma,g,(fun sigma _ -> aux sigma l))
  in
  fun sigma l -> dependent_init (aux sigma l)

let initial_goals initial = initial

(* Returns whether this proofview is finished or not. That is,
   if it has empty subgoals in the comb. There could still be unsolved
   subgoaled, but they would then be out of the view, focused out. *)
let finished = function
  | {comb = []} -> true
  | _  -> false

(* Returns the current value of the proofview partial proofs. *)
let return { solution=defs } = defs

let return_constr { solution = defs } c = Evarutil.nf_evar defs c

let partial_proof entry pv = List.map (return_constr pv) (List.map fst entry)


(* Type of the object which allow to unfocus a view.*)
(* First component is a reverse list of what comes before
   and second component is what goes after (in the expected
   order) *)
type focus_context = Evar.t list * Evar.t list

let focus_context f = f

(* This (internal) function extracts a sublist between two indices, and
   returns this sublist together with its context:
   if it returns [(a,(b,c))] then [a] is the sublist and (rev b)@a@c is the
   original list.
   The focused list has lenght [j-i-1] and contains the goals from
   number [i] to number [j] (both included) the first goal of the list
   being numbered [1].
   [focus_sublist i j l] raises [IndexOutOfRange] if
   [i > length l], or [j > length l] or [ j < i ].  *)
let focus_sublist i j l =
  let (left,sub_right) = CList.goto (i-1) l in
  let (sub, right) = 
    try List.chop (j-i+1) sub_right
    with Failure _ -> raise CList.IndexOutOfRange
  in
  (sub, (left,right))

(* Inverse operation to the previous one. *)
let unfocus_sublist (left,right) s =
  List.rev_append left (s@right)


(* [focus i j] focuses a proofview on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned proofview). The first goal has index 1.
   It returns the focus proof, and a context for the focus trace. *)
let focus i j sp =
  let (new_comb, context) = focus_sublist i j sp.comb in
  ( { sp with comb = new_comb } , context )


(* [advance sigma g] returns [Some g'] if [g'] is undefined and
    is the current avatar of [g] (for instance [g] was changed by [clear]
    into [g']). It returns [None] if [g] has been (partially) solved. *)
(* spiwack: [advance] is probably performance critical, and the good
   behaviour of its definition may depend sensitively to the actual
   definition of [Evd.find]. Currently, [Evd.find] starts looking for
   a value in the heap of undefined variable, which is small. Hence in
   the most common case, where [advance] is applied to an unsolved
   goal ([advance] is used to figure if a side effect has modified the
   goal) it terminates quickly. *)
let rec advance sigma g =
  let open Evd in
  let evi = Evd.find sigma g in
  match evi.evar_body with
  | Evar_empty -> Some g
  | Evar_defined v ->
      if Option.default false (Store.get evi.evar_extra Evarutil.cleared) then
        let (e,_) = Term.destEvar v in
        advance sigma e
      else
        None

(** [undefined defs l] is the list of goals in [l] which are still
    unsolved (after advancing cleared goals). *)
let undefined defs l = CList.map_filter (advance defs) l

(* Unfocuses a proofview with respect to a context. *)
let unfocus c sp =
  { sp with comb = undefined sp.solution (unfocus_sublist c sp.comb) }


(* The tactic monad:
   - Tactics are objects which apply a transformation to all
     the subgoals of the current view at the same time. By opposition
     to the old vision of applying it to a single goal. It allows 
     tactics such as [shelve_unifiable] or tactics to reorder
     the focused goals (not done yet).
     (* spiwack: the ordering of goals, though, is actually rather
        brittle. It would be much more interesting to find a more
        robust way to adress goals, I have no idea at this time 
        though*) 
     or global automation tactic for dependent subgoals (instantiating
     an evar has influences on the other goals of the proof in progress,
     not being able to take that into account causes the current eauto
     tactic to fail on some instances where it could succeed).
     Another benefit is that it is possible to write tactics that can
     be executed even if there are no focused goals.
   - Tactics form a monad ['a tactic], in a sense a tactic can be 
     seens as a function (without argument) which returns a value
     of type 'a and modifies the environement (in our case: the view).
     Tactics of course have arguments, but these are given at the 
     meta-level as OCaml functions.
     Most tactics in the sense we are used to return [()], that is
     no really interesting values. But some might pass information 
     around. 
     (* spiwack: as far as I'm aware this doesn't really relate to
        F. Kirchner and C. Muñoz.
     *)
     The tactics seen in Coq's Ltac are (for now at least) only 
     [unit tactic], the return values are kept for the OCaml toolkit.
     The operation or the monad are [Proofview.tclUNIT] (which is the 
     "return" of the tactic monad) [Proofview.tclBIND] (which is
     the "bind") and [Proofview.tclTHEN] (which is a specialized
     bind on unit-returning tactics).
*)

(* type of tactics:

   tactics can
   - access the environment,
   - report unsafe status, shelved goals and given up goals
   - access and change the current [proofview]
   - backtrack on previous changes of the proofview *)
type +'a tactic = 'a Proof.t

type 'a case =
| Fail of exn
| Next of 'a * (exn -> 'a tactic)

(* Applies a tactic to the current proofview. *)
let apply env t sp =
  let (next_r,(next_state,_),status) =
    Proofview_monad.NonLogical.run (Proof.run t () (sp,env))
  in
  next_r,next_state,status

(*** tacticals ***)


let catchable_exception = function
  | Proofview_monad.Exception _ -> false
  | e -> Errors.noncritical e


(* Unit of the tactic monad *)
let tclUNIT = Proof.ret

(* Bind operation of the tactic monad *)
let tclBIND = Proof.bind

(* Interpretes the ";" (semicolon) of Ltac.
   As a monadic operation, it's a specialized "bind"
   on unit-returning tactic (meaning "there is no value to bind") *)
let tclTHEN = Proof.seq

(* [tclIGNORE t] has the same operational content as [t],
   but drops the value at the end. *)
let tclIGNORE = Proof.ignore

(* [tclOR t1 t2 = t1] as long as [t1] succeeds. Whenever the successes
   of [t1] have been depleted and it failed with [e], then it behaves
   as [t2 e].  No interleaving at this point. *)
let tclOR = Proof.plus

(* [tclZERO e] always fails with error message [e]*)
let tclZERO = Proof.zero

(* [tclCASE t] observes the head of the tactic and returns it as a value *)
let tclCASE t =
  let map = function
  | Nil e -> Fail e
  | Cons (x, t) -> Next (x, t)
  in
  Proof.map map (Proof.split t)

(* [tclORELSE t1 t2] behaves like [t1] if [t1] succeeds at least once
   or [t2] if [t1] fails. *)
let tclORELSE t1 t2 =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.split t1 >>= function
    | Nil e -> t2 e
    | Cons (a,t1') -> Proof.plus (Proof.ret a) t1'

(* [tclIFCATCH a s f] is a generalisation of [tclORELSE]: if [a]
   succeeds at least once then it behaves as [tclBIND a s] otherwise, if [a]
   fails with [e], then it behaves as [f e]. *)
let tclIFCATCH a s f =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.split a >>= function
    | Nil e -> f e
    | Cons (x,a') -> Proof.plus (s x) (fun e -> (a' e) >>= fun x' -> (s x'))

(* [tclONCE t] fails if [t] fails, otherwise it has exactly one
   success. *)
let tclONCE = Proof.once

let tclBREAK = Proof.break

exception MoreThanOneSuccess
let _ = Errors.register_handler begin function
  | MoreThanOneSuccess -> Errors.error "This tactic has more than one success."
  | _ -> raise Errors.Unhandled
end

(* [tclONCE e t] succeeds as [t] if [t] has exactly one
   success. Otherwise it fails.  It may behave differently than [t] as
   there may be extra non-logical effects used to discover that [t]
   does not have a second success. Moreover the second success may be
   conditional on the error recieved: [e] is used. *)
let tclEXACTLY_ONCE e t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.split t >>= function
    | Nil e -> tclZERO e
    | Cons (x,k) ->
        Proof.split (k e) >>= function
          | Nil _ -> tclUNIT x
          | _ -> tclZERO MoreThanOneSuccess


(* Focuses a tactic at a range of subgoals, found by their indices. *)
exception NoSuchGoals of int
let _ = Errors.register_handler begin function
  | NoSuchGoals n -> Errors.error ("No such " ^ String.plural n "goal" ^".")
  | _ -> raise Errors.Unhandled
end
let tclFOCUS_gen nosuchgoal i j t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Pv.get >>= fun initial ->
  try
    let (focused,context) = focus i j initial in
    Pv.set focused >>
    t >>= fun result ->
    Pv.modify (fun next -> unfocus context next) >>
    Proof.ret result
  with CList.IndexOutOfRange -> nosuchgoal

let tclFOCUS i j t = tclFOCUS_gen (tclZERO (NoSuchGoals (j+1-i))) i j t
let tclTRYFOCUS i j t = tclFOCUS_gen (tclUNIT ()) i j t

let tclFOCUSID id t =
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Pv.get >>= fun initial ->
  let rec aux n = function
    | [] -> tclZERO (NoSuchGoals 1)
    | g::l ->
        if Names.Id.equal (Evd.evar_ident g initial.solution) id then
          let (focused,context) = focus n n initial in
          Pv.set focused >>
            t >>= fun result ->
          Pv.modify (fun next -> unfocus context next) >>
            Proof.ret result
        else
          aux (n+1) l in
  aux 1 initial.comb


(* Dispatch tacticals are used to apply a different tactic to each goal under
   consideration. They come in two flavours:
   [tclDISPATCH] takes a list of [unit tactic]-s and build a [unit tactic].
   [tclDISPATCHL] takes a list of ['a tactic] and returns an ['a list tactic].

   They both work by applying each of the tactic to the corresponding
   goal (starting with the first goal). In the case of [tclDISPATCHL],
   the tactic returns a list of the same size as the argument list (of
   tactics), each element being the result of the tactic executed in
   the corresponding goal. *)
exception SizeMismatch of int*int
let _ = Errors.register_handler begin function
  | SizeMismatch (i,_) ->
      let open Pp in
      let errmsg =
        str"Incorrect number of goals" ++ spc() ++
        str"(expected "++int i++str" tactics)."
      in
      Errors.errorlabstrm "" errmsg
  | _ -> raise Errors.Unhandled
end

(* A variant of [Monad.List.iter] where we iter over the focused list of
   goals. The argument tactic is executed in a focus comprising only
   of the current goal, a goal which has been solved by side effect is
   skipped. The generated subgoals are concatenated in order.  *)
let iter_goal i =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Comb.get >>= fun initial ->
  Monad.List.fold_left begin fun (subgoals as cur) goal ->
    Solution.get >>= fun step ->
    match advance step goal with
    | None -> Proof.ret cur
    | Some goal ->
        Comb.set [goal] >>
        i goal >>
        Proof.map (fun comb -> comb :: subgoals) Comb.get
  end [] initial >>= fun subgoals ->
  Comb.set (List.flatten (List.rev subgoals))

(* A variant of [Monad.List.fold_left2] where the first list is the
   list of focused goals. The argument tactic is executed in a focus
   comprising only of the current goal, a goal which has been solved
   by side effect is skipped. The generated subgoals are concatenated
   in order. *)
let fold_left2_goal i s l =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Pv.get >>= fun initial ->
  tclORELSE begin
    Monad.List.fold_left2 tclZERO begin fun ((r,subgoals) as cur) goal a ->
      Solution.get >>= fun step ->
      match advance step goal with
      | None -> Proof.ret cur
      | Some goal ->
          Comb.set [goal] >>
            i goal a r >>= fun r ->
          Proof.map (fun comb -> (r, comb :: subgoals)) Comb.get
    end (s,[]) initial.comb l >>= fun (r,subgoals) ->
    Comb.set (List.flatten (List.rev subgoals)) >>
    Proof.ret r
  end
  begin function
      | SizeMismatch _ -> tclZERO (SizeMismatch (List.length initial.comb,List.length l))
      | reraise -> tclZERO reraise
    end

(* spiwack: we use an parametrised function to generate the dispatch
   tacticals.  [tclDISPATCHGEN] takes an argument [join] to reify the
   list of produced value into the final value. *)
let tclDISPATCHGEN f join tacs =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  match tacs with
  | [] ->
      begin 
        Comb.get >>= function
        | [] -> tclUNIT (join [])
        | comb -> tclZERO (SizeMismatch (List.length comb,0))
      end
  | [tac] ->
      begin
        Pv.get >>= function
        | { comb=[goal] ; solution } ->
            begin match advance solution goal with
            | None -> tclUNIT (join [])
            | Some _ -> Proof.map (fun res -> join [res]) (f tac)
            end
        | {comb} -> tclZERO (SizeMismatch(List.length comb,1))
      end
  | _ ->
      let iter _ t cur = Proof.map (fun y -> y :: cur) (f t) in
      let ans = fold_left2_goal iter [] tacs in
      Proof.map join ans

let tclDISPATCH tacs = tclDISPATCHGEN Util.identity ignore tacs

let tclDISPATCHL tacs =
  tclDISPATCHGEN Util.identity List.rev tacs

let extend_to_list startxs rx endxs l =
  (* spiwack: I use [l] essentially as a natural number *)
  let rec duplicate acc = function
    | [] -> acc
    | _::rest -> duplicate (rx::acc) rest
  in
  let rec tail to_match rest =
    match rest, to_match with
    | [] , _::_ -> raise (SizeMismatch(0,0)) (* placeholder *)
    | _::rest , _::to_match -> tail to_match rest
    | _ , [] -> duplicate endxs rest
  in
  let rec copy pref rest =
    match rest,pref with
    | [] , _::_ -> raise (SizeMismatch(0,0)) (* placeholder *)
    | _::rest, a::pref -> a::(copy pref rest)
    | _ , [] -> tail endxs rest
  in
  copy startxs l

let tclEXTEND tacs1 rtac tacs2 =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Comb.get >>= fun comb ->
  try
    let tacs = extend_to_list tacs1 rtac tacs2 comb in
    tclDISPATCH tacs
  with SizeMismatch _ ->
    tclZERO (SizeMismatch(
      List.length comb,
      (List.length tacs1)+(List.length tacs2)))
(* spiwack: failure occur only when the number of goals is too
   small. Hence we can assume that [rtac] is replicated 0 times for
   any error message. *)

let tclINDEPENDENT tac =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Pv.get >>= fun initial ->
  match initial.comb with
  | [] -> tclUNIT ()
  | [_] -> tac
  | _ -> iter_goal (fun _ -> tac)

(* Equality function on goals *)
let goal_equal evars1 gl1 evars2 gl2 =
  let evi1 = Evd.find evars1 gl1 in
  let evi2 = Evd.find evars2 gl2 in
  Evd.eq_evar_info evars2 evi1 evi2

let tclPROGRESS t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Pv.get >>= fun initial ->
  t >>= fun res ->
  Pv.get >>= fun final ->
  let test =
    Evd.progress_evar_map initial.solution final.solution &&
    not (Util.List.for_all2eq (fun i f -> goal_equal initial.solution i final.solution f) initial.comb final.comb)
  in
  if test then
    tclUNIT res
  else
    tclZERO (Errors.UserError ("Proofview.tclPROGRESS" , Pp.str"Failed to progress."))

let tclEVARMAP = Solution.get

let tclENV = Env.get


let emit_side_effects eff x =
  { x with solution = Evd.emit_side_effects eff x.solution }

let tclEFFECTS eff =
  Proof.bind (Proof.ret ())
    (fun () -> (* The Global.env should be taken at exec time *)
       Proof.seq
         (Env.set (Global.env ()))
         (Pv.modify (fun initial -> emit_side_effects eff initial)))

exception Timeout
let _ = Errors.register_handler begin function
  | Timeout -> Errors.errorlabstrm "Proofview.tclTIMEOUT" (Pp.str"Tactic timeout!")
  | _ -> Pervasives.raise Errors.Unhandled
end

let tclTIMEOUT n t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  (* spiwack: as one of the monad is a continuation passing monad, it
     doesn't force the computation to be threaded inside the underlying
     (IO) monad. Hence I force it myself by asking for the evaluation of
     a dummy value first, lest [timeout] be called when everything has
     already been computed. *)
  let t = Proof.lift (Proofview_monad.NonLogical.ret ()) >> t in
  Proof.get >>= fun initial ->
  Proof.lift begin
    Proofview_monad.NonLogical.catch
      begin
        Proofview_monad.NonLogical.bind
          (Proofview_monad.NonLogical.timeout n (Proof.run t () initial))
          (fun r -> Proofview_monad.NonLogical.ret (Util.Inl r))
      end
      begin function
        | Proofview_monad.Timeout -> Proofview_monad.NonLogical.ret (Util.Inr Timeout)
        | Proofview_monad.TacticFailure e as src ->
          let e = Backtrace.app_backtrace ~src ~dst:e in
          Proofview_monad.NonLogical.ret (Util.Inr e)
        | e -> Proofview_monad.NonLogical.raise e
      end
  end >>= function
    | Util.Inl (res,s,m) ->
        Proof.set s >>
        Proof.put m >>
        Proof.ret res
    | Util.Inr e -> tclZERO e

let tclTIME s t =
  let (>>=) = Proof.bind in
  let pr_time t1 t2 n msg =
    let msg =
      if n = 0 then
        str msg
      else
        str (msg ^ " after ") ++ int n ++ str (String.plural n " backtracking")
    in
    msg_info(str "Tactic call" ++ pr_opt str s ++ str " ran for " ++
             System.fmt_time_difference t1 t2 ++ str " " ++ surround msg) in
  let rec aux n t =
    tclUNIT () >>= fun () ->
    let tstart = System.get_time() in
    Proof.split t >>= function
    | Nil e ->
      begin
        let tend = System.get_time() in
        pr_time tstart tend n "failure";
        tclZERO e
      end
    | Cons (x,k) ->
        let tend = System.get_time() in
        pr_time tstart tend n "success";
        tclOR (tclUNIT x) (fun e -> aux (n+1) (k e))
  in aux 0 t

let mark_as_unsafe = Status.put false

(* Shelves all the goals under focus. *)
let shelve =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Comb.get >>= fun initial ->
  Comb.set [] >>
  Shelf.put initial


(* [contained_in_info e evi] checks whether the evar [e] appears in
   the hypotheses, the conclusion or the body of the evar_info
   [evi]. Note: since we want to use it on goals, the body is actually
   supposed to be empty. *)
let contained_in_info sigma e evi =
  Evar.Set.mem e (Evd.evars_of_filtered_evar_info (Evarutil.nf_evar_info sigma evi))

(* [depends_on sigma src tgt] checks whether the goal [src] appears as an
   existential variable in the definition of the goal [tgt] in [sigma]. *)
let depends_on sigma src tgt =
  let evi = Evd.find sigma tgt in
  contained_in_info sigma src evi

(* [unifiable sigma g l] checks whether [g] appears in another subgoal
   of [l]. The list [l] may contain [g], but it does not affect the
   result. *)
let unifiable sigma g l =
  List.exists (fun tgt -> not (Evar.equal g tgt) && depends_on sigma g tgt) l

(* [partition_unifiable sigma l] partitions [l] into a pair [(u,n)]
   where [u] is composed of the unifiable goals, i.e. the goals on
   whose definition other goals of [l] depend, and [n] are the
   non-unifiable goals. *)
let partition_unifiable sigma l =
  List.partition (fun g -> unifiable sigma g l) l

(* Shelves the unifiable goals under focus, i.e. the goals which
   appear in other goals under focus (the unfocused goals are not
   considered). *)
let shelve_unifiable =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Pv.get >>= fun initial ->
  let (u,n) = partition_unifiable initial.solution initial.comb in
  Comb.set n >>
  Shelf.put u

let check_no_dependencies =
  let (>>=) = Proof.bind in
  Pv.get >>= fun initial ->
  let (u,n) = partition_unifiable initial.solution initial.comb in
  match u with
  | [] -> tclUNIT ()
  | gls ->
      let l = List.map (fun g -> Evd.dependent_evar_ident g initial.solution) gls in
      let l = List.map (fun id -> Names.Name id) l in
      tclZERO (Logic.RefinerError (Logic.UnresolvedBindings l))

(* [unshelve l p] adds all the goals in [l] at the end of the focused
   goals of p *)
let unshelve l p =
  (* advance the goals in case of clear *)
  let l = undefined p.solution l in
  { p with comb = p.comb@l }

(* Gives up on the goal under focus. Reports an unsafe status. Proofs
   with given up goals cannot be closed. *)
let give_up =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Comb.get >>= fun initial ->
  Comb.set [] >>
  mark_as_unsafe >>
  Giveup.put initial

(** [goodmod p m] computes the representative of [p] modulo [m] in the
    interval [[0,m-1]].*)
let goodmod p m =
  let p' = p mod m in
  (* if [n] is negative [n mod l] is negative of absolute value less
     than [l], so [(n mod l)+l] is the representative of [n] in the
     interval [[0,l-1]].*)
  if p' < 0 then p'+m else p'

let cycle n =
  Comb.modify begin fun initial ->
    let l = List.length initial in
    let n' = goodmod n l in
    let (front,rear) = List.chop n' initial in
    rear@front
  end

let swap i j =
  Comb.modify begin fun initial ->
    let l = List.length initial in
    let i = if i>0 then i-1 else i and j = if j>0 then j-1 else j in
    let i = goodmod i l and j = goodmod j l in
    CList.map_i begin fun k x ->
      match k with
      | k when Int.equal k i -> CList.nth initial j
      | k when Int.equal k j -> CList.nth initial i
      | _ -> x
    end 0 initial
  end

let revgoals =
  Comb.modify List.rev

let numgoals =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Comb.get >>= fun comb ->
  Proof.ret (List.length comb)

module Unsafe = struct

  (* A [Proofview.tactic] version of [Refiner.tclEVARS] *)
  let tclEVARS evd =
    Pv.modify (fun ps -> { ps with solution = evd })

  let tclNEWGOALS gls =
    Pv.modify begin fun step ->
      let gls = undefined step.solution gls in
      { step with comb = step.comb @ gls }
    end

  let tclEVARSADVANCE evd =
    Pv.modify (fun ps -> { solution = evd; comb = undefined evd ps.comb })

  let tclEVARUNIVCONTEXT ctx = 
    Pv.modify (fun ps -> { ps with solution = Evd.set_universe_context ps.solution ctx })

  let reset_future_goals p =
    { p with solution = Evd.reset_future_goals p.solution }


end

module Notations = struct
  let (>>=) = tclBIND
  let (<*>) = tclTHEN
  let (<+>) t1 t2 = tclOR t1 (fun _ -> t2)
end

open Notations

(* To avoid shadowing by the local [Goal] module *)
module GoalV82 = Goal.V82

module Goal = struct

  type 'a t = {
    env : Environ.env;
    sigma : Evd.evar_map;
    concl : Term.constr ;
    self : Evar.t ; (* for compatibility with old-style definitions *)
  }

  let assume (gl : 'a t) = (gl :> [ `NF ] t)

  let env { env=env } = env
  let sigma { sigma=sigma } = sigma
  let hyps { env=env } = Environ.named_context env
  let concl { concl=concl } = concl

  let raw_concl { concl=concl } = concl


  let gmake_with info env sigma goal = 
    { env = Environ.reset_with_named_context (Evd.evar_filtered_hyps info) env ;
      sigma = sigma ;
      concl = Evd.evar_concl info ;
      self = goal }

  let nf_gmake env sigma goal =
    let info = Evarutil.nf_evar_info sigma (Evd.find sigma goal) in
    let sigma = Evd.add sigma goal info in
    gmake_with info env sigma goal , sigma

  let nf_enter f =
    iter_goal begin fun goal ->
      Env.get >>= fun env ->
      tclEVARMAP >>= fun sigma ->
      try
        let (gl, sigma) = nf_gmake env sigma goal in
        tclTHEN (Unsafe.tclEVARS sigma) (f gl)
      with e when catchable_exception e ->
        let e = Errors.push e in
        tclZERO e
    end

  let normalize { self } =
    Env.get >>= fun env ->
    tclEVARMAP >>= fun sigma ->
    let (gl,sigma) = nf_gmake env sigma self in
    tclTHEN (Unsafe.tclEVARS sigma) (tclUNIT gl)

  let gmake env sigma goal =
    let info = Evd.find sigma goal in
    gmake_with info env sigma goal

  let enter f =
    iter_goal begin fun goal ->
      Env.get >>= fun env ->
      tclEVARMAP >>= fun sigma ->
      try f (gmake env sigma goal)
      with e when catchable_exception e ->
        let e = Errors.push e in
        tclZERO e
    end

  let goals =
    Env.get >>= fun env ->
    Pv.get >>= fun step ->
    let sigma = step.solution in
    let map goal =
      match advance sigma goal with
      | None -> None (** ppedrot: Is this check really necessary? *)
      | Some goal ->
        let gl =
          tclEVARMAP >>= fun sigma ->
          tclUNIT (gmake env sigma goal)
        in
        Some gl
    in
    tclUNIT (List.map_filter map step.comb)

  (* compatibility *)
  let goal { self=self } = self

end

module Refine =
struct

  let mark_as_goal evd content =
    let info = Evd.find evd content in
    let info =
      { info with Evd.evar_source = (fst (info.Evd.evar_source),Evar_kinds.GoalEvar) }
    in
    let info = Typeclasses.mark_unresolvable info in
    Evd.add evd content info

  let typecheck_evar ev env sigma =
    let info = Evd.find sigma ev in
    let evdref = ref sigma in
    let env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
    let _ = Typing.sort_of env evdref (Evd.evar_concl info) in
    !evdref

  let typecheck_proof c concl env sigma =
    let evdref = ref sigma in
    let () = Typing.check env evdref c concl in
    !evdref

  let refine ?(unsafe = false) f = Goal.enter begin fun gl ->
    let sigma = Goal.sigma gl in
    let env = Goal.env gl in
    let concl = Goal.concl gl in
    (** Save the [future_goals] state to restore them after the
        refinement. *)
    let prev_future_goals = Evd.future_goals sigma in
    let prev_principal_goal = Evd.principal_future_goal sigma in
    (** Create the refinement term *)
    let (sigma, c) = f (Evd.reset_future_goals sigma) in
    let evs = Evd.future_goals sigma in
    let evkmain = Evd.principal_future_goal sigma in
    (** Check that the introduced evars are well-typed *)
    let fold accu ev = typecheck_evar ev env accu in
    let sigma = if unsafe then sigma else List.fold_left fold sigma evs in
    (** Check that the refined term is typesafe *)
    let sigma = if unsafe then sigma else typecheck_proof c concl env sigma in
    (** Proceed to the refinement *)
    let sigma = match evkmain with
      | None -> Evd.define gl.Goal.self c sigma
      | Some evk ->
          let id = Evd.evar_ident gl.Goal.self sigma in
          Evd.rename evk id (Evd.define gl.Goal.self c sigma)
    in
    (** Restore the [future goals] state. *)
    let sigma = Evd.restore_future_goals sigma prev_future_goals prev_principal_goal in
    (** Select the goals *)
    let comb = undefined sigma (List.rev evs) in
    let sigma = List.fold_left mark_as_goal sigma comb in
    Pv.set { solution = Evd.reset_future_goals sigma; comb; }
  end

  (** Useful definitions *)

  let with_type env evd c t =
    let my_type = Retyping.get_type_of env evd c in
    let j = Environ.make_judge c my_type in
    let (evd,j') =
      Coercion.inh_conv_coerce_to true (Loc.ghost) env evd j t
    in
    evd , j'.Environ.uj_val

  let refine_casted ?(unsafe = false) f = Goal.enter begin fun gl ->
    let concl = Goal.concl gl in
    let env = Goal.env gl in
    let f h = let (h, c) = f h in with_type env h c concl in
    refine ~unsafe f
  end
end

module NonLogical = Proofview_monad.NonLogical

let tclLIFT = Proof.lift

let tclCHECKINTERRUPT =
   tclLIFT (NonLogical.make Control.check_for_interrupt)





(*** Compatibility layer with <= 8.2 tactics ***)
module V82 = struct
  type tac = Evar.t Evd.sigma -> Evar.t list Evd.sigma

  let tactic tac =
    (* spiwack: we ignore the dependencies between goals here,
       expectingly preserving the semantics of <= 8.2 tactics *)
    (* spiwack: convenience notations, waiting for ocaml 3.12 *)
    let (>>=) = Proof.bind in
    Pv.get >>= fun ps ->
    try
      let tac gl evd = 
        let glsigma  =
          tac { Evd.it = gl ; sigma = evd; }  in
        let sigma = glsigma.Evd.sigma in
        let g = glsigma.Evd.it in
        ( g, sigma )
      in
        (* Old style tactics expect the goals normalized with respect to evars. *)
      let (initgoals,initevd) =
        Evd.Monad.List.map (fun g s -> GoalV82.nf_evar s g) ps.comb ps.solution
      in
      let (goalss,evd) = Evd.Monad.List.map tac initgoals initevd in
      let sgs = List.flatten goalss in
      Pv.set { solution = evd; comb = sgs; }
    with e when catchable_exception e ->
      let e = Errors.push e in
      tclZERO e


  (* normalises the evars in the goals, and stores the result in
     solution. *)
  let nf_evar_goals =
    Pv.modify begin fun ps ->
    let map g s = GoalV82.nf_evar s g in
    let (goals,evd) = Evd.Monad.List.map map ps.comb ps.solution in
    { solution = evd; comb = goals; }
    end
      
  let has_unresolved_evar pv =
    Evd.has_undefined pv.solution

  (* Main function in the implementation of Grab Existential Variables.*)
  let grab pv =
    let undef = Evd.undefined_map pv.solution in
    let goals = List.rev_map fst (Evar.Map.bindings undef) in
    { pv with comb = goals }
      
    

  (* Returns the open goals of the proofview together with the evar_map to 
     interprete them. *)
  let goals { comb = comb ; solution = solution; } =
   { Evd.it = comb ; sigma = solution }

  let top_goals initial { solution=solution; } =
    let goals = List.map (fun (t,_) -> fst (Term.destEvar t)) initial in
    { Evd.it = goals ; sigma=solution; }

  let top_evars initial =
    let evars_of_initial (c,_) =
      Evar.Set.elements (Evd.evars_of_term c)
    in
    List.flatten (List.map evars_of_initial initial)

  let instantiate_evar n com pv =
    let (evk,_) =
      let evl = Evarutil.non_instantiated pv.solution in
      let evl = Evar.Map.bindings evl in
      if (n <= 0) then
	Errors.error "incorrect existential variable index"
      else if List.length evl < n then
	  Errors.error "not so many uninstantiated existential variables"
      else
	List.nth evl (n-1) 
    in
    { pv with
	solution = Evar_refiner.instantiate_pf_com evk com pv.solution }

  let of_tactic t gls =
    try
      let init = { solution = gls.Evd.sigma ; comb = [gls.Evd.it] } in
      let (_,final,_) = apply (GoalV82.env gls.Evd.sigma gls.Evd.it) t init in
      { Evd.sigma = final.solution ; it = final.comb }
    with Proofview_monad.TacticFailure e as src ->
      let src = Errors.push src in
      let e = Backtrace.app_backtrace ~src ~dst:e in
      raise e

  let put_status = Status.put

  let catchable_exception = catchable_exception

  let wrap_exceptions f =
    try f ()
    with e when catchable_exception e -> let e = Errors.push e in tclZERO e

end
