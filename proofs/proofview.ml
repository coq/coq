(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat

(* The proofview datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a proofview which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with 
   one another, which represents the various subnodes of the proof, together
   with a comb: a datastructure that gives order to some of these nodes, 
   namely the open goals. 
   The natural candidate for the solution is an {!Evd.evar_map}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the proofview
   to be able to return information about the proofview. *)

(* Type of proofviews. *)
type proofview = {
     initial : (Term.constr * Term.types) list;
     solution : Evd.evar_map;
     comb : Goal.goal list
     }

(* Initialises a proofview, the argument is a list of environement, 
   conclusion types, and optional names, creating that many initial goals. *)
let init = 
  let rec aux = function
  | [] ->  { initial = [] ; 
	     solution = Evd.empty ;
	     comb = []
	   }
  | (env,typ)::l -> let { initial = ret ; solution = sol ; comb = comb } =
                           aux l
                         in
                         let ( new_defs , econstr ) = 
			   Evarutil.new_evar sol env typ
			 in
			 let (e,_) = Term.destEvar econstr in
			 let gl = Goal.build e in
			 { initial = (econstr,typ)::ret;
			   solution = new_defs ;
			   comb = gl::comb }
  in
  fun l -> let v = aux l in
    (* Marks all the goal unresolvable for typeclasses. *)
    { v with solution = Typeclasses.mark_unresolvables v.solution }

(* Returns whether this proofview is finished or not. That is,
   if it has empty subgoals in the comb. There could still be unsolved
   subgoaled, but they would then be out of the view, focused out. *)
let finished = function
  | {comb = []} -> true
  | _  -> false

(* Returns the current value of the proofview partial proofs. *)
let return { initial=init; solution=defs }  =
  List.map (fun (c,t) -> (Evarutil.nf_evar defs c , t)) init

(* spiwack: this function should probably go in the Util section,
    but I'd rather have Util (or a separate module for lists)
    raise proper exceptions before *)
(* [IndexOutOfRange] occurs in case of malformed indices
   with respect to list lengths. *)
exception IndexOutOfRange
(* no handler: should not be allowed to reach toplevel *)

(* [list_goto i l] returns a pair of lists [c,t] where
   [c] has length [i] and is the reversed of the [i] first
   elements of [l], and [t] is the rest of the list.
   The idea is to navigate through the list, [c] is then
   seen as the context of the current position. 
   Raises [IndexOutOfRange] if [i > length l]*)
let list_goto = 
  let rec aux acc index = function
    | l when index = 0-> (acc,l)
    | [] -> raise IndexOutOfRange
    | a::q -> aux (a::acc) (index-1) q
  in
  fun i l ->
    if i < 0 then
      raise IndexOutOfRange
    else
      aux [] i l

(* Type of the object which allow to unfocus a view.*)
(* First component is a reverse list of what comes before
   and second component is what goes after (in the expected
   order) *)
type focus_context = Goal.goal list * Goal.goal list

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
  let (left,sub_right) = list_goto (i-1) l in
  let (sub, right) = 
    try 
      Util.list_chop (j-i+1) sub_right 
    with Failure "list_chop" -> 
      Util.errorlabstrm "nth_unproven" (Pp.str"No such unproven subgoal")
  in
  (sub, (left,right))

(* Inverse operation to the previous one. *)
let unfocus_sublist (left,right) s =
  List.rev_append left (s@right)


(* [focus i j] focuses a proofview on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned proofview).
   It returns the focus proof, and a context for the focus trace. *)
let focus i j sp =
  let (new_comb, context) = focus_sublist i j sp.comb in
  ( { sp with comb = new_comb } , context )

(* Unfocuses a proofview with respect to a context. *)
let undefined defs l =
  Option.List.flatten (List.map (Goal.advance defs) l)
let unfocus c sp =
  { sp with comb = undefined sp.solution (unfocus_sublist c sp.comb) }


(* The tactic monad:
   - Tactics are objects which apply a transformation to all
     the subgoals of the current view at the same time. By opposed
     to the old vision of applying it to a single goal. It mostly 
     allows to consider tactic like [reorder] to reorder the goals
     in the current view (which might be useful for the tactic designer)
     (* spiwack: the ordering of goals, though, is perhaps a bit
        brittle. It would be much more interesting to find a more
        robust way to adress goals, I have no idea at this time 
        though*) 
     or global automation tactic for dependent subgoals (instantiating
     an evar has influences on the other goals of the proof in progress,
     not being able to take that into account causes the current eauto
     tactic to fail on some instances where it could succeed).
   - Tactics are a monad ['a tactic], in a sense a tactic can be 
     seens as a function (without argument) which returns a value
     of type 'a and modifies the environement (in our case: the view).
     Tactics of course have arguments, but these are given at the 
     meta-level as OCaml functions.
     Most tactics, in the sense we are used to, return [ () ], that is
     no really interesting values. But some might pass information 
     around; the [(>>--)] and [(>>==)] bind-like construction are the
     main ingredients of this information passing. 
     (* spiwack: I don't know how much all this relates to F. Kirchner and 
        C. Muñoz. I wasn't able to understand how they used the monad
        structure in there developpement.
     *)
     The tactics seen in Coq's Ltac are (for now at least) only 
     [unit tactic], the return values are kept for the OCaml toolkit.
     The operation or the monad are [Proofview.tclUNIT] (which is the 
     "return" of the tactic monad) [Proofview.tclBIND] (which is
     the "bind", also noted [(>=)]) and [Proofview.tclTHEN] (which is a
     specialized bind on unit-returning tactics).
*)

(* type of tactics *)
(* spiwack: double-continuation backtracking monads are reasonable
    folklore for "search" implementations (including Tac interactive prover's
    tactics). Yet it's quite hard to wrap your head around these.
    I recommand reading a few times the "Backtracking, Interleaving, and Terminating
    Monad Transformers" paper by O. Kiselyov, C. Chen, D. Fridman.  
    The peculiar shape of the monadic type is reminiscent of that of the continuation
    monad transformer.
    A good way to get a feel of what's happening is to look at what happens when
    executing [apply (tclUNIT ())]. 
    The disjunction function is unlike that of the LogicT paper, because we want and 
    need to backtrack over state as well as values. Therefore we cannot be
    polymorphic over the inner monad. *)
type proof_step = { goals : Goal.goal list ; defs : Evd.evar_map }
type +'a result = { proof_step : proof_step ;
		                content : 'a }

(* nb=non-backtracking *)
type +'a nb_tactic  = proof_step -> 'a result

(* double-continutation backtracking *)
(* "sk" stands for "success continuation", "fk" for "failure continuation" *)
type 'r fk = exn -> 'r
type (-'a,'r) sk = 'a -> 'r fk -> 'r
type +'a tactic0 = { go : 'r. ('a, 'r nb_tactic) sk -> 'r nb_tactic fk -> 'r nb_tactic }

(* We obtain a tactic by parametrizing with an environment *)
(* spiwack: alternatively the environment could be part of the "nb_tactic" state
    monad. As long as we do not intend to change the environment during a tactic,
    it's probably better here. *)
type +'a tactic = Environ.env -> 'a tactic0

(* unit of [nb_tactic] *)
let nb_tac_unit a step = { proof_step = step ; content = a }

(* Applies a tactic to the current proofview. *)
let apply env t sp  = 
  let start = { goals = sp.comb ; defs = sp.solution } in
  let res = (t env).go (fun a _ step -> nb_tac_unit a step) (fun e _ -> raise e) start in
  let next = res.proof_step in
  {sp with
     solution = next.defs ;
     comb = next.goals
  }

(*** tacticals ***)


(* Unit of the tactic monad *)
let tclUNIT a _ = { go = fun sk fk step -> sk a fk step }

(* Bind operation of the tactic monad *)
let tclBIND t k env = { go = fun sk fk step ->
  (t env).go (fun a fk -> (k a env).go sk fk) fk step
}

(* Interpretes the ";" (semicolon) of Ltac.
   As a monadic operation, it's a specialized "bind"
   on unit-returning tactic (meaning "there is no value to bind") *)
let tclTHEN t1 t2 env = { go = fun sk fk step ->
  (t1 env).go (fun () fk -> (t2 env).go sk fk) fk step
}

(* [tclIGNORE t] has the same operational content as [t],
   but drops the value at the end. *)
let tclIGNORE tac env = { go = fun sk fk step ->
  (tac env).go (fun _ fk -> sk () fk) fk step
}

(* [tclOR t1 t2 = t1] if t1 succeeds and [tclOR t1 t2 = t2] if t1 fails. 
    No interleaving for the moment. *)
(* spiwack: compared to the LogicT paper, we backtrack at the same state
    where [t1] has been called, not the state where [t1] failed. *)
let tclOR t1 t2 env = { go = fun sk fk step ->
  (t1 env).go sk (fun _ _ -> (t2 env).go sk fk step) step
}

(* [tclZERO e] always fails with error message [e]*)
let tclZERO e env = { go = fun _ fk step -> fk e step }


(* Focusing operation on proof_steps. *)
let focus_proof_step i j ps =
  let (new_subgoals, context) = focus_sublist i j ps.goals in
  ( { ps with goals = new_subgoals } , context )

(* Unfocusing operation of proof_steps. *)
let unfocus_proof_step c ps =
  { ps with 
     goals = undefined ps.defs (unfocus_sublist c ps.goals) 
  }

(* Focuses a tactic at a range of subgoals, found by their indices. *)
(* arnaud: bug if 0 goals ! *)
let tclFOCUS i j t env = { go = fun sk fk step ->
  let (focused,context) = focus_proof_step i j step in
  (t env).go (fun a fk step -> sk a fk (unfocus_proof_step context step)) fk focused
}

(* Dispatch tacticals are used to apply a different tactic to each goal under
    consideration. They come in two flavours:
    [tclDISPATCH] takes a list of [unit tactic]-s and build a [unit tactic].
    [tclDISPATCHS] takes a list of ['a sensitive tactic] and returns and returns
    and ['a sensitive tactic] where the ['a sensitive] interpreted in a goal [g]
    corresponds to that of the tactic which created [g].
    It is to be noted that the return value of [tclDISPATCHS ts] makes only
    sense in the goals immediatly built by it, and would cause an anomaly
    is used otherwise. *)
exception SizeMismatch
let _ = Errors.register_handler begin function
  | SizeMismatch -> Util.error "Incorrect number of goals."
  | _ -> raise Errors.Unhandled
end
(* spiwack: we use an parametrised function to generate the dispatch tacticals.
    [tclDISPATCHGEN] takes a [null] argument to generate the return value
    if there are no goal under focus, and a [join] argument to explain how
    the return value at two given lists of subgoals are combined when
    both lists are being concatenated.
    [join] and [null] need be some sort of comutative monoid. *)
let rec tclDISPATCHGEN null join tacs env = { go = fun sk fk step ->
  match tacs,step.goals with
  | [] , [] -> (tclUNIT null env).go sk fk step
  | t::tacs , first::goals -> 
      (tclDISPATCHGEN null join tacs env).go
	begin fun x fk step -> 
	  match Goal.advance step.defs first with
	  | None -> sk x fk step
	  | Some first ->
	    (t env).go 
	      begin fun y fk step' -> 
		sk (join x y) fk { step' with 
			                   goals = step'.goals@step.goals
				         }
	      end 
	      fk 
	      { step with goals = [first] }
	end
	fk
	{ step with goals = goals }
  | _ -> raise SizeMismatch
}

(* takes a tactic which can raise exception and makes it pure by *failing* 
    on with these exceptions. Does not catch anomalies. *)
let purify t = 
  let t' env = { go = fun sk fk step -> try (t env).go (fun x -> sk (Util.Inl x)) fk step
     	                                                     with Util.Anomaly _ as e -> raise e
							           | e -> sk (Util.Inr e) fk step
	       }
  in
  tclBIND t' begin function
    | Util.Inl x -> tclUNIT x
    | Util.Inr e -> tclZERO e
  end
let tclDISPATCHGEN null join tacs = purify (tclDISPATCHGEN null join tacs)

let unitK () () = ()
let tclDISPATCH = tclDISPATCHGEN () unitK

let extend_to_list =
  let rec copy n x l =
    if n < 0 then raise SizeMismatch
    else if n = 0 then l
    else copy (n-1) x (x::l)
  in
  fun startxs rx endxs l ->
    let ns = List.length startxs in
    let ne = List.length endxs in
    let n = List.length l in
    startxs@(copy (n-ne-ns) rx endxs)
let tclEXTEND tacs1 rtac tacs2 env = { go = fun sk fk step -> 
  let tacs = extend_to_list tacs1 rtac tacs2 step.goals in
  (tclDISPATCH tacs env).go sk fk step
}

(* [tclGOALBIND] and [tclGOALBINDU] are sorts of bind which take a
    [Goal.sensitive] as a first argument, the tactic then acts on each goal separately.
    Allows backtracking between goals. *)
let list_of_sensitive s k env step =
  Goal.list_map begin fun defs g ->
    let (a,defs) = Goal.eval s env defs g in
    (k a) , defs
  end step.goals step.defs
(* In form of a tactic *)
let list_of_sensitive s k env = { go = fun sk fk step ->
  let (tacs,defs) = list_of_sensitive s k env step in
  sk tacs fk { step with defs = defs } 
}

(* This is a helper function for the dispatching tactics (like [tclGOALBIND] and
    [tclDISPATCHS]). It takes an ['a sensitive] value, and returns a tactic
    whose return value is, again, ['a sensitive] but only has value in the
    (unmodified) goals under focus. *)
let here_s b env = { go = fun sk fk step ->
  sk (Goal.bind (Goal.here_list step.goals b) (fun b -> b)) fk step
}

let rec tclGOALBIND s k = 
  (* spiwack: the first line ensures that the value returned by the tactic [k] will
      not "escape its scope". *)
  let k a = tclBIND (k a) here_s in
  purify begin 
    tclBIND (list_of_sensitive s k) begin fun tacs ->
      tclDISPATCHGEN Goal.null Goal.plus tacs
    end 
  end

(* spiwack: this should probably be moved closer to the [tclDISPATCH] tactical. *)
let tclDISPATCHS tacs = 
  let tacs = 
    List.map begin fun tac -> 
      tclBIND tac here_s
    end tacs 
  in
  purify begin 
    tclDISPATCHGEN Goal.null Goal.plus tacs
  end

let rec tclGOALBINDU s k = 
  purify begin 
    tclBIND (list_of_sensitive s k) begin fun tacs ->
      tclDISPATCHGEN () unitK tacs
    end
  end

(* spiwack: up to a few details, same errors are in the Logic module.
    this should be maintained synchronized, probably. *)
open Pretype_errors
let rec catchable_exception = function
  | Loc.Exc_located(_,e) -> catchable_exception e
  | Util.UserError _
  | Type_errors.TypeError _ | PretypeError (_,_,TypingError _)
  | Indrec.RecursionSchemeError _
  | Nametab.GlobalizationError _ | PretypeError (_,_,VarNotFound _)
  (* unification errors *)
  | PretypeError(_,_,(CannotUnify _|CannotUnifyLocal _|CannotGeneralize _
		   |NoOccurrenceFound _|CannotUnifyBindingType _|NotClean _
		   |CannotFindWellTypedAbstraction _
		   |UnsolvableImplicit _)) -> true
  | Typeclasses_errors.TypeClassError 
      (_, Typeclasses_errors.UnsatisfiableConstraints _) -> true
  | _ -> false

(* No backtracking can happen here, hence, as opposed to the dispatch tacticals,
    everything is done in one step. *)
let sensitive_on_step s env step =
  let wrap g ((defs, partial_list) as partial_res) = 
    match Goal.advance defs g with
    | None ->partial_res
    | Some g ->
      let {Goal.subgoals = sg } , d' = Goal.eval s env defs g in
      (d',sg::partial_list)
  in
  let ( new_defs , combed_subgoals ) = 
    List.fold_right wrap step.goals (step.defs,[])
  in
  { defs = new_defs;
     goals = List.flatten combed_subgoals }
let tclSENSITIVE s =
  purify begin
    fun env -> { go = fun sk fk step -> sk () fk (sensitive_on_step s env step) }
  end

module Notations = struct
  let (>-) = Goal.bind
  let (>>-) = tclGOALBINDU
  let (>>--) = tclGOALBIND
  let (>=) = tclBIND
  let (>>=) t k = t >= fun s -> s >>- k
  let (>>==) t k = t >= fun s -> s >>-- k
  let (<*>) = tclTHEN
  let (<+>) = tclOR
end

(*** Compatibility layer with <= 8.2 tactics ***)
module V82 = struct
  type tac = Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

  let tactic tac _ = { go = fun sk fk ps ->
    (* spiwack: we ignore the dependencies between goals here, expectingly
         preserving the semantics of <= 8.2 tactics *)
    let tac evd gl = 
      let glsigma  = tac { Evd.it = gl ; Evd.sigma = evd }  in
      let sigma = glsigma.Evd.sigma in
      let g = glsigma.Evd.it in
      ( g , sigma )
    in
    (* Old style tactics expect the goals normalized with respect to evars. *)
    let (initgoals,initevd) = 
      Goal.list_map Goal.V82.nf_evar ps.goals ps.defs
    in
    let (goalss,evd) = Goal.list_map tac initgoals initevd in
    let sgs = List.flatten goalss in
    sk () fk { defs = evd ; goals = sgs }
}

  let has_unresolved_evar pv =
    Evd.has_undefined pv.solution

  (* Returns the open goals of the proofview together with the evar_map to 
     interprete them. *)
  let goals { comb = comb ; solution = solution } = 
    { Evd.it = comb ; sigma = solution}

  let top_goals { initial=initial ; solution=solution } = 
    let goals = List.map (fun (t,_) -> Goal.V82.build (fst (Term.destEvar t))) initial in
    { Evd.it = goals ; sigma=solution }

  let instantiate_evar n com pv =
    let (evk,_) = 
      let evl = Evarutil.non_instantiated pv.solution in
     if (n <= 0) then
	Util.error "incorrect existential variable index"
      else if List.length evl < n then
	  Util.error "not so many uninstantiated existential variables"
      else
	List.nth evl (n-1) 
    in
    { pv with
	solution = Evar_refiner.instantiate_pf_com evk com pv.solution }

  let purify = purify
end
