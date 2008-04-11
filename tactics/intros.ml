(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(************************************************************************)
(*                                                                      *)
(*   This file defines the high-level intro and intros tactic.          *)
(*   Those the user sees.                                               *)
(*                                                                      *)
(************************************************************************)

(* arnaud: remplacer la plupart des Proofview. par des Logic. ? *)

open Term
open Names
let (>>=) = Goal.bind

let fresh_id_avoid avoid id =
  Termops.next_global_ident_away true id avoid

let fresh_id avoid id =
  Goal.hyps >>= fun hyps ->
  let ids = Termops.ids_of_named_context (Environ.named_context_of_val hyps) in
  Goal.return (fresh_id_avoid (avoid@ids) id)

let id_of_name_with_default s = function
  | Anonymous -> id_of_string s
  | Name id   -> id

let default_id env sigma = function
  | (name,None,t) ->
      (match Typing.sort_of env sigma t with
	| Prop _ -> (id_of_name_with_default "H" name)
	| Type _ -> (id_of_name_with_default "X" name))
  | (name,Some b,_) -> Termops.id_of_name_using_hdchar env b name

(* Non primitive introduction tactics are treated by central_intro
   There is possibly renaming, with possibly names to avoid and 
   possibly a move to do after the introduction *)

type intro_name_flag =
  | IntroAvoid of identifier list
  | IntroBasedOn of identifier * identifier list
  | IntroMustBe of identifier

let find_name decl = function
  | IntroAvoid idl -> 
      (* this case must be compatible with [find_intro_names] below. *)
      Goal.env >>= fun env ->
      Goal.defs >>= fun defs ->
      let sigma = Evd.evars_of defs in
      fresh_id idl (default_id env sigma decl)
  | IntroBasedOn (id,idl) -> fresh_id idl id
  | IntroMustBe id        -> 
      fresh_id [] id >>= fun id' ->
      if id' <> id then Proofview.fail (Pp.str ((string_of_id id)^" is already used"));
      Goal.return id'

(* arnaud: à éventuellement restaurer plus tard
(* Returns the names that would be created by intros, without doing
   intros.  This function is supposed to be compatible with an
   iteration of [find_name] above. As [default_id] checks the sort of
   the type to build hyp names, we maintain an environment to be able
   to type dependent hyps. *)
let find_intro_names ctxt gl = 
  let _, res = List.fold_right 
    (fun decl acc -> 
      let wantedname,x,typdecl = decl in
      let env,idl = acc in
      let name = fresh_id idl (default_id env gl.sigma decl) gl in
      let newenv = push_rel (wantedname,x,typdecl) env in
      (newenv,(name::idl)))
    ctxt (pf_env gl , []) in
  List.rev res 
*)

let build_intro_tac id = function
  | None      -> Logic.intro id
  | Some dest -> Util.anomaly "Intro.build_intro_tac: Some: à restaurer" (* arnaud: original tclTHEN (introduction id) (move_hyp true id dest)*)

let find_intro_gen_name name_flag force_flag =
  Goal.concl >>= fun concl ->
  match kind_of_term concl with
    | Prod (name,t,_) -> 
	find_name (name,None,t) name_flag
    | LetIn (name,b,t,_) ->
	find_name (name,Some b,t) name_flag
    | _ -> 
	if not force_flag then raise (Util.anomaly"Logic.intro_gen: remettre une vrai erreur"(* arnaud:RefinerError IntroNeedsProduct *));
	Util.anomaly "Intro.intro_gen: last case: à restaurer"
	(* arnaud: à restaurer: original venant de intro_gen
	try
	  Proofview.tclTHEN
	    (reduce (Red true) onConcl)
	    (intro_gen name_flag move_flag force_flag)
	with Redelimination ->
	  errorlabstrm "Intro" (str "No product even after head-reduction")
	*)

let rec intro_gen name_flag move_flag force_flag =
  build_intro_tac (find_intro_gen_name name_flag force_flag) move_flag

let intro_mustbe_force id = intro_gen (IntroMustBe id) None true
let intro_using id = intro_gen (IntroBasedOn (id,[])) None false
let intro_force force_flag = intro_gen (IntroAvoid []) None force_flag
let intro = intro_force false
let introf = intro_force true

let intro_avoiding l = intro_gen (IntroAvoid l) None false 

let introf_move_name destopt = intro_gen (IntroAvoid []) destopt true

(* arnaud: à virer
(* For backwards compatibility *)
let central_intro = intro_gen
*)

let rec intros_using = function
  | []      -> Proofview.id ()
  | id::l  -> Proofview.tclTHEN (intro_using id) (intros_using l)

let intros = Proofview.tclREPEAT (intro_force false)

let intro_erasing id = Proofview.tclTHEN (Logic.clear (Goal.expr_of_list [id])) 
                                        (Logic.intro id)

let intros_replacing ids = 
  Util.anomaly "Intro.intros_replacing: à restaurer"
  (* arnaud: à restaurer : il manque intro_replacing apparemment
  let rec introrec = function
    | [] -> Proofview.id
    | id::tl ->
	(Proofview.tclTHEN (Proofview.tclORELSE (intro_replacing id)
		    (Proofview.tclORELSE (intro_erasing id)   (* ?? *)
                       (intro_using id)))
           (introrec tl))
  in 
  introrec ids
  *)

let intro_move idopt idopt' = 
  match idopt with
  | None -> intro_gen (IntroAvoid []) idopt' true
  | Some id -> intro_gen (IntroMustBe id) idopt' true

let pf_lookup_hypothesis_as_renamed env ccl = function
  | Rawterm.AnonHyp n -> Detyping.lookup_index_as_renamed env ccl n
  | Rawterm.NamedHyp id -> Detyping.lookup_name_as_renamed env ccl id

let pf_lookup_hypothesis_as_renamed_gen red h =
  Goal.env >>= fun env ->
  Goal.defs >>= fun defs ->
  let sigma = Evd.evars_of defs in
  let rec aux ccl =
    match pf_lookup_hypothesis_as_renamed env ccl h with
      | None when red ->
          aux 
	    ((fst (Redexpr.reduction_of_red_expr (Rawterm.Red true))) 
	       env sigma ccl)
      | x -> x
  in
  try 
    Goal.concl >>= fun concl ->
    Goal.return (aux concl)
  with Tacred.Redelimination -> 
    Goal.return None

let is_quantified_hypothesis id =
  pf_lookup_hypothesis_as_renamed_gen true (Rawterm.NamedHyp id) >>= fun hyp ->
  Goal.return (
    match hyp with
    | Some _ -> true
    | None -> false
  )

open Pp
let msg_quantified_hypothesis = function
  | Rawterm.NamedHyp id -> 
      str "hypothesis " ++ Ppconstr.pr_id id
  | Rawterm.AnonHyp n ->
      int n ++ str (match n with 1 -> "st" | 2 -> "nd" | _ -> "th") ++
      str " non dependent hypothesis"

let depth_of_quantified_hypothesis red h =
  pf_lookup_hypothesis_as_renamed_gen red h >>= fun hyp ->
  Goal.return (
    match hyp with
    | Some depth -> depth
    | None ->
        Proofview.fail ( 
          (str "No " ++ msg_quantified_hypothesis h ++
	  str " in current goal" ++
	  if red then str " even after head-reduction" else mt ())
	)
  )

(* arnaud: faire intros until 0 
   fait dans le trunk. *)
(* arnaud: si il y a un bug là dedans je ne serais pas étonné *)
let intros_until_gen red h =
  Proofview.tactic_of_sensitive_proof_step (
    depth_of_quantified_hypothesis red h >>= fun depth ->
    Proofview.goal_tactic_of_tactic (Logic.tclDO depth intro)
  )

let intros_until_id id = intros_until_gen true (Rawterm.NamedHyp id)
let intros_until_n_gen red n = intros_until_gen red (Rawterm.AnonHyp n)

let intros_until = intros_until_gen true
let intros_until_n = intros_until_n_gen true
let intros_until_n_wored = intros_until_n_gen false

let try_intros_until tac = function
  | Rawterm.NamedHyp id -> Proofview.tclTHEN
                               (Logic.tclTRY (intros_until_id id)) 
	                       (tac (Goal.return id))
  | Rawterm.AnonHyp n -> Proofview.tclTHEN (intros_until_n n) (Logic.onLastHyp tac)

let rec intros_move = function
  | [] -> Proofview.id ()
  | (hyp,destopt) :: rest ->
      Proofview.tclTHEN (intro_gen (IntroMustBe hyp) destopt false)
	               (intros_move rest)

