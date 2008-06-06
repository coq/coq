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
(* arnaud: beaucoup d'occurence de Goal.return ({None,true,false}),
   peut-être tenter de factoriser. *)

open Term
open Names
let (>>=) = Goal.bind

let id_of_name_with_default s = function
  | Anonymous -> id_of_string s
  | Name id   -> id

let default_id decl = 
  Goal.env >>= fun env ->
  Goal.defs >>= fun defs ->
  let sigma = Evd.evars_of defs in
  Goal.return (
    match decl with
    | (name,None,t) ->
	(match Typing.sort_of env sigma t with
	 | Prop _ -> (id_of_name_with_default "H" name)
	 | Type _ -> (id_of_name_with_default "X" name))
    | (name,Some b,_) -> Termops.id_of_name_using_hdchar env b name
  )

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
      (* arnaud: pourquoi est-ce là ? let sigma = Evd.evars_of defs in*)
      default_id decl >>= fun id ->
      Logic.fresh_id idl id
  | IntroBasedOn (id,idl) -> Logic.fresh_id idl id
  | IntroMustBe id        -> 
      Logic.fresh_id [] id >>= fun id' ->
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

let build_intro_tac id move_flag =
  Proofview.sensitive_tactic (
    move_flag >>= function
      | None      -> Goal.return (Logic.intro id)
      | Some dest -> Util.anomaly "Intro.build_intro_tac: Some: à restaurer" (* arnaud: original tclTHEN (introduction id) (move_hyp true id dest)*)
  )
(* arnaud: original
let build_intro_tac id = function
  | None      -> Logic.intro id
  | Some dest -> Util.anomaly "Intro.build_intro_tac: Some: à restaurer" (* arnaud: original tclTHEN (introduction id) (move_hyp true id dest)*)
*)

let find_intro_gen_name name_flag force_flag =
  Goal.concl >>= fun concl ->
  name_flag >>= fun name_flag ->
  force_flag >>= fun force_flag ->
  match kind_of_term concl with
    | Prod (name,t,_) -> 
	find_name (name,None,t) name_flag
    | LetIn (name,b,t,_) ->
	find_name (name,Some b,t) name_flag
    | _ -> 
	if not force_flag then raise (Util.anomaly"Logic.intro_gen: remettre une vrai erreur (IntroNeedsProduct)"(* arnaud:RefinerError IntroNeedsProduct *));
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

let intro_mustbe_force id = 
  let mustbe_id =
    id >>= fun id ->
    Goal.return (IntroMustBe id)
  in
  intro_gen mustbe_id Goal.sNone Goal.strue
let intro_using id = 
  let basedon_id =
    id >>= fun id ->
    Goal.return (IntroBasedOn (id,[]))
  in
  intro_gen basedon_id Goal.sNone Goal.sfalse
let intro_force force_flag = 
  intro_gen (Goal.return (IntroAvoid [])) Goal.sNone force_flag
let intro = intro_force Goal.sfalse
let introf = intro_force Goal.strue

let intro_avoiding l = 
  let avoid_l =
    l >>= fun l ->
    Goal.return (IntroAvoid l)
  in
  intro_gen avoid_l Goal.sNone Goal.sfalse

let introf_move_name destopt = 
  intro_gen (Goal.return (IntroAvoid [])) destopt Goal.strue

(* arnaud: à virer
(* For backwards compatibility *)
let central_intro = intro_gen
*)

let rec intros_using = function
  | []      -> Proofview.tclIDTAC ()
  | id::l  -> Proofview.tclTHEN (intro_using id) (intros_using l)

let intros = Proofview.tclREPEAT (intro_force Goal.sfalse)

let intro_erasing id = Proofview.tclTHEN (Logic.clear (Goal.sensitive_list [id])) 
                                        (Logic.intro id)

let intros_replacing ids = 
  Util.anomaly "Intro.intros_replacing: à restaurer"
  (* arnaud: à restaurer : il manque intro_replacing apparemment
  let rec introrec = function
    | [] -> Proofview.tclIDTAC
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
  | None -> intro_gen (Goal.return (IntroAvoid [])) idopt' Goal.strue
  | Some id -> intro_gen (Goal.return (IntroMustBe id)) idopt' Goal.strue

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
    Goal.sNone

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
  Proofview.sensitive_tactic (
    h >>= fun h ->
    depth_of_quantified_hypothesis red h >>= fun depth ->
    Goal.return (Logic.tclDO depth intro)
  )

let intros_until_id id = 
  let arg = 
    id >>= fun id ->
    Goal.return (Rawterm.NamedHyp id)
  in
  intros_until_gen true arg
let intros_until_n_gen red n = 
  let arg =
      n >>= fun n ->
      Goal.return (Rawterm.AnonHyp n)
  in
  intros_until_gen red arg

let intros_until = intros_until_gen true
let intros_until_n = intros_until_n_gen true
let intros_until_n_wored = intros_until_n_gen false

let try_intros_until tac = 
  Util.anomaly "Intros.try_intros_until: à restaurer"
  (* arnaud: à restaurer:
     Fait parti de sensitive_tactic probablement
     function
  | Rawterm.NamedHyp id -> Proofview.tclTHEN
                               (Logic.tclTRY (intros_until_id id)) 
	                       (tac (Goal.return id))
  | Rawterm.AnonHyp n -> Proofview.tclTHEN (intros_until_n n) (Logic.onLastHyp tac)
  *)

let rec intros_move_gen = function
  | [] -> Proofview.tclIDTAC ()
  | (hyp,destopt) :: rest ->
      Proofview.tclTHEN (intro_gen (Goal.return (IntroMustBe hyp)) (Goal.return destopt) Goal.sfalse)
	               (intros_move_gen rest)

let intros_move l =
  Proofview.sensitive_tactic (
    l >>= fun l -> 
    Goal.return (intros_move_gen l)
  )

let move_to_rhyp rhyp =
  Proofview.sensitive_tactic begin
  let rec get_lhyp lastfixed depdecls = function
    | [] ->
	Goal.return
	(match rhyp with
	   | None -> lastfixed
      	   | Some h -> Util.anomaly ("Hypothesis should occur: "^ (string_of_id h)))
    | (hyp,c,typ) as ht :: rest ->
	Goal.env >>= fun env ->
	if Some hyp = rhyp then 
	  Goal.return lastfixed
	else if List.exists (Termops.occur_var_in_decl env hyp) depdecls then 
	  get_lhyp lastfixed (ht::depdecls) rest
        else
	  get_lhyp (Some hyp) depdecls rest
  in
  Goal.hyps >>= fun hyps ->
  let sign = Environ.named_context_of_val hyps in
  let (hyp,c,typ as decl) = List.hd sign in
  get_lhyp None [decl] (List.tl sign) >>= function
    | None -> Goal.return (Proofview.tclIDTAC ())
    | Some hypto -> Goal.return (Logic.move_hyp true (Goal.return hyp) (Goal.return hypto))
  end

let rec intros_rmove_gen = function
  | [] -> Proofview.tclIDTAC ()
  | (hyp,destopt) :: rest ->
      Logic.tclTHENLIST [ Logic.intro (Goal.return hyp);
 			  move_to_rhyp destopt;
			  intros_rmove_gen rest ]
let intros_rmove l =
  Proofview.sensitive_tactic (
    l >>= fun l ->
    Goal.return (intros_rmove_gen l)
  )
