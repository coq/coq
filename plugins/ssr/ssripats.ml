(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ssrmatching_plugin

open Util
open Names
open Constr
open Context

open Proofview
open Proofview.Notations

open Ssrast

type ssriop =
  | IOpId of Names.Id.t
  | IOpDrop
  | IOpTemporay
  | IOpInaccessible of string option
  | IOpInaccessibleAll
  | IOpAbstractVars of Names.Id.t list
  | IOpFastNondep

  | IOpInj of ssriops list

  | IOpDispatchBlock of id_block
  | IOpDispatchBranches of ssriops list

  | IOpCaseBlock of id_block
  | IOpCaseBranches of ssriops list

  | IOpRewrite of ssrocc * ssrdir
  | IOpView of ssrclear option * ssrview (* extra clears to be performed *)

  | IOpClear of ssrclear * ssrhyp option (* must clear, may clear *)
  | IOpSimpl of ssrsimpl

  | IOpEqGen of unit Proofview.tactic (* generation of eqn *)

  | IOpNoop

and ssriops = ssriop list

let rec pr_ipatop = function
  | IOpId id -> Names.Id.print id
  | IOpDrop -> Pp.str "_"
  | IOpTemporay -> Pp.str "+"
  | IOpInaccessible None -> Pp.str "?"
  | IOpInaccessible (Some s) -> Pp.str ("?«"^s^"»")
  | IOpInaccessibleAll -> Pp.str "*"
  | IOpAbstractVars l -> Pp.str ("[:"^String.concat " " (List.map Names.Id.to_string l)^"]")
  | IOpFastNondep -> Pp.str ">"

  | IOpInj l -> Pp.(str "[=" ++ ppl l ++ str "]")

  | IOpDispatchBlock b -> Pp.(str"(" ++ Ssrprinters.pr_block b ++ str")")
  | IOpDispatchBranches l -> Pp.(str "(" ++ ppl l ++ str ")")

  | IOpCaseBlock b -> Pp.(str"[" ++ Ssrprinters.pr_block b ++ str"]")
  | IOpCaseBranches l -> Pp.(str "[" ++ ppl l ++ str "]")

  | IOpRewrite (occ,dir) -> Pp.(Ssrprinters.(pr_occ occ ++ pr_dir dir))
  | IOpView (None,vs) -> Pp.(prlist_with_sep mt (fun c -> str "/" ++ Ssrprinters.pr_ast_closure_term c) vs)
  | IOpView (Some cl,vs) -> Pp.(Ssrprinters.pr_clear Pp.spc cl ++ prlist_with_sep mt (fun c -> str "/" ++ Ssrprinters.pr_ast_closure_term c) vs)

  | IOpClear (clmust,clmay) ->
      Pp.(Ssrprinters.pr_clear spc clmust ++
            match clmay with
            | Some cl -> str "(try " ++ Ssrprinters.pr_clear spc [cl] ++ str")"
            | None -> mt ())
  | IOpSimpl s -> Ssrprinters.pr_simpl s

  | IOpEqGen _ -> Pp.str "E:"
  | IOpNoop -> Pp.str"-"
and ppl x = Pp.(prlist_with_sep (fun () -> str"|") (prlist_with_sep spc pr_ipatop)) x


module IpatMachine : sig

  (* the => tactical.  ?eqtac is a tactic to be eventually run
   * after the first [..] block.  first_case_is_dispatch is the
   * ssr exception to elim: and case: *)
  val main : ?eqtac:unit tactic -> first_case_is_dispatch:bool ->
        ssriops -> unit tactic

  val tclCompileIPats : ssripats -> ssriops

  val tclSEED_SUBGOALS : Names.Name.t list array -> unit tactic -> unit tactic

end = struct (* {{{ *)

module State : sig

  type delayed_gen = {
    tmp_id : Id.t;    (* Temporary name *)
    orig_name : Name.t   (* Old name *)
  }

  (* to_clear API *)
  val isCLR_PUSH    : Id.t -> unit tactic
  val isCLR_PUSHL   : Id.t list -> unit tactic
  val isCLR_CONSUME : unit tactic

  (* to_generalize API *)
  val isGEN_PUSH    : delayed_gen -> unit tactic
  val isGEN_CONSUME : unit tactic

  (* name_seed API *)
  val isNSEED_SET : Names.Name.t list -> unit tactic
  val isNSEED_CONSUME : (Names.Name.t list option -> unit tactic) -> unit tactic

  (* Some data may expire *)
  val isTICK : ssriop -> unit tactic

  val isPRINT : Proofview.Goal.t -> Pp.t

end = struct (* {{{ *)

type istate = {

  (* Delayed clear *)
  to_clear : Id.t list;

  (* Temporary intros, to be generalized back *)
  to_generalize : delayed_gen list;

  (* The type of the inductive constructor corresponding to the current proof
   * branch: name seeds are taken from that in an intro block *)
  name_seed : Names.Name.t list option;

}
and delayed_gen = {
  tmp_id : Id.t;    (* Temporary name *)
  orig_name : Name.t   (* Old name *)
}

let empty_state = {
  to_clear = [];
  to_generalize = [];
  name_seed = None;
}

include Ssrcommon.MakeState(struct
  type state = istate
  let init = empty_state
end)

let print_name_seed env sigma = function
  | None -> Pp.str "-"
  | Some nl -> Pp.prlist Names.Name.print nl

let print_delayed_gen { tmp_id; orig_name } =
  Pp.(Id.print tmp_id ++ str"->" ++ Name.print orig_name)

let isPRINT g =
  let env, sigma = Goal.env g, Goal.sigma g in
  let state = get g in
  Pp.(str"{{ to_clear: " ++
        prlist_with_sep spc Id.print state.to_clear ++ spc () ++
      str"to_generalize: " ++
        prlist_with_sep spc print_delayed_gen state.to_generalize ++ spc () ++
      str"name_seed: " ++ print_name_seed env sigma state.name_seed ++ str" }}")


let isCLR_PUSH id =
  tclGET (fun ({ to_clear = ids } as s) ->
  tclSET { s with to_clear = id :: ids })

let isCLR_PUSHL more_ids =
  tclGET (fun ({ to_clear = ids } as s) ->
  tclSET { s with to_clear = more_ids @ ids })

let isCLR_CONSUME =
  tclGET (fun ({ to_clear = ids } as s) ->
  tclSET { s with to_clear = [] } <*>
  Tactics.clear ids)


let isGEN_PUSH dg =
  tclGET (fun s ->
  tclSET { s with to_generalize = dg :: s.to_generalize })

(* generalize `id` as `new_name` *)
let gen_astac id new_name =
 let gen = ((None,Some(false,[])),Ssrmatching.cpattern_of_id id) in
 V82.tactic (Ssrcommon.gentac gen)
 <*> Ssrcommon.tclRENAME_HD_PROD new_name

(* performs and resets all delayed generalizations *)
let isGEN_CONSUME =
  tclGET (fun ({ to_generalize = dgs } as s) ->
  tclSET { s with to_generalize = [] } <*>
  Tacticals.New.tclTHENLIST
    (List.map (fun { tmp_id; orig_name } ->
       gen_astac tmp_id orig_name) dgs) <*>
  Tactics.clear (List.map (fun gen -> gen.tmp_id) dgs))


let isNSEED_SET ty =
  tclGET (fun s ->
  tclSET { s with name_seed = Some ty })

let isNSEED_CONSUME k =
  tclGET (fun ({ name_seed = x } as s) ->
  tclSET { s with name_seed = None } <*>
  k x)

let isTICK = function
  | IOpSimpl _ | IOpClear _ -> tclUNIT ()
  | _ -> tclGET (fun s -> tclSET { s with name_seed = None })

end (* }}} *************************************************************** *)

open State

(***[=> *] ****************************************************************)
(** [nb_assums] returns the number of dependent premises
    Warning: unlike [nb_deps_assums], it does not perform reduction *)
let rec nb_assums cur env sigma t =
  match EConstr.kind sigma t with
  | Prod(name,ty,body) ->
     nb_assums (cur+1) env sigma body
  | LetIn(name,ty,t1,t2) ->
    nb_assums (cur+1) env sigma t2
  | Cast(t,_,_) ->
     nb_assums cur env sigma t
  | _ -> cur
let nb_assums = nb_assums 0

let intro_anon_all = Goal.enter begin fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let g = Goal.concl gl in
  let n = nb_assums env sigma g in
  Tacticals.New.tclDO n (Ssrcommon.tclINTRO_ANON ())
end

(*** [=> >*] **************************************************************)
(** [nb_deps_assums] returns the number of dependent premises *)
let rec nb_deps_assums cur env sigma t =
  let t' = Reductionops.whd_allnolet env sigma t in
  match EConstr.kind sigma t' with
  | Constr.Prod(name,ty,body) ->
     if EConstr.Vars.noccurn sigma 1 body &&
        not (Typeclasses.is_class_type sigma ty) then cur
     else nb_deps_assums (cur+1) env sigma body
  | Constr.LetIn(name,ty,t1,t2) ->
     nb_deps_assums (cur+1) env sigma t2
  | Constr.Cast(t,_,_) ->
     nb_deps_assums cur env sigma t
  | _ -> cur
let nb_deps_assums = nb_deps_assums 0

let intro_anon_deps = Goal.enter begin fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let g = Goal.concl gl in
  let n = nb_deps_assums env sigma g in
  Tacticals.New.tclDO n (Ssrcommon.tclINTRO_ANON ())
end

(** [intro_drop] behaves like [intro_anon] but registers the id of the
    introduced assumption for a delayed clear. *)
let intro_drop =
  Ssrcommon.tclINTRO ~id:Ssrcommon.Anon
    ~conclusion:(fun ~orig_name:_ ~new_name -> isCLR_PUSH new_name)

(** [intro_temp] behaves like [intro_anon] but registers the id of the
    introduced assumption for a regeneralization. *)
let intro_anon_temp =
  Ssrcommon.tclINTRO ~id:Ssrcommon.Anon
    ~conclusion:(fun ~orig_name ~new_name ->
      isGEN_PUSH { tmp_id = new_name; orig_name })

(** [intro_end] performs the actions that have been delayed. *)
let intro_end =
  Ssrcommon.tcl0G ~default:() (isCLR_CONSUME <*> isGEN_CONSUME)

(** [=> _] *****************************************************************)
let intro_clear ids =
  Goal.enter begin fun gl ->
    let _, clear_ids, ren =
      List.fold_left (fun (used_ids, clear_ids, ren) id ->
            let new_id = Ssrcommon.mk_anon_id (Id.to_string id) used_ids in
            (new_id :: used_ids, new_id :: clear_ids, (id, new_id) :: ren))
                     (Tacmach.New.pf_ids_of_hyps gl, [], []) ids
    in
    Tactics.rename_hyp ren <*>
    isCLR_PUSHL clear_ids
end

let tacCHECK_HYPS_EXIST hyps = Goal.enter begin fun gl ->
  let ctx = Goal.hyps gl in
  List.iter (Ssrcommon.check_hyp_exists ctx) hyps;
  tclUNIT ()
end

let tacFILTER_HYP_EXIST hyps k = Goal.enter begin fun gl ->
  let ctx = Goal.hyps gl in
  k (Option.bind hyps (fun h ->
      if Ssrcommon.test_hyp_exists ctx h &&
         Ssrcommon.(not_section_id (hyp_id h)) then Some h else None))
end

(** [=> []] *****************************************************************)

(* calls t1 then t2 on each subgoal passing to t2 the index of the current
 * subgoal (starting from 0) as well as the number of subgoals *)
let tclTHENin t1 t2 =
  tclUNIT () >>= begin fun () -> let i = ref (-1) in
  t1 <*> numgoals >>= fun n ->
  Goal.enter begin fun g -> incr i; t2 !i n end
end

(* Attaches one element of `seeds` to each of the last k goals generated by
`tac`, where k is the size of `seeds` *)
let tclSEED_SUBGOALS seeds tac =
  tclTHENin tac (fun i n ->
          Ssrprinters.ppdebug (lazy Pp.(str"seeding"));
      (* eg [case: (H _ : nat)] generates 3 goals:
         - 1 for _
         - 2 for the nat constructors *)
    let extra_goals = n - Array.length seeds in
    if i < extra_goals then tclUNIT ()
    else isNSEED_SET seeds.(i - extra_goals))

let tac_case t =
  Goal.enter begin fun _ ->
    Ssrcommon.tacTYPEOF t >>= fun ty ->
    Ssrcommon.tacIS_INJECTION_CASE ~ty t >>= fun is_inj ->
    if is_inj then
      V82.tactic ~nf_evars:false (Ssrelim.perform_injection t)
    else
      Goal.enter begin fun g ->
         (Ssrelim.casetac t (fun ?seed k ->
           match seed with
           | None -> k
           | Some seed -> tclSEED_SUBGOALS seed k))
      end
end

(** [=> [^ seed ]] *********************************************************)
let tac_intro_seed interp_ipats fix = Goal.enter begin fun gl ->
  isNSEED_CONSUME begin fun seeds ->
    let seeds =
      Ssrcommon.option_assert_get seeds Pp.(str"tac_intro_seed: no seed") in
    let ipats = List.map (function
       | Anonymous ->
           let s = match fix with
             | Prefix id ->  Id.to_string id ^ "?"
             | SuffixNum n -> "?" ^ string_of_int n
             | SuffixId id -> "?" ^ Id.to_string id in
           IOpInaccessible (Some s)
       | Name id ->
           let s = match fix with
             | Prefix fix ->  Id.to_string fix ^ Id.to_string id
             | SuffixNum n -> Id.to_string id ^ string_of_int n
             | SuffixId fix -> Id.to_string id ^ Id.to_string fix in
           IOpId (Id.of_string s)) seeds in
    interp_ipats ipats
end end

(*** [=> [: id]] ************************************************************)
let mk_abstract_id =
  let open Coqlib in
  let ssr_abstract_id = Summary.ref ~name:"SSR:abstractid" 0 in
begin fun env sigma ->
  let sigma, zero = EConstr.fresh_global env sigma (lib_ref "num.nat.O") in
  let sigma, succ = EConstr.fresh_global env sigma (lib_ref "num.nat.S") in
  let rec nat_of_n n =
    if n = 0 then zero
    else EConstr.mkApp (succ, [|nat_of_n (n-1)|]) in
  incr ssr_abstract_id;
  sigma, nat_of_n !ssr_abstract_id
end

let tclMK_ABSTRACT_VAR id = Goal.enter begin fun gl ->
  let env, concl = Goal.(env gl, concl gl) in
  let step = begin fun sigma ->
    let (sigma, (abstract_proof, abstract_ty)) =
      let (sigma, (ty, _)) =
        Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
      let (sigma, ablock) = Ssrcommon.mkSsrConst "abstract_lock" env sigma in
      let (sigma, lock) = Evarutil.new_evar env sigma ablock in
      let (sigma, abstract) = Ssrcommon.mkSsrConst "abstract" env sigma in
      let (sigma, abstract_id) = mk_abstract_id env sigma in
      let abstract_ty = EConstr.mkApp(abstract, [|ty; abstract_id; lock|]) in
      let sigma, m = Evarutil.new_evar env sigma abstract_ty in
      sigma, (m, abstract_ty) in
    let sigma, kont =
      let rd = Context.Rel.Declaration.LocalAssum (make_annot (Name id) Sorts.Relevant, abstract_ty) in
      let sigma, ev = Evarutil.new_evar (EConstr.push_rel rd env) sigma concl in
      sigma, ev
    in
    let term =
      EConstr.(mkApp (mkLambda(make_annot (Name id) Sorts.Relevant,abstract_ty,kont),[|abstract_proof|])) in
    let sigma, _ = Typing.type_of env sigma term in
    sigma, term
  end in
  Tactics.New.refine ~typecheck:false step <*>
  tclFOCUS 1 3 Proofview.shelve
end

let tclMK_ABSTRACT_VARS ids =
  List.fold_right (fun id tac ->
    Tacticals.New.tclTHENFIRST (tclMK_ABSTRACT_VAR id) tac) ids (tclUNIT ())

(* Debugging *)
let tclLOG p t =
  tclUNIT () >>= begin fun () ->
    Ssrprinters.ppdebug (lazy Pp.(str "exec: " ++ pr_ipatop p));
    tclUNIT ()
  end <*>
  Goal.enter begin fun g ->
    Ssrprinters.ppdebug (lazy Pp.(str" on state:" ++ spc () ++
      isPRINT g ++
      str" goal:" ++ spc () ++ Printer.pr_goal (Goal.print g)));
    tclUNIT ()
  end
  <*>
    t p
  >>= fun ret ->
  Goal.enter begin fun g ->
    Ssrprinters.ppdebug (lazy Pp.(str "done: " ++ isPRINT g));
    tclUNIT ()
  end
  >>= fun () -> tclUNIT ret

let notTAC = tclUNIT false

let duplicate_clear =
  CWarnings.create ~name:"duplicate-clear" ~category:"ssr"
    (fun id -> Pp.(str "Duplicate clear of " ++ Id.print id))

(* returns true if it was a tactic (eg /ltac:tactic) *)
let rec ipat_tac1 ipat : bool tactic =
  match ipat with
  | IOpView (glued_clear,l) ->
      let clear_if_id, extra_clear =
        match glued_clear with
        | None -> false, []
        | Some x -> true, List.map Ssrcommon.hyp_id x in
      Ssrview.tclIPAT_VIEWS
        ~views:l ~clear_if_id
        ~conclusion:(fun ~to_clear:clr ->
            let inter = CList.intersect Id.equal clr extra_clear in
            List.iter duplicate_clear inter;
            let cl = CList.union Id.equal clr extra_clear in
            intro_clear cl)

  | IOpDispatchBranches ipatss ->
      tclDISPATCH (List.map ipat_tac ipatss) <*> notTAC
  | IOpDispatchBlock id_block ->
      tac_intro_seed ipat_tac id_block <*> notTAC
  | IOpCaseBlock id_block ->
      Ssrcommon.tclWITHTOP tac_case <*> tac_intro_seed ipat_tac id_block <*> notTAC

  | IOpCaseBranches ipatss ->
     tclIORPAT (Ssrcommon.tclWITHTOP tac_case) ipatss <*> notTAC

  | IOpId id -> Ssrcommon.tclINTRO_ID id <*> notTAC
  | IOpFastNondep -> intro_anon_deps <*> notTAC
  | IOpDrop -> intro_drop <*> notTAC
  | IOpInaccessible seed -> Ssrcommon.tclINTRO_ANON ?seed () <*> notTAC
  | IOpInaccessibleAll -> intro_anon_all <*> notTAC
  | IOpTemporay -> intro_anon_temp <*> notTAC

  | IOpSimpl Nop -> assert false

  | IOpInj ipatss ->
     tclIORPAT (Ssrcommon.tclWITHTOP
       (fun t -> V82.tactic  ~nf_evars:false (Ssrelim.perform_injection t)))
       ipatss
     <*> notTAC

  | IOpClear (must,may) ->
      tacCHECK_HYPS_EXIST must <*>
      tacFILTER_HYP_EXIST may (fun may ->
        let must = List.map Ssrcommon.hyp_id must in
        let cl = Option.fold_left (fun cls (SsrHyp(_,id)) ->
          if CList.mem_f Id.equal id cls then begin
            duplicate_clear id;
            cls
          end else id :: cls) must may in
        intro_clear cl) <*>
      notTAC

  | IOpSimpl x ->
      V82.tactic ~nf_evars:false (Ssrequality.simpltac x) <*> notTAC

  | IOpRewrite (occ,dir) ->
     Ssrcommon.tclWITHTOP
       (fun x -> V82.tactic  ~nf_evars:false (Ssrequality.ipat_rewrite occ dir x)) <*> notTAC

  | IOpAbstractVars ids -> tclMK_ABSTRACT_VARS ids <*> notTAC

  | IOpEqGen t -> t <*> notTAC
  | IOpNoop -> notTAC

and ipat_tac pl : unit tactic =
  match pl with
  | [] -> tclUNIT ()
  | pat :: pl ->
      Ssrcommon.tcl0G ~default:false (tclLOG pat ipat_tac1) >>= fun was_tac ->
      isTICK pat (* drops expired seeds *) >>= fun () ->
      if was_tac then (* exception *)
        let ip_before, case, ip_after = split_at_first_case pl in
        let case = ssr_exception true case in
        let case = option_to_list case in
        ipat_tac (ip_before @ case @ ip_after)
      else ipat_tac pl

and tclIORPAT tac = function
  | [[]] -> tac
  | p -> Tacticals.New.tclTHENS tac (List.map ipat_tac p)

and ssr_exception is_on = function
  | Some (IOpCaseBranches [[]]) when is_on -> Some IOpNoop
  | Some (IOpCaseBranches l) when is_on ->
      Some (IOpDispatchBranches l)
  | Some (IOpCaseBlock s) when is_on ->
      Some (IOpDispatchBlock s)
  | x -> x

and option_to_list = function None -> [] | Some x -> [x]

and split_at_first_case ipats =
  let rec loop acc = function
    | (IOpSimpl _ | IOpClear _) as x :: rest -> loop (x :: acc) rest
    | (IOpCaseBlock _ | IOpCaseBranches _
      | IOpDispatchBlock _ | IOpDispatchBranches _) as x :: xs ->
      CList.rev acc, Some x, xs
    | pats -> CList.rev acc, None, pats
  in
    loop [] ipats
;;

(* Simple pass doing {x}/v ->  /v{x} *)
let tclCompileIPats l =
  let rec elab = function

  | (IPatClear cl) :: (IPatView v) :: rest ->
      (IOpView(Some cl,v)) :: elab rest
  | (IPatClear cl) :: (IPatId id) :: rest ->
      (IOpClear (cl,Some (SsrHyp(None,id)))) :: IOpId id :: elab rest

  (* boring code *)
  | [] -> []

  | IPatId id :: rest -> IOpId id :: elab rest
  | IPatAnon (One hint) ::rest -> IOpInaccessible hint :: elab rest
  | IPatAnon Drop :: rest -> IOpDrop :: elab rest
  | IPatAnon All :: rest -> IOpInaccessibleAll :: elab rest
  | IPatAnon Temporary :: rest -> IOpTemporay :: elab rest
  | IPatAbstractVars vs :: rest -> IOpAbstractVars vs :: elab rest
  | IPatFastNondep :: rest -> IOpFastNondep :: elab rest

  | IPatInj pats :: rest -> IOpInj (List.map elab pats) :: elab rest
  | IPatRewrite(occ,dir) :: rest -> IOpRewrite(occ,dir) :: elab rest
  | IPatView vs :: rest -> IOpView (None,vs) :: elab rest
  | IPatSimpl s :: rest -> IOpSimpl s :: elab rest
  | IPatClear cl :: rest -> IOpClear (cl,None) :: elab rest

  | IPatCase (Block seed) :: rest -> IOpCaseBlock seed :: elab rest
  | IPatCase (Regular bs) :: rest -> IOpCaseBranches (List.map elab bs) :: elab rest
  | IPatDispatch (Block seed) :: rest -> IOpDispatchBlock seed :: elab rest
  | IPatDispatch (Regular bs) :: rest -> IOpDispatchBranches (List.map elab bs) :: elab rest
  | IPatNoop :: rest -> IOpNoop :: elab rest

  in
  elab l
;;
let tclCompileIPats l =
  Ssrprinters.ppdebug (lazy Pp.(str "tclCompileIPats input: " ++
                                  prlist_with_sep spc Ssrprinters.pr_ipat l));
  let ops = tclCompileIPats l in
  Ssrprinters.ppdebug (lazy Pp.(str "tclCompileIPats output: " ++
                                  prlist_with_sep spc pr_ipatop ops));
  ops

let main ?eqtac ~first_case_is_dispatch iops =
  let ip_before, case, ip_after = split_at_first_case iops in
  let case = ssr_exception first_case_is_dispatch case in
  let case = option_to_list case in
  let eqtac = option_to_list (Option.map (fun x -> IOpEqGen x) eqtac) in
  let ipats = ip_before @ case @ eqtac @ ip_after in
  Ssrcommon.tcl0G ~default:() (ipat_tac ipats <*> intro_end)

end (* }}} *)

let tclIPAT_EQ eqtac ip =
  Ssrprinters.ppdebug (lazy Pp.(str "ipat@run: " ++ Ssrprinters.pr_ipats ip));
  IpatMachine.(main ~eqtac ~first_case_is_dispatch:true (tclCompileIPats ip))

let tclIPATssr ip =
  Ssrprinters.ppdebug (lazy Pp.(str "ipat@run: " ++ Ssrprinters.pr_ipats ip));
  IpatMachine.(main ~first_case_is_dispatch:true (tclCompileIPats ip))

let tclCompileIPats = IpatMachine.tclCompileIPats

(* Common code to handle generalization lists along with the defective case *)
let with_defective maintac deps clr = Goal.enter begin fun g ->
  let sigma, concl = Goal.(sigma g, concl g) in
  let top_id =
    match EConstr.kind_of_type sigma concl with
    | Term.ProdType ({binder_name=Name id}, _, _)
      when Ssrcommon.is_discharged_id id -> id
    | _ -> Ssrcommon.top_id in
  let top_gen = Ssrequality.mkclr clr, Ssrmatching.cpattern_of_id top_id in
  Ssrcommon.tclINTRO_ID top_id <*> maintac deps top_gen
end

let with_dgens { dgens; gens; clr } maintac = match gens with
  | [] -> with_defective maintac dgens clr
  | gen :: gens ->
      V82.tactic ~nf_evars:false (Ssrcommon.genstac (gens, clr)) <*> maintac dgens gen

let mkCoqEq env sigma =
  let eq = Coqlib.((build_coq_eq_data ()).eq) in
  let sigma, eq = EConstr.fresh_global env sigma eq in
  eq, sigma

let mkCoqRefl t c env sigma =
  let refl = Coqlib.((build_coq_eq_data()).refl) in
  let sigma, refl = EConstr.fresh_global env sigma refl in
  EConstr.mkApp (refl, [|t; c|]), sigma

(** Intro patterns processing for elim tactic, in particular when used in
    conjunction with equation generation as in [elim E: x] *)
let elim_intro_tac ipats ?seed what eqid ssrelim is_rec clr =
  let intro_eq =
    match eqid with
    | Some (IPatId ipat) when not is_rec ->
       let rec intro_eq () = Goal.enter begin fun g ->
         let sigma, env, concl = Goal.(sigma g, env g, concl g) in
         match EConstr.kind_of_type sigma concl with
         | Term.ProdType (_, src, tgt) -> begin
             match EConstr.kind_of_type sigma src with
             | Term.AtomicType (hd, _) when Ssrcommon.is_protect hd env sigma ->
                V82.tactic ~nf_evars:false Ssrcommon.unprotecttac <*>
                Ssrcommon.tclINTRO_ID ipat
             | _ -> Ssrcommon.tclINTRO_ANON () <*> intro_eq ()
             end
         |_ -> Ssrcommon.errorstrm (Pp.str "Too many names in intro pattern")
       end in
       intro_eq ()
    | Some (IPatId ipat) ->
       let intro_lhs = Goal.enter begin fun g ->
         let sigma = Goal.sigma g in
         let elim_name = match clr, what with
           | [SsrHyp(_, x)], _ -> x
           | _, `EConstr(_,_,t) when EConstr.isVar sigma t ->
              EConstr.destVar sigma t
           | _ -> Ssrcommon.mk_anon_id "K" (Tacmach.New.pf_ids_of_hyps g) in
         Tacticals.New.tclFIRST
           [ Ssrcommon.tclINTRO_ID elim_name
           ; Ssrcommon.tclINTRO_ANON ~seed:"K" ()]
       end in
       let rec gen_eq_tac () = Goal.enter begin fun g ->
         let sigma, env, concl = Goal.(sigma g, env g, concl g) in
         let sigma, eq =
           EConstr.fresh_global env sigma (Coqlib.lib_ref "core.eq.type") in
         let ctx, last = EConstr.decompose_prod_assum sigma concl in
         let args = match EConstr.kind_of_type sigma last with
           | Term.AtomicType (hd, args) ->
               if Ssrcommon.is_protect hd env sigma then args
               else Ssrcommon.errorstrm
                  (Pp.str "Too many names in intro pattern")
           | _ -> assert false in
         let case = args.(Array.length args-1) in
         if not(EConstr.Vars.closed0 sigma case)
         then Ssrcommon.tclINTRO_ANON () <*> gen_eq_tac ()
         else
           Ssrcommon.tacTYPEOF case >>= fun case_ty ->
           let open EConstr in
           let refl =
             mkApp (eq, [|Vars.lift 1 case_ty; mkRel 1; Vars.lift 1 case|]) in
           let name = Ssrcommon.mk_anon_id "K" (Tacmach.New.pf_ids_of_hyps g) in

           let new_concl =
             mkProd (make_annot (Name name) Sorts.Relevant, case_ty, mkArrow refl Sorts.Relevant (Vars.lift 2 concl)) in
           let erefl, sigma = mkCoqRefl case_ty case env sigma in
           Proofview.Unsafe.tclEVARS sigma <*>
           Tactics.apply_type ~typecheck:true new_concl [case;erefl]
       end in
       gen_eq_tac () <*>
       intro_lhs <*>
       Ssrcommon.tclINTRO_ID ipat
    | _ -> tclUNIT () in
  let unprotect =
    if eqid <> None && is_rec
    then V82.tactic ~nf_evars:false Ssrcommon.unprotecttac else tclUNIT () in
  begin match seed with
  | None -> ssrelim
  | Some s -> IpatMachine.tclSEED_SUBGOALS s ssrelim end <*>
  tclIPAT_EQ (intro_eq <*> unprotect) ipats
;;

let mkEq dir cl c t n env sigma =
  let open EConstr in
  let eqargs = [|t; c; c|] in
  eqargs.(Ssrequality.dir_org dir) <- mkRel n;
  let eq, sigma = mkCoqEq env sigma in
  let refl, sigma = mkCoqRefl t c env sigma in
  mkArrow (mkApp (eq, eqargs)) Sorts.Relevant (Vars.lift 1 cl), refl, sigma

(** in [tac/v: last gens..] the first (last to be run) generalization is
    "special" in that is it also the main argument of [tac] and is eventually
    to be processed forward with view [v]. The behavior implemented is
    very close to [tac: (v last) gens..] but:
    - [v last] may use a view adaptor
    - eventually clear for [last] is taken into account
    - [tac/v {clr}] is also supported, and [{clr}] is to be run later
    The code here does not "grab" [v last] nor apply [v] to [last], see the
    [tacVIEW_THEN_GRAB] combinator. *)
let tclLAST_GEN ~to_ind ((oclr, occ), t) conclusion = tclINDEPENDENTL begin
  Ssrcommon.tacSIGMA >>= fun sigma0 ->
  Goal.enter_one begin fun g ->
  let pat = Ssrmatching.interp_cpattern sigma0 t None in
  let cl0, env, sigma, hyps = Goal.(concl g, env g, sigma g, hyps g) in
  let cl = EConstr.to_constr ~abort_on_undefined_evars:false sigma cl0 in
  let (c, ucst), cl =
    try Ssrmatching.fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with Ssrmatching.NoMatch -> Ssrmatching.redex_of_pattern env pat, cl in
  let sigma = Evd.merge_universe_context sigma ucst in
  let c, cl = EConstr.of_constr c, EConstr.of_constr cl in
  let clr =
    Ssrcommon.interp_clr sigma (oclr, (Ssrmatching.tag_of_cpattern t,c)) in
  (* Historically in Coq, and hence in ssr, [case t] accepts [t] of type
     [A.. -> Ind] and opens new goals for [A..] as well as for the branches
     of [Ind], see the [~to_ind] argument *)
  if not(Termops.occur_existential sigma c) then
    if Ssrmatching.tag_of_cpattern t = Ssrprinters.xWithAt then
      if not (EConstr.isVar sigma c) then
        Ssrcommon.errorstrm Pp.(str "@ can be used with variables only")
      else match Context.Named.lookup (EConstr.destVar sigma c) hyps with
      | Context.Named.Declaration.LocalAssum _ ->
          Ssrcommon.errorstrm Pp.(str "@ can be used with let-ins only")
      | Context.Named.Declaration.LocalDef (name, b, ty) ->
          Unsafe.tclEVARS sigma <*>
          tclUNIT (true, EConstr.mkLetIn (map_annot Name.mk_name name,b,ty,cl), c, clr)
    else
      Unsafe.tclEVARS sigma <*>
      Ssrcommon.tacMKPROD c cl >>= fun ccl ->
      tclUNIT (false, ccl, c, clr)
  else
    if to_ind && occ = None then
      let _, p, _, ucst' =
        (* TODO: use abs_evars2 *)
        Ssrcommon.pf_abs_evars sigma0 (fst pat, c) in
      let sigma = Evd.merge_universe_context sigma ucst' in
      Unsafe.tclEVARS sigma <*>
      Ssrcommon.tacTYPEOF p >>= fun pty ->
      (* TODO: check bug: cl0 no lift? *)
      let ccl = EConstr.mkProd (make_annot (Ssrcommon.constr_name sigma c) Sorts.Relevant, pty, cl0) in
      tclUNIT (false, ccl, p, clr)
  else
    Ssrcommon.errorstrm Pp.(str "generalized term didn't match")
end end >>= begin
  fun infos -> tclDISPATCH (infos |> List.map conclusion)
end

(** a typical mate of [tclLAST_GEN] doing the job of applying the views [cs]
    to [c] and generalizing the resulting term *)
let tacVIEW_THEN_GRAB ?(simple_types=true)
  vs ~conclusion (is_letin, new_concl, c, clear)
=
  Ssrview.tclWITH_FWD_VIEWS ~simple_types ~subject:c ~views:vs
  ~conclusion:(fun t ->
    Ssrcommon.tacCONSTR_NAME c >>= fun name ->
    Goal.enter_one ~__LOC__ begin fun g ->
      let sigma, env = Goal.sigma g, Goal.env g in
      Ssrcommon.tacMKPROD t ~name
        (Termops.subst_term sigma t (* NOTE: we grab t here *)
          (Termops.prod_applist sigma new_concl [c])) >>=
      conclusion is_letin t clear
    end)

(* Elim views are elimination lemmas, so the eliminated term is not added *)
(* to the dependent terms as for "case", unless it actually occurs in the  *)
(* goal, the "all occurrences" {+} switch is used, or the equation switch  *)
(* is used and there are no dependents.                                    *)

let ssrelimtac (view, (eqid, (dgens, ipats))) =
  let ndefectelimtac view eqid ipats deps gen =
    match view with
    | [v] ->
      Ssrcommon.tclINTERP_AST_CLOSURE_TERM_AS_CONSTR v >>= fun cs ->
      tclDISPATCH (List.map (fun elim ->
          (Ssrelim.ssrelim deps (`EGen gen) ~elim eqid (elim_intro_tac ipats)))
        cs)
    | [] ->
      tclINDEPENDENT
          (Ssrelim.ssrelim deps (`EGen gen) eqid (elim_intro_tac ipats))
    | _ ->
      Ssrcommon.errorstrm
        Pp.(str "elim: only one elimination lemma can be provided")
  in
  with_dgens dgens (ndefectelimtac view eqid ipats)

let ssrcasetac (view, (eqid, (dgens, ipats))) =
  let ndefectcasetac view eqid ipats deps ((_, occ), _ as gen) =
    tclLAST_GEN ~to_ind:true gen (fun (_, cl, c, clear as info) ->
      let conclusion _ vc _clear _cl =
        Ssrcommon.tacIS_INJECTION_CASE vc >>= fun inj ->
        let simple = (eqid = None && deps = [] && occ = None) in
        if simple && inj then
          V82.tactic ~nf_evars:false (Ssrelim.perform_injection vc) <*>
          Tactics.clear (List.map Ssrcommon.hyp_id clear) <*>
          tclIPATssr ipats
        else
        (* macro for "case/v E: x" ---> "case E: x / (v x)" *)
          let deps, clear, occ =
            if view <> [] && eqid <> None && deps = []
            then [gen], [], None
            else deps, clear, occ in
          Ssrelim.ssrelim ~is_case:true deps (`EConstr (clear, occ, vc))
            eqid (elim_intro_tac ipats)
      in
      if view = [] then conclusion false c clear c
      else tacVIEW_THEN_GRAB ~simple_types:false view ~conclusion info)
  in
  with_dgens dgens (ndefectcasetac view eqid ipats)

let ssrscasetoptac = Ssrcommon.tclWITHTOP Ssrelim.ssrscase_or_inj_tac
let ssrselimtoptac = Ssrcommon.tclWITHTOP Ssrelim.elimtac

(** [move] **************************************************************)
let pushmoveeqtac cl c = Goal.enter begin fun g ->
  let env, sigma = Goal.(env g, sigma g) in
  let x, t, cl1 = EConstr.destProd sigma cl in
  let cl2, eqc, sigma = mkEq R2L cl1 c t 1 env sigma in
  Unsafe.tclEVARS sigma <*>
  Tactics.apply_type ~typecheck:true (EConstr.mkProd (x, t, cl2)) [c; eqc]
end

let eqmovetac _ gen =
  Ssrcommon.pfLIFT (Ssrcommon.pf_interp_gen false gen) >>=
  fun (cl, c, _) -> pushmoveeqtac cl c
;;

let rec eqmoveipats eqpat = function
  | (IOpSimpl _ | IOpClear _ as ipat) :: ipats ->
       ipat :: eqmoveipats eqpat ipats
  | (IOpInaccessibleAll :: _ | []) as ipats ->
       IOpInaccessible None :: eqpat @ ipats
  | ipat :: ipats ->
       ipat :: eqpat @ ipats

let ssrsmovetac = Goal.enter begin fun g ->
  let sigma, concl = Goal.(sigma g, concl g) in
  match EConstr.kind sigma concl with
  | Prod _ | LetIn _ -> tclUNIT ()
  | _ -> Tactics.hnf_in_concl
end

let tclIPAT ip =
  IpatMachine.main ~first_case_is_dispatch:false ip

let ssrmovetac = function
  | _::_ as view, (_, ({ gens = lastgen :: gens; clr }, ipats)) ->
     let gentac = V82.tactic ~nf_evars:false (Ssrcommon.genstac (gens, [])) in
     let conclusion _ t clear ccl =
       Tactics.apply_type ~typecheck:true ccl [t] <*>
       Tactics.clear (List.map Ssrcommon.hyp_id clear) in
     gentac <*>
     tclLAST_GEN ~to_ind:false lastgen
       (tacVIEW_THEN_GRAB view ~conclusion) <*>
     tclIPAT (IOpClear (clr,None) :: IpatMachine.tclCompileIPats ipats)
  | _::_ as view, (_, ({ gens = []; clr }, ipats)) ->
      tclIPAT (IOpView (None,view) :: IOpClear (clr,None) :: IpatMachine.tclCompileIPats ipats)
  | _, (Some pat, (dgens, ipats)) ->
    let dgentac = with_dgens dgens eqmovetac in
    dgentac <*> tclIPAT (eqmoveipats (IpatMachine.tclCompileIPats [pat]) (IpatMachine.tclCompileIPats ipats))
  | _, (_, ({ gens = (_ :: _ as gens); dgens = []; clr}, ipats)) ->
    let gentac = V82.tactic ~nf_evars:false (Ssrcommon.genstac (gens, clr)) in
    gentac <*> tclIPAT (IpatMachine.tclCompileIPats ipats)
  | _, (_, ({ clr }, ipats)) ->
    Tacticals.New.tclTHENLIST [ssrsmovetac; Tactics.clear (List.map Ssrcommon.hyp_id clr); tclIPAT (IpatMachine.tclCompileIPats ipats)]

(** [abstract: absvar gens] **************************************************)
let rec is_Evar_or_CastedMeta sigma x =
  EConstr.isEvar sigma x ||
  EConstr.isMeta sigma x ||
  (EConstr.isCast sigma x &&
    is_Evar_or_CastedMeta sigma (pi1 (EConstr.destCast sigma x)))

let occur_existential_or_casted_meta sigma c =
  let rec occrec c = match EConstr.kind sigma c with
    | Evar _ -> raise Not_found
    | Cast (m,_,_) when EConstr.isMeta sigma m -> raise Not_found
    | _ -> EConstr.iter sigma occrec c
  in
  try occrec c; false
  with Not_found -> true

let tacEXAMINE_ABSTRACT id = Ssrcommon.tacTYPEOF id >>= begin fun tid ->
  Ssrcommon.tacMK_SSR_CONST "abstract" >>= fun abstract ->
  Goal.enter_one ~__LOC__ begin fun g ->
  let sigma, env = Goal.(sigma g, env g) in
  let err () =
    Ssrcommon.errorstrm
      Pp.(strbrk"not a proper abstract constant: "++
        Printer.pr_econstr_env env sigma id) in
  if not (EConstr.isApp sigma tid) then err ();
  let hd, args_id = EConstr.destApp sigma tid in
  if not (EConstr.eq_constr_nounivs sigma hd abstract) then err ();
  if Array.length args_id <> 3 then err ();
  if not (is_Evar_or_CastedMeta sigma args_id.(2)) then
    Ssrcommon.errorstrm Pp.(strbrk"abstract constant "++
      Printer.pr_econstr_env env sigma id++str" already used");
  tclUNIT (tid, args_id)
end end

let tacFIND_ABSTRACT_PROOF check_lock abstract_n =
  Ssrcommon.tacMK_SSR_CONST "abstract" >>= fun abstract ->
  Goal.enter_one ~__LOC__ begin fun g ->
    let sigma, env = Goal.(sigma g, env g) in
    let l = Evd.fold_undefined (fun e ei l ->
      match EConstr.kind sigma ei.Evd.evar_concl with
      | App(hd, [|ty; n; lock|])
        when (not check_lock ||
                   (occur_existential_or_casted_meta sigma ty &&
                    is_Evar_or_CastedMeta sigma lock)) &&
             EConstr.eq_constr_nounivs sigma hd abstract &&
             EConstr.eq_constr_nounivs sigma n abstract_n -> e :: l
      | _ -> l) sigma [] in
    match l with
    | [e] -> tclUNIT e
    | _ -> Ssrcommon.errorstrm
       Pp.(strbrk"abstract constant "++
         Printer.pr_econstr_env env sigma abstract_n ++
           strbrk" not found in the evar map exactly once. "++
           strbrk"Did you tamper with it?")
end

let ssrabstract dgens =
  let main _ (_,cid) = Goal.enter begin fun g ->
    Ssrcommon.tacMK_SSR_CONST "abstract" >>= fun abstract ->
    Ssrcommon.tacMK_SSR_CONST "abstract_key" >>= fun abstract_key ->
    Ssrcommon.tacINTERP_CPATTERN cid >>= fun cid ->
    let id = EConstr.mkVar (Option.get (Ssrmatching.id_of_pattern cid)) in
    tacEXAMINE_ABSTRACT id >>= fun (idty, args_id) ->
    let abstract_n = args_id.(1) in
    tacFIND_ABSTRACT_PROOF true abstract_n >>= fun abstract_proof ->
    let tacFIND_HOLE = Goal.enter_one ~__LOC__ begin fun g ->
      let sigma, env, concl = Goal.(sigma g, env g, concl g) in
      let t = args_id.(0) in
      match EConstr.kind sigma t with
      | (Evar _ | Meta _) -> Ssrcommon.tacUNIFY concl t <*> tclUNIT id
      | Cast(m,_,_)
        when EConstr.isEvar sigma m || EConstr.isMeta sigma m ->
          Ssrcommon.tacUNIFY concl t <*> tclUNIT id
      | _ ->
          Ssrcommon.errorstrm
            Pp.(strbrk"abstract constant "++
               Printer.pr_econstr_env env sigma abstract_n ++
               strbrk" has an unexpected shape. Did you tamper with it?")
      end in
    tacFIND_HOLE >>= fun proof ->
    Ssrcommon.tacUNIFY abstract_key args_id.(2) <*>
    Ssrcommon.tacTYPEOF idty >>= fun _ ->
    Unsafe.tclGETGOALS >>= fun goals ->
    (* Here we jump in the proof tree: we move from the current goal to
       the evar that inhabits the abstract variable with the current goal *)
    Unsafe.tclSETGOALS
      (goals @ [Proofview_monad.with_empty_state abstract_proof]) <*>
    tclDISPATCH [
      Tacticals.New.tclSOLVE [Tactics.apply proof];
      Ssrcommon.unfold[abstract;abstract_key]
    ]
  end in
  let interp_gens { gens } ~conclusion = Goal.enter begin fun g ->
   Ssrcommon.tacSIGMA >>= fun gl0 ->
     let open Ssrmatching in
     let ipats = List.map (fun (_,cp) ->
       match id_of_pattern (interp_cpattern gl0 cp None) with
       | None -> IPatAnon (One None)
       | Some id -> IPatId id)
       (List.tl gens) in
     conclusion ipats
  end in
  interp_gens dgens ~conclusion:(fun ipats ->
  with_dgens dgens main <*>
  tclIPATssr ipats)

module Internal = struct

  let pf_find_abstract_proof b gl t =
    let res = ref None in
    let _ = V82.of_tactic (tacFIND_ABSTRACT_PROOF b (EConstr.of_constr t) >>= fun x -> res := Some x; tclUNIT ()) gl in
    match !res with
    | None -> assert false
    | Some x -> x

  let examine_abstract t gl =
    let res = ref None in
    let _ = V82.of_tactic (tacEXAMINE_ABSTRACT t >>= fun x -> res := Some x; tclUNIT ()) gl in
    match !res with
    | None -> assert false
    | Some x -> x

end

(* vim: set filetype=ocaml foldmethod=marker: *)
