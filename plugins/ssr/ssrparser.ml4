(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

let _vmcast = Constr.VMcast
open Names
open Pp
open Pcoq
open Ltac_plugin
open Genarg
open Stdarg
open Tacarg
open Libnames
open Tactics
open Tacmach
open Util
open Locus
open Tacexpr
open Tacinterp
open Pltac
open Extraargs
open Ppconstr

open Namegen
open Tactypes
open Decl_kinds
open Constrexpr
open Constrexpr_ops

open Proofview
open Proofview.Notations

open Ssrprinters
open Ssrcommon
open Ssrtacticals
open Ssrbwd
open Ssrequality
open Ssripats

(** Ssreflect load check. *)

(* To allow ssrcoq to be fully compatible with the "plain" Coq, we only *)
(* turn on its incompatible features (the new rewrite syntax, and the   *)
(* reserved identifiers) when the theory library (ssreflect.v) has      *)
(* has actually been required, or is being defined. Because this check  *)
(* needs to be done often (for each identifier lookup), we implement    *)
(* some caching, repeating the test only when the environment changes.  *)
(*   We check for protect_term because it is the first constant loaded; *)
(* ssr_have would ultimately be a better choice.                        *)
let ssr_loaded = Summary.ref ~name:"SSR:loaded" false
let is_ssr_loaded () =
  !ssr_loaded ||
  (if CLexer.is_keyword "SsrSyntax_is_Imported" then ssr_loaded:=true;
   !ssr_loaded)

DECLARE PLUGIN "ssreflect_plugin"
(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.get_keyword_state () ;;

let tacltop = (5,Notation_gram.E)

let pr_ssrtacarg _ _ prt = prt tacltop
ARGUMENT EXTEND ssrtacarg TYPED AS tactic PRINTED BY pr_ssrtacarg
| [ "YouShouldNotTypeThis" ] -> [ CErrors.anomaly (Pp.str "Grammar placeholder match") ]
END
GEXTEND Gram
  GLOBAL: ssrtacarg;
  ssrtacarg: [[ tac = tactic_expr LEVEL "5" -> tac ]];
END

(* Lexically closed tactic for tacticals. *)
let pr_ssrtclarg _ _ prt tac = prt tacltop tac
ARGUMENT EXTEND ssrtclarg TYPED AS ssrtacarg
    PRINTED BY pr_ssrtclarg
| [ ssrtacarg(tac) ] -> [ tac ]
END

open Genarg

(** Adding a new uninterpreted generic argument type *)
let add_genarg tag pr =
  let wit = Genarg.make0 tag in
  let tag = Geninterp.Val.create tag in
  let glob ist x = (ist, x) in
  let subst _ x = x in
  let interp ist x = Ftactic.return (Geninterp.Val.Dyn (tag, x)) in
  let gen_pr _ _ _ = pr in
  let () = Genintern.register_intern0 wit glob in
  let () = Genintern.register_subst0 wit subst in
  let () = Geninterp.register_interp0 wit interp in
  let () = Geninterp.register_val0 wit (Some (Geninterp.Val.Base tag)) in
  Pptactic.declare_extra_genarg_pprule wit gen_pr gen_pr gen_pr;
  wit

(** Primitive parsing to avoid syntax conflicts with basic tactics. *)

let accept_before_syms syms strm =
  match Util.stream_nth 1 strm with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_any_id syms strm =
  match Util.stream_nth 1 strm with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | Tok.IDENT _ -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_ids syms ids strm =
  match Util.stream_nth 1 strm with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | Tok.IDENT id when List.mem id ids -> ()
  | _ -> raise Stream.Failure

open Ssrast
let pr_id = Ppconstr.pr_id
let pr_name = function Name id -> pr_id id | Anonymous -> str "_"
let pr_spc () = str " "
let pr_list = prlist_with_sep

(**************************** ssrhyp **************************************) 

let pr_ssrhyp _ _ _ = pr_hyp

let wit_ssrhyprep = add_genarg "ssrhyprep" pr_hyp

let intern_hyp ist (SsrHyp (loc, id) as hyp) =
  let _ = Tacintern.intern_genarg ist (in_gen (rawwit wit_var) CAst.(make ?loc id)) in
  if not_section_id id then hyp else
  hyp_err ?loc "Can't clear section hypothesis " id

open Pcoq.Prim

ARGUMENT EXTEND ssrhyp TYPED AS ssrhyprep PRINTED BY pr_ssrhyp
                       INTERPRETED BY interp_hyp
                       GLOBALIZED BY intern_hyp
  | [ ident(id) ] -> [ SsrHyp (Loc.tag ~loc id) ]
END


let pr_hoi = hoik pr_hyp
let pr_ssrhoi _ _ _ = pr_hoi

let wit_ssrhoirep = add_genarg "ssrhoirep" pr_hoi

let intern_ssrhoi ist = function
  | Hyp h -> Hyp (intern_hyp ist h)
  | Id (SsrHyp (_, id)) as hyp ->
    let _ = Tacintern.intern_genarg ist (in_gen (rawwit wit_ident) id) in
    hyp

let interp_ssrhoi ist gl = function
  | Hyp h -> let s, h' = interp_hyp ist gl h in s, Hyp h'
  | Id (SsrHyp (loc, id)) ->
    let s, id' = interp_wit wit_ident ist gl id in
    s, Id (SsrHyp (loc, id'))

ARGUMENT EXTEND ssrhoi_hyp TYPED AS ssrhoirep PRINTED BY pr_ssrhoi
                       INTERPRETED BY interp_ssrhoi
                       GLOBALIZED BY intern_ssrhoi
  | [ ident(id) ] -> [ Hyp (SsrHyp(Loc.tag ~loc id)) ]
END
ARGUMENT EXTEND ssrhoi_id TYPED AS ssrhoirep PRINTED BY pr_ssrhoi
                       INTERPRETED BY interp_ssrhoi
                       GLOBALIZED BY intern_ssrhoi
  | [ ident(id) ] -> [ Id (SsrHyp(Loc.tag ~loc id)) ]
END


let pr_ssrhyps _ _ _ = pr_hyps

ARGUMENT EXTEND ssrhyps TYPED AS ssrhyp list PRINTED BY pr_ssrhyps
                        INTERPRETED BY interp_hyps
  | [ ssrhyp_list(hyps) ] -> [ check_hyps_uniq [] hyps; hyps ]
END

(** Rewriting direction *)


let pr_rwdir = function L2R -> mt() | R2L -> str "-"

let wit_ssrdir = add_genarg "ssrdir" pr_dir

(** Simpl switch *)

let pr_ssrsimpl _ _ _ = pr_simpl

let wit_ssrsimplrep = add_genarg "ssrsimplrep" pr_simpl

let test_ssrslashnum b1 b2 strm =
  match Util.stream_nth 0 strm with
  | Tok.KEYWORD "/" ->
      (match Util.stream_nth 1 strm with
      | Tok.INT _ when b1 ->
         (match Util.stream_nth 2 strm with
         | Tok.KEYWORD "=" | Tok.KEYWORD "/=" when not b2 -> ()
         | Tok.KEYWORD "/" ->
             if not b2 then () else begin
               match Util.stream_nth 3 strm with
               | Tok.INT _ -> ()
               | _ -> raise Stream.Failure
             end
         | _ -> raise Stream.Failure)
      | Tok.KEYWORD "/" when not b1 ->
         (match Util.stream_nth 2 strm with
         | Tok.KEYWORD "=" when not b2 -> ()
         | Tok.INT _ when b2 ->
           (match Util.stream_nth 3 strm with
           | Tok.KEYWORD "=" -> ()
           | _ -> raise Stream.Failure)
         | _ when not b2 -> ()
         | _ -> raise Stream.Failure)
      | Tok.KEYWORD "=" when not b1 && not b2 -> ()
      | _ -> raise Stream.Failure)
  | Tok.KEYWORD "//" when not b1 ->
         (match Util.stream_nth 1 strm with
         | Tok.KEYWORD "=" when not b2 -> ()
         | Tok.INT _ when b2 ->
           (match Util.stream_nth 2 strm with
           | Tok.KEYWORD "=" -> ()
           | _ -> raise Stream.Failure)
         | _ when not b2 -> ()
         | _ -> raise Stream.Failure)
  | _ -> raise Stream.Failure

let test_ssrslashnum10 = test_ssrslashnum true false
let test_ssrslashnum11 = test_ssrslashnum true true
let test_ssrslashnum01 = test_ssrslashnum false true
let test_ssrslashnum00 = test_ssrslashnum false false

let negate_parser f x =
  let rc = try Some (f x) with Stream.Failure -> None in
  match rc with
  | None -> ()
  | Some _ -> raise Stream.Failure 

let test_not_ssrslashnum =
  Pcoq.Gram.Entry.of_parser
    "test_not_ssrslashnum" (negate_parser test_ssrslashnum10)
let test_ssrslashnum00 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum01" test_ssrslashnum00
let test_ssrslashnum10 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum10" test_ssrslashnum10
let test_ssrslashnum11 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum11" test_ssrslashnum11
let test_ssrslashnum01 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum01" test_ssrslashnum01


ARGUMENT EXTEND ssrsimpl_ne TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ "//=" ] -> [ SimplCut (~-1,~-1) ]
| [ "/=" ] -> [ Simpl ~-1 ]
END

Pcoq.(Prim.(
GEXTEND Gram
  GLOBAL: ssrsimpl_ne;
  ssrsimpl_ne: [
    [ test_ssrslashnum11; "/"; n = natural; "/"; m = natural; "=" -> SimplCut(n,m)
    | test_ssrslashnum10; "/"; n = natural; "/" -> Cut n 
    | test_ssrslashnum10; "/"; n = natural; "=" -> Simpl n 
    | test_ssrslashnum10; "/"; n = natural; "/=" -> SimplCut (n,~-1) 
    | test_ssrslashnum10; "/"; n = natural; "/"; "=" -> SimplCut (n,~-1) 
    | test_ssrslashnum01; "//"; m = natural; "=" -> SimplCut (~-1,m)
    | test_ssrslashnum00; "//" -> Cut ~-1
    ]];

END
))

ARGUMENT EXTEND ssrsimpl TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ ssrsimpl_ne(sim) ] -> [ sim ]
| [ ] -> [ Nop ]
END


let pr_ssrclear _ _ _ = pr_clear mt

ARGUMENT EXTEND ssrclear_ne TYPED AS ssrhyps PRINTED BY pr_ssrclear
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ check_hyps_uniq [] clr; clr ]
END

ARGUMENT EXTEND ssrclear TYPED AS ssrclear_ne PRINTED BY pr_ssrclear
| [ ssrclear_ne(clr) ] -> [ clr ]
| [ ] -> [ [] ]
END

(** Indexes *)

(* Since SSR indexes are always positive numbers, we use the 0 value *)
(* to encode an omitted index. We reuse the in or_var type, but we   *)
(* supply our own interpretation function, which checks for non      *)
(* positive values, and allows the use of constr numerals, so that   *)
(* e.g., "let n := eval compute in (1 + 3) in (do n!clear)" works.   *)


let pr_index = function
  | ArgVar {CAst.v=id} -> pr_id id
  | ArgArg n when n > 0 -> int n
  | _ -> mt ()
let pr_ssrindex _ _ _ = pr_index

let noindex = ArgArg 0

let check_index ?loc i =
  if i > 0 then i else CErrors.user_err ?loc (str"Index not positive")
let mk_index ?loc = function
  | ArgArg i -> ArgArg (check_index ?loc i)
  | iv -> iv

let interp_index ist gl idx =
  Tacmach.project gl,
  match idx with
  | ArgArg _ -> idx
  | ArgVar id ->
    let i =
      try
        let v = Id.Map.find id.CAst.v ist.Tacinterp.lfun in
        begin match Tacinterp.Value.to_int v with
        | Some i -> i
        | None ->
        begin match Tacinterp.Value.to_constr v with
        | Some c ->
          let rc = Detyping.detype Detyping.Now false Id.Set.empty (pf_env gl) (project gl) c in
          begin match Notation.uninterp_prim_token rc with
          | _, Constrexpr.Numeral (s,b) ->
             let n = int_of_string s in if b then n else -n
          | _ -> raise Not_found
          end
        | None -> raise Not_found
        end end
    with _ -> CErrors.user_err ?loc:id.CAst.loc (str"Index not a number") in
    ArgArg (check_index ?loc:id.CAst.loc i)

open Pltac

ARGUMENT EXTEND ssrindex TYPED AS ssrindex PRINTED BY pr_ssrindex
  INTERPRETED BY interp_index
| [ int_or_var(i) ] -> [ mk_index ~loc i ]
END


(** Occurrence switch *)

(* The standard syntax of complemented occurrence lists involves a single *)
(* initial "-", e.g., {-1 3 5}. An initial                                *)
(* "+" may be used to indicate positive occurrences (the default). The    *)
(* "+" is optional, except if the list of occurrences starts with a       *)
(* variable or is empty (to avoid confusion with a clear switch). The     *)
(* empty positive switch "{+}" selects no occurrences, while the empty    *)
(* negative switch "{-}" selects all occurrences explicitly; this is the  *)
(* default, but "{-}" prevents the implicit clear, and can be used to     *)
(* force dependent elimination -- see ndefectelimtac below.               *)


let pr_ssrocc _ _ _ = pr_occ

open Pcoq.Prim

ARGUMENT EXTEND ssrocc TYPED AS (bool * int list) option PRINTED BY pr_ssrocc
| [ natural(n) natural_list(occ) ] -> [
     Some (false, List.map (check_index ~loc) (n::occ)) ]
| [ "-" natural_list(occ) ]     -> [ Some (true, occ) ]
| [ "+" natural_list(occ) ]     -> [ Some (false, occ) ]
END


(* modality *)


let pr_mmod = function May -> str "?" | Must -> str "!" | Once -> mt ()

let wit_ssrmmod = add_genarg "ssrmmod" pr_mmod
let ssrmmod = Pcoq.create_generic_entry Pcoq.utactic "ssrmmod" (Genarg.rawwit wit_ssrmmod);;

GEXTEND Gram
  GLOBAL: ssrmmod;
  ssrmmod: [[ "!" -> Must | LEFTQMARK -> May | "?" -> May]];
END

(** Rewrite multiplier: !n ?n *)

let pr_mult (n, m) =
  if n > 0 && m <> Once then int n ++ pr_mmod m else pr_mmod m

let pr_ssrmult _ _ _ = pr_mult

ARGUMENT EXTEND ssrmult_ne TYPED AS int * ssrmmod PRINTED BY pr_ssrmult
  | [ natural(n) ssrmmod(m) ] -> [ check_index ~loc n, m ]
  | [ ssrmmod(m) ]            -> [ notimes, m ]
END

ARGUMENT EXTEND ssrmult TYPED AS ssrmult_ne PRINTED BY pr_ssrmult
  | [ ssrmult_ne(m) ] -> [ m ]
  | [ ] -> [ nomult ]
END

(** Discharge occ switch (combined occurrence / clear switch *)

let pr_docc = function
  | None, occ -> pr_occ occ
  | Some clr, _ -> pr_clear mt clr

let pr_ssrdocc _ _ _ = pr_docc

ARGUMENT EXTEND ssrdocc TYPED AS ssrclear option * ssrocc PRINTED BY pr_ssrdocc
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
| [ "{" ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
END

(* Old kinds of terms *)

let input_ssrtermkind strm = match Util.stream_nth 0 strm with
  | Tok.KEYWORD "(" -> xInParens
  | Tok.KEYWORD "@" -> xWithAt
  | _ -> xNoFlag

let ssrtermkind = Pcoq.Gram.Entry.of_parser "ssrtermkind" input_ssrtermkind

(* New kinds of terms *)

let input_term_annotation strm =
  match Stream.npeek 2 strm with
  | Tok.KEYWORD "(" :: Tok.KEYWORD "(" :: _ -> `DoubleParens
  | Tok.KEYWORD "(" :: _ -> `Parens
  | Tok.KEYWORD "@" :: _ -> `At
  | _ -> `None
let term_annotation =
  Gram.Entry.of_parser "term_annotation" input_term_annotation

(* terms *)

(** Terms parsing. ********************************************************)

(* Because we allow wildcards in term references, we need to stage the *)
(* interpretation of terms so that it occurs at the right time during  *)
(* the execution of the tactic (e.g., so that we don't report an error *)
(* for a term that isn't actually used in the execution).              *)
(*   The term representation tracks whether the concrete initial term  *)
(* started with an opening paren, which might avoid a conflict between *)
(* the ssrreflect term syntax and Gallina notation.                    *)

(* Old terms *)
let pr_ssrterm _ _ _ = pr_term
let glob_ssrterm gs = function
  | k, (_, Some c) -> k, Tacintern.intern_constr gs c
  | ct -> ct
let subst_ssrterm s (k, c) = k, Tacsubst.subst_glob_constr_and_expr s c
let interp_ssrterm _ gl t = Tacmach.project gl, t

open Pcoq.Constr

ARGUMENT EXTEND ssrterm
     PRINTED BY pr_ssrterm
     INTERPRETED BY interp_ssrterm
     GLOBALIZED BY glob_ssrterm SUBSTITUTED BY subst_ssrterm
     RAW_PRINTED BY pr_ssrterm
     GLOB_PRINTED BY pr_ssrterm
| [ "YouShouldNotTypeThis" constr(c) ] -> [ mk_lterm c ]
END


GEXTEND Gram
  GLOBAL: ssrterm;
  ssrterm: [[ k = ssrtermkind; c = Pcoq.Constr.constr -> mk_term k c ]];
END

(* New terms *)

let pp_ast_closure_term _ _ _ = pr_ast_closure_term

ARGUMENT EXTEND ast_closure_term
     PRINTED BY pp_ast_closure_term
     INTERPRETED BY interp_ast_closure_term
     GLOBALIZED BY glob_ast_closure_term
     SUBSTITUTED BY subst_ast_closure_term
     RAW_PRINTED BY pp_ast_closure_term
     GLOB_PRINTED BY pp_ast_closure_term
  | [ term_annotation(a) constr(c) ] -> [ mk_ast_closure_term a c ]
END
ARGUMENT EXTEND ast_closure_lterm
     PRINTED BY pp_ast_closure_term
     INTERPRETED BY interp_ast_closure_term
     GLOBALIZED BY glob_ast_closure_term
     SUBSTITUTED BY subst_ast_closure_term
     RAW_PRINTED BY pp_ast_closure_term
     GLOB_PRINTED BY pp_ast_closure_term
  | [ term_annotation(a) lconstr(c) ] -> [ mk_ast_closure_term a c ]
END

(* Old Views *)

let pr_view = pr_list mt (fun c -> str "/" ++ pr_term c)

let pr_ssrbwdview _ _ _ = pr_view

ARGUMENT EXTEND ssrbwdview TYPED AS ssrterm list
   PRINTED BY pr_ssrbwdview
| [ "YouShouldNotTypeThis" ] -> [ [] ]
END

Pcoq.(
GEXTEND Gram
  GLOBAL: ssrbwdview;
  ssrbwdview: [
    [  test_not_ssrslashnum; "/"; c = Pcoq.Constr.constr -> [mk_term xNoFlag c]
    |  test_not_ssrslashnum; "/"; c = Pcoq.Constr.constr; w = ssrbwdview ->
                    (mk_term xNoFlag c) :: w ]];
END
)

(* New Views *)


let pr_ssrfwdview _ _ _ = pr_view2

ARGUMENT EXTEND ssrfwdview TYPED AS ast_closure_term list
   PRINTED BY pr_ssrfwdview
| [ "YouShouldNotTypeThis" ] -> [ [] ]
END

Pcoq.(
GEXTEND Gram
  GLOBAL: ssrfwdview;
  ssrfwdview: [
    [  test_not_ssrslashnum; "/"; c = Pcoq.Constr.constr ->
            [mk_ast_closure_term `None c]
    |  test_not_ssrslashnum; "/"; c = Pcoq.Constr.constr; w = ssrfwdview ->
                    (mk_ast_closure_term `None c) :: w ]];
END
)

(* }}} *)
 
(* ipats *)


let remove_loc x = x.CAst.v

let ipat_of_intro_pattern p = Tactypes.(
  let rec ipat_of_intro_pattern = function
    | IntroNaming (IntroIdentifier id) -> IPatId id
    | IntroAction IntroWildcard -> IPatAnon Drop
    | IntroAction (IntroOrAndPattern (IntroOrPattern iorpat)) ->
      IPatCase 
       (List.map (List.map ipat_of_intro_pattern) 
 	 (List.map (List.map remove_loc) iorpat))
    | IntroAction (IntroOrAndPattern (IntroAndPattern iandpat)) ->
      IPatCase 
       [List.map ipat_of_intro_pattern (List.map remove_loc iandpat)]
    | IntroNaming IntroAnonymous -> IPatAnon One
    | IntroAction (IntroRewrite b) -> IPatRewrite (allocc, if b then L2R else R2L)
    | IntroNaming (IntroFresh id) -> IPatAnon One
    | IntroAction (IntroApplyOn _) -> (* to do *) CErrors.user_err (Pp.str "TO DO")
    | IntroAction (IntroInjection ips) ->
        IPatInj [List.map ipat_of_intro_pattern (List.map remove_loc ips)]
    | IntroForthcoming _ ->
        (* Unable to determine which kind of ipat interp_introid could
         * return [HH] *)
        assert false
  in
  ipat_of_intro_pattern p
)

let rec map_ipat map_id map_ssrhyp map_ast_closure_term = function
  | (IPatSimpl _ | IPatAnon _ | IPatRewrite _ | IPatNoop) as x -> x
  | IPatId id -> IPatId (map_id id)
  | IPatAbstractVars l -> IPatAbstractVars (List.map map_id l)
  | IPatClear clr -> IPatClear (List.map map_ssrhyp clr)
  | IPatCase iorpat -> IPatCase (List.map (List.map (map_ipat map_id map_ssrhyp map_ast_closure_term)) iorpat)
  | IPatDispatch (s,iorpat) -> IPatDispatch (s,List.map (List.map (map_ipat map_id map_ssrhyp map_ast_closure_term)) iorpat)
  | IPatInj iorpat -> IPatInj (List.map (List.map (map_ipat map_id map_ssrhyp map_ast_closure_term)) iorpat)
  | IPatView (clr,v) -> IPatView (clr,List.map map_ast_closure_term v)
  | IPatTac _ -> assert false (*internal usage only *)

let wit_ssripatrep = add_genarg "ssripatrep" pr_ipat

let pr_ssripat _ _ _ = pr_ipat
let pr_ssripats _ _ _ = pr_ipats
let pr_ssriorpat _ _ _ = pr_iorpat

let intern_ipat ist =
  map_ipat
    (fun id -> id)
    (intern_hyp ist)
    (glob_ast_closure_term ist)

let intern_ipats ist = List.map (intern_ipat ist)

let interp_intro_pattern = interp_wit wit_intro_pattern

let interp_introid ist gl id =
 try IntroNaming (IntroIdentifier (hyp_id (snd (interp_hyp ist gl (SsrHyp (Loc.tag id))))))
 with _ -> (snd (interp_intro_pattern ist gl (CAst.make @@ IntroNaming (IntroIdentifier id)))).CAst.v

let get_intro_id = function
  | IntroNaming (IntroIdentifier id) -> id
  | _ -> assert false

let rec add_intro_pattern_hyps ipat hyps =
  let {CAst.loc=loc;v=ipat} = ipat in
  match ipat with
  | IntroNaming (IntroIdentifier id) ->
    if not_section_id id then SsrHyp (loc, id) :: hyps else
    hyp_err ?loc "Can't delete section hypothesis " id
  | IntroAction IntroWildcard -> hyps
  | IntroAction (IntroOrAndPattern (IntroOrPattern iorpat)) ->
     List.fold_right (List.fold_right add_intro_pattern_hyps) iorpat hyps
  | IntroAction (IntroOrAndPattern (IntroAndPattern iandpat)) ->
    List.fold_right add_intro_pattern_hyps iandpat hyps
  | IntroNaming IntroAnonymous -> []
  | IntroNaming (IntroFresh _) -> []
  | IntroAction (IntroRewrite _) -> hyps
  | IntroAction (IntroInjection ips) -> List.fold_right add_intro_pattern_hyps ips hyps
  | IntroAction (IntroApplyOn (c,pat)) -> add_intro_pattern_hyps pat hyps
  | IntroForthcoming _ -> 
    (* As in ipat_of_intro_pattern, was unable to determine which kind
      of ipat interp_introid could return [HH] *) assert false

(* We interp the ipat using the standard ltac machinery for ids, since
 * we have no clue what a name could be bound to (maybe another ipat) *)
let interp_ipat ist gl =
  let ltacvar id = Id.Map.mem id ist.Tacinterp.lfun in
  let rec interp = function
  | IPatId id when ltacvar id ->
    ipat_of_intro_pattern (interp_introid ist gl id)
  | IPatId _ as x -> x
  | IPatClear clr ->
    let add_hyps (SsrHyp (loc, id) as hyp) hyps =
      if not (ltacvar id) then hyp :: hyps else
      add_intro_pattern_hyps CAst.(make ?loc (interp_introid ist gl id)) hyps in
    let clr' = List.fold_right add_hyps clr [] in
    check_hyps_uniq [] clr'; IPatClear clr'
  | IPatCase(iorpat) ->
      IPatCase(List.map (List.map interp) iorpat)
  | IPatDispatch(s,iorpat) ->
      IPatDispatch(s,List.map (List.map interp) iorpat)
  | IPatInj iorpat -> IPatInj (List.map (List.map interp) iorpat)
  | IPatAbstractVars l ->
     IPatAbstractVars (List.map get_intro_id (List.map (interp_introid ist gl) l))
  | IPatView (clr,l) -> IPatView (clr,List.map (fun x -> snd(interp_ast_closure_term ist
     gl x)) l)
  | (IPatSimpl _ | IPatAnon _ | IPatRewrite _ | IPatNoop) as x -> x
  | IPatTac _ -> assert false (*internal usage only *)
    in
  interp

let interp_ipats ist gl l = project gl, List.map (interp_ipat ist gl) l

let pushIPatRewrite = function
  | pats :: orpat -> (IPatRewrite (allocc, L2R) :: pats) :: orpat
  | [] -> []

let pushIPatNoop = function
  | pats :: orpat -> (IPatNoop :: pats) :: orpat
  | [] -> []

ARGUMENT EXTEND ssripat TYPED AS ssripatrep list PRINTED BY pr_ssripats
  INTERPRETED BY interp_ipats
  GLOBALIZED BY intern_ipats
  | [ "_" ] -> [ [IPatAnon Drop] ]
  | [ "*" ] -> [ [IPatAnon All] ]
             (*
  | [ "^" "*" ] -> [ [IPatFastMode] ]
  | [ "^" "_" ] -> [ [IPatSeed `Wild] ]
  | [ "^_" ] -> [ [IPatSeed `Wild] ]
  | [ "^" "?" ] -> [ [IPatSeed `Anon] ]
  | [ "^?" ] -> [ [IPatSeed `Anon] ]
  | [ "^" ident(id) ] -> [ [IPatSeed (`Id(id,`Pre))] ]
  | [ "^" "~" ident(id) ] -> [ [IPatSeed (`Id(id,`Post))] ]
  | [ "^~" ident(id) ] -> [ [IPatSeed (`Id(id,`Post))] ]
              *)
  | [ ident(id) ] -> [ [IPatId id] ]
  | [ "?" ] -> [ [IPatAnon One] ]
(* TODO  | [ "+" ] -> [ [IPatAnon Temporary] ] *)
  | [ ssrsimpl_ne(sim) ] -> [ [IPatSimpl sim] ]
  | [ ssrdocc(occ) "->" ] -> [ match occ with
      | Some [], _ -> CErrors.user_err ~loc (str"occ_switch expected")
      | None, occ -> [IPatRewrite (occ, L2R)]
      | Some clr, _ -> [IPatClear clr; IPatRewrite (allocc, L2R)]]
  | [ ssrdocc(occ) "<-" ] -> [ match occ with
      | Some [], _ -> CErrors.user_err ~loc (str"occ_switch expected")
      | None, occ ->  [IPatRewrite (occ, R2L)]
      | Some clr, _ -> [IPatClear clr; IPatRewrite (allocc, R2L)]]
  | [ ssrdocc(occ) ssrfwdview(v) ] -> [ match occ with
      | Some [], _ -> [IPatView (true,v)]
      | Some cl, _ -> check_hyps_uniq [] cl; [IPatClear cl;IPatView (false,v)]
      | _ -> CErrors.user_err ~loc (str"Only identifiers are allowed here") ]
  | [ ssrdocc(occ) ] -> [ match occ with
      | Some cl, _ -> check_hyps_uniq [] cl; [IPatClear cl]
      | _ -> CErrors.user_err ~loc (str"Only identifiers are allowed here")]
  | [ "->" ] -> [ [IPatRewrite (allocc, L2R)] ]
  | [ "<-" ] -> [ [IPatRewrite (allocc, R2L)] ]
  | [ "-" ] -> [ [IPatNoop] ]
  | [ "-/" "=" ] -> [ [IPatNoop;IPatSimpl(Simpl ~-1)] ]
  | [ "-/=" ] -> [ [IPatNoop;IPatSimpl(Simpl ~-1)] ]
  | [ "-/" "/" ] -> [ [IPatNoop;IPatSimpl(Cut ~-1)] ]
  | [ "-//" ] -> [ [IPatNoop;IPatSimpl(Cut ~-1)] ]
  | [ "-/" integer(n) "/" ] -> [ [IPatNoop;IPatSimpl(Cut n)] ]
  | [ "-/" "/=" ] -> [ [IPatNoop;IPatSimpl(SimplCut (~-1,~-1))] ]
  | [ "-//" "=" ] -> [ [IPatNoop;IPatSimpl(SimplCut (~-1,~-1))] ]
  | [ "-//=" ] -> [ [IPatNoop;IPatSimpl(SimplCut (~-1,~-1))] ]
  | [ "-/" integer(n) "/=" ] -> [ [IPatNoop;IPatSimpl(SimplCut (n,~-1))] ]
  | [ "-/" integer(n) "/" integer (m) "=" ] ->
      [ [IPatNoop;IPatSimpl(SimplCut(n,m))] ]
  | [ ssrfwdview(v) ] -> [ [IPatView (false,v)] ]
  | [ "[" ":" ident_list(idl) "]" ] -> [ [IPatAbstractVars idl] ]
  | [ "[:" ident_list(idl) "]" ] -> [ [IPatAbstractVars idl] ]
END

ARGUMENT EXTEND ssripats TYPED AS ssripat PRINTED BY pr_ssripats
  | [ ssripat(i) ssripats(tl) ] -> [ i @ tl ]
  | [ ] -> [ [] ]
END

ARGUMENT EXTEND ssriorpat TYPED AS ssripat list PRINTED BY pr_ssriorpat
| [ ssripats(pats) "|" ssriorpat(orpat) ] -> [ pats :: orpat ]
| [ ssripats(pats) "|-" ">" ssriorpat(orpat) ] -> [ pats :: pushIPatRewrite orpat ]
| [ ssripats(pats) "|-" ssriorpat(orpat) ] -> [ pats :: pushIPatNoop orpat ]
| [ ssripats(pats) "|->" ssriorpat(orpat) ] -> [ pats :: pushIPatRewrite orpat ]
| [ ssripats(pats) "||" ssriorpat(orpat) ] -> [ pats :: [] :: orpat ]
| [ ssripats(pats) "|||" ssriorpat(orpat) ] -> [ pats :: [] :: [] :: orpat ]
| [ ssripats(pats) "||||" ssriorpat(orpat) ] -> [ [pats; []; []; []] @ orpat ]
| [ ssripats(pats) ] -> [ [pats] ]
END

let reject_ssrhid strm =
  match Util.stream_nth 0 strm with
  | Tok.KEYWORD "[" ->
      (match Util.stream_nth 1 strm with
      | Tok.KEYWORD ":" -> raise Stream.Failure
      | _ -> ())
  | _ -> ()

let test_nohidden = Pcoq.Gram.Entry.of_parser "test_ssrhid" reject_ssrhid

ARGUMENT EXTEND ssrcpat TYPED AS ssripatrep PRINTED BY pr_ssripat
  | [ "YouShouldNotTypeThis" ssriorpat(x) ] -> [ IPatCase(x) ]
END

Pcoq.(
GEXTEND Gram
  GLOBAL: ssrcpat;
  ssrcpat: [
   [ test_nohidden; "["; iorpat = ssriorpat; "]" ->
(*      check_no_inner_seed !@loc false iorpat;
      IPatCase (understand_case_type iorpat) *)
      IPatCase iorpat
(*
   | test_nohidden; "("; iorpat = ssriorpat; ")" ->
(*      check_no_inner_seed !@loc false iorpat;
      IPatCase (understand_case_type iorpat) *)
      IPatDispatch iorpat
*)
   | test_nohidden; "[="; iorpat = ssriorpat; "]" ->
(*      check_no_inner_seed !@loc false iorpat; *)
      IPatInj iorpat ]];
END
);;

Pcoq.(
GEXTEND Gram
  GLOBAL: ssripat;
  ssripat: [[ pat = ssrcpat -> [pat] ]];
END
)

ARGUMENT EXTEND ssripats_ne TYPED AS ssripat PRINTED BY pr_ssripats
  | [ ssripat(i) ssripats(tl) ] -> [ i @ tl ]
                                     END

(* subsets of patterns *)

(* TODO: review what this function does, it looks suspicious *)
let check_ssrhpats loc w_binders ipats =
  let err_loc s = CErrors.user_err ~loc ~hdr:"ssreflect" s in
  let clr, ipats =
    let rec aux clr = function
      | IPatClear cl :: tl -> aux (clr @ cl) tl
(*      | IPatSimpl (cl, sim) :: tl -> clr @ cl, IPatSimpl ([], sim) :: tl *)
      | tl -> clr, tl
    in aux [] ipats in
  let simpl, ipats = 
    match List.rev ipats with
    | IPatSimpl _ as s :: tl -> [s], List.rev tl
    | _ -> [],  ipats in
  if simpl <> [] && not w_binders then
    err_loc (str "No s-item allowed here: " ++ pr_ipats simpl);
  let ipat, binders =
    let rec loop ipat = function
      | [] -> ipat, []
      | ( IPatId _| IPatAnon _| IPatCase _ | IPatDispatch _ | IPatRewrite _ as i) :: tl ->
        if w_binders then
          if simpl <> [] && tl <> [] then 
            err_loc(str"binders XOR s-item allowed here: "++pr_ipats(tl@simpl))
          else if not (List.for_all (function IPatId _ -> true | _ -> false) tl)
          then err_loc (str "Only binders allowed here: " ++ pr_ipats tl)
          else ipat @ [i], tl
        else
          if tl = [] then  ipat @ [i], []
          else err_loc (str "No binder or s-item allowed here: " ++ pr_ipats tl)
      | hd :: tl -> loop (ipat @ [hd]) tl
    in loop [] ipats in
  ((clr, ipat), binders), simpl

let pr_hpats (((clr, ipat), binders), simpl) =
   pr_clear mt clr ++ pr_ipats ipat ++ pr_ipats binders ++ pr_ipats simpl
let pr_ssrhpats _ _ _ = pr_hpats
let pr_ssrhpats_wtransp _ _ _ (_, x) = pr_hpats x

ARGUMENT EXTEND ssrhpats TYPED AS ((ssrclear * ssripat) * ssripat) * ssripat
PRINTED BY pr_ssrhpats
  | [ ssripats(i) ] -> [ check_ssrhpats loc true i ]
END

ARGUMENT EXTEND ssrhpats_wtransp
  TYPED AS bool * (((ssrclear * ssripats) * ssripats) * ssripats)
  PRINTED BY pr_ssrhpats_wtransp
  | [ ssripats(i) ] -> [ false,check_ssrhpats loc true i ]
  | [ ssripats(i) "@" ssripats(j) ] -> [ true,check_ssrhpats loc true (i @ j) ]
END

ARGUMENT EXTEND ssrhpats_nobs 
TYPED AS ((ssrclear * ssripats) * ssripats) * ssripats PRINTED BY pr_ssrhpats
  | [ ssripats(i) ] -> [ check_ssrhpats loc false i ]
END

ARGUMENT EXTEND ssrrpat TYPED AS ssripatrep PRINTED BY pr_ssripat
  | [ "->" ] -> [ IPatRewrite (allocc, L2R) ]
  | [ "<-" ] -> [ IPatRewrite (allocc, R2L) ]
END

let pr_intros sep intrs =
  if intrs = [] then mt() else sep () ++ str "=>" ++ pr_ipats intrs
let pr_ssrintros _ _ _ = pr_intros mt

ARGUMENT EXTEND ssrintros_ne TYPED AS ssripat
 PRINTED BY pr_ssrintros
  | [ "=>" ssripats_ne(pats) ] -> [ pats ]
(*  TODO | [ "=>" ">" ssripats_ne(pats) ] -> [ IPatFastMode :: pats ]
  | [ "=>>" ssripats_ne(pats) ] -> [ IPatFastMode :: pats ] *)
END

ARGUMENT EXTEND ssrintros TYPED AS ssrintros_ne PRINTED BY pr_ssrintros
  | [ ssrintros_ne(intrs) ] -> [ intrs ]
  | [ ] -> [ [] ]
END

let pr_ssrintrosarg _ _ prt (tac, ipats) =
  prt tacltop tac ++ pr_intros spc ipats

ARGUMENT EXTEND ssrintrosarg TYPED AS tactic * ssrintros
   PRINTED BY pr_ssrintrosarg
| [ "YouShouldNotTypeThis" ssrtacarg(arg) ssrintros_ne(ipats) ] -> [ arg, ipats ]
END

TACTIC EXTEND ssrtclintros
| [ "YouShouldNotTypeThis" ssrintrosarg(arg) ] ->
  [ let tac, intros = arg in
    ssrevaltac ist tac <*> tclIPATssr intros ]
END

(** Defined identifier *)
let pr_ssrfwdid id = pr_spc () ++ pr_id id

let pr_ssrfwdidx _ _ _ = pr_ssrfwdid

(* We use a primitive parser for the head identifier of forward *)
(* tactis to avoid syntactic conflicts with basic Coq tactics. *)
ARGUMENT EXTEND ssrfwdid TYPED AS ident PRINTED BY pr_ssrfwdidx
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let accept_ssrfwdid strm =
  match stream_nth 0 strm with
  | Tok.IDENT id -> accept_before_syms_or_any_id [":"; ":="; "("] strm
  | _ -> raise Stream.Failure


let test_ssrfwdid = Gram.Entry.of_parser "test_ssrfwdid" accept_ssrfwdid

GEXTEND Gram
  GLOBAL: ssrfwdid;
  ssrfwdid: [[ test_ssrfwdid; id = Prim.ident -> id ]];
  END

  
(* by *)
(** Tactical arguments. *)

(* We have four kinds: simple tactics, [|]-bracketed lists, hints, and swaps *)
(* The latter two are used in forward-chaining tactics (have, suffice, wlog) *)
(* and subgoal reordering tacticals (; first & ; last), respectively.        *)


let pr_ortacs prt = 
  let rec pr_rec = function
  | [None]           -> spc() ++ str "|" ++ spc()
  | None :: tacs     -> spc() ++ str "|" ++ pr_rec tacs
  | Some tac :: tacs -> spc() ++ str "| " ++ prt tacltop tac ++  pr_rec tacs
  | []                -> mt() in
  function
  | [None]           -> spc()
  | None :: tacs     -> pr_rec tacs
  | Some tac :: tacs -> prt tacltop tac ++ pr_rec tacs
  | []                -> mt()
let pr_ssrortacs _ _ = pr_ortacs

ARGUMENT EXTEND ssrortacs TYPED AS tactic option list PRINTED BY pr_ssrortacs
| [ ssrtacarg(tac) "|" ssrortacs(tacs) ] -> [ Some tac :: tacs ]
| [ ssrtacarg(tac) "|" ] -> [ [Some tac; None] ]
| [ ssrtacarg(tac) ] -> [ [Some tac] ]
| [ "|" ssrortacs(tacs) ] -> [ None :: tacs ]
| [ "|" ] -> [ [None; None] ]
END

let pr_hintarg prt = function
  | true, tacs -> hv 0 (str "[ " ++ pr_ortacs prt tacs ++ str " ]")
  | false, [Some tac] -> prt tacltop tac
  | _, _ -> mt()

let pr_ssrhintarg _ _ = pr_hintarg


ARGUMENT EXTEND ssrhintarg TYPED AS bool * ssrortacs PRINTED BY pr_ssrhintarg
| [ "[" "]" ] -> [ nullhint ]
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_orhint tacs ]
| [ ssrtacarg(arg) ] -> [ mk_hint arg ]
END

ARGUMENT EXTEND ssrortacarg TYPED AS ssrhintarg PRINTED BY pr_ssrhintarg
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_orhint tacs ]
END


let pr_hint prt arg =
  if arg = nohint then mt() else str "by " ++ pr_hintarg prt arg
let pr_ssrhint _ _ = pr_hint

ARGUMENT EXTEND ssrhint TYPED AS ssrhintarg PRINTED BY pr_ssrhint
| [ ]                       -> [ nohint ]
END
(** The "in" pseudo-tactical *)(* {{{ **********************************************)

(* We can't make "in" into a general tactical because this would create a  *)
(* crippling conflict with the ltac let .. in construct. Hence, we add     *)
(* explicitly an "in" suffix to all the extended tactics for which it is   *)
(* relevant (including move, case, elim) and to the extended do tactical   *)
(* below, which yields a general-purpose "in" of the form do [...] in ...  *)

(* This tactical needs to come before the intro tactics because the latter *)
(* must take precautions in order not to interfere with the discharged     *)
(* assumptions. This is especially difficult for discharged "let"s, which  *)
(* the default simpl and unfold tactics would erase blindly.               *)

open Ssrmatching_plugin.Ssrmatching
open Ssrmatching_plugin.G_ssrmatching

let pr_wgen = function 
  | (clr, Some((id,k),None)) -> spc() ++ pr_clear mt clr ++ str k ++ pr_hoi id
  | (clr, Some((id,k),Some p)) ->
      spc() ++ pr_clear mt clr ++ str"(" ++ str k ++ pr_hoi id ++ str ":=" ++
        pr_cpattern p ++ str ")"
  | (clr, None) -> spc () ++ pr_clear mt clr
let pr_ssrwgen _ _ _ = pr_wgen

(* no globwith for char *)
ARGUMENT EXTEND ssrwgen
  TYPED AS ssrclear * ((ssrhoi_hyp * string) * cpattern option) option
  PRINTED BY pr_ssrwgen
| [ ssrclear_ne(clr) ] -> [ clr, None ]
| [ ssrhoi_hyp(hyp) ] -> [ [], Some((hyp, " "), None) ]
| [ "@" ssrhoi_hyp(hyp) ] -> [ [], Some((hyp, "@"), None) ]
| [ "(" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id," "),Some p) ]
| [ "(" ssrhoi_id(id) ")" ] -> [ [], Some ((id,"("), None) ]
| [ "(@" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id,"@"),Some p) ]
| [ "(" "@" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id,"@"),Some p) ]
END

let pr_clseq = function
  | InGoal | InHyps -> mt ()
  | InSeqGoal       -> str "|- *"
  | InHypsSeqGoal   -> str " |- *"
  | InHypsGoal      -> str " *"
  | InAll           -> str "*"
  | InHypsSeq       -> str " |-"
  | InAllHyps       -> str "* |-"

let wit_ssrclseq = add_genarg "ssrclseq" pr_clseq
let pr_clausehyps = pr_list pr_spc pr_wgen
let pr_ssrclausehyps _ _ _ = pr_clausehyps

ARGUMENT EXTEND ssrclausehyps 
TYPED AS ssrwgen list PRINTED BY pr_ssrclausehyps
| [ ssrwgen(hyp) "," ssrclausehyps(hyps) ] -> [ hyp :: hyps ]
| [ ssrwgen(hyp) ssrclausehyps(hyps) ] -> [ hyp :: hyps ]
| [ ssrwgen(hyp) ] -> [ [hyp] ]
END

(* type ssrclauses = ssrahyps * ssrclseq *)

let pr_clauses (hyps, clseq) = 
  if clseq = InGoal then mt ()
  else str "in " ++ pr_clausehyps hyps ++ pr_clseq clseq
let pr_ssrclauses _ _ _ = pr_clauses

ARGUMENT EXTEND ssrclauses TYPED AS ssrwgen list * ssrclseq
    PRINTED BY pr_ssrclauses
  | [ "in" ssrclausehyps(hyps) "|-" "*" ] -> [ hyps, InHypsSeqGoal ]
  | [ "in" ssrclausehyps(hyps) "|-" ]     -> [ hyps, InHypsSeq ]
  | [ "in" ssrclausehyps(hyps) "*" ]      -> [ hyps, InHypsGoal ]
  | [ "in" ssrclausehyps(hyps) ]          -> [ hyps, InHyps ]
  | [ "in" "|-" "*" ]                     -> [ [], InSeqGoal ]
  | [ "in" "*" ]                          -> [ [], InAll ]
  | [ "in" "*" "|-" ]                     -> [ [], InAllHyps ]
  | [ ]                                   -> [ [], InGoal ]
END




(** Definition value formatting *)

(* We use an intermediate structure to correctly render the binder list  *)
(* abbreviations. We use a list of hints to extract the binders and      *)
(* base term from a term, for the two first levels of representation of  *)
(* of constr terms.                                                      *)

let pr_binder prl = function
  | Bvar x ->
    pr_name x
  | Bdecl (xs, t) ->
    str "(" ++ pr_list pr_spc pr_name xs ++ str " : " ++ prl t ++ str ")"
  | Bdef (x, None, v) ->
    str "(" ++ pr_name x ++ str " := " ++ prl v ++ str ")"
  | Bdef (x, Some t, v) ->
    str "(" ++ pr_name x ++ str " : " ++ prl t ++
                            str " := " ++ prl v ++ str ")"
  | Bstruct x ->
    str "{struct " ++ pr_name x ++ str "}"
  | Bcast t ->
    str ": " ++ prl t

let rec format_local_binders h0 bl0 = match h0, bl0 with
  | BFvar :: h, CLocalAssum ([{CAst.v=x}], _,  _) :: bl ->
    Bvar x :: format_local_binders h bl
  | BFdecl _ :: h, CLocalAssum (lxs, _, t) :: bl ->
    Bdecl (List.map (fun x -> x.CAst.v) lxs, t) :: format_local_binders h bl
  | BFdef :: h, CLocalDef ({CAst.v=x}, v, oty) :: bl ->
    Bdef (x, oty, v) :: format_local_binders h bl
  | _ -> []
  
let rec format_constr_expr h0 c0 = let open CAst in match h0, c0 with
  | BFvar :: h, { v = CLambdaN ([CLocalAssum([{CAst.v=x}], _, _)], c) } ->
    let bs, c' = format_constr_expr h c in
    Bvar x :: bs, c'
  | BFdecl _:: h, { v = CLambdaN ([CLocalAssum(lxs, _, t)], c) } ->
    let bs, c' = format_constr_expr h c in
    Bdecl (List.map (fun x -> x.CAst.v) lxs, t) :: bs, c'
  | BFdef :: h, { v = CLetIn({CAst.v=x}, v, oty, c) } ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, oty, v) :: bs, c'
  | [BFcast], { v = CCast (c, Glob_term.CastConv t) } ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, 
    { v = CFix ( _, [_, (Some locn, CStructRec), bl, t, c]) } ->
    let bs = format_local_binders h bl in
    let bstr = if has_str then [Bstruct (Name locn.CAst.v)] else [] in
    bs @ bstr @ (if has_cast then [Bcast t] else []), c 
  | BFrec (_, has_cast) :: h, { v = CCoFix ( _, [_, bl, t, c]) } ->
    format_local_binders h bl @ (if has_cast then [Bcast t] else []), c
  | _, c ->
    [], c

(** Forward chaining argument *)

(* There are three kinds of forward definitions:           *)
(*   - Hint: type only, cast to Type, may have proof hint. *)
(*   - Have: type option + value, no space before type     *)
(*   - Pose: binders + value, space before binders.        *)

let pr_fwdkind = function
  | FwdHint (s,_) -> str (s ^ " ") | _ -> str " :=" ++ spc ()
let pr_fwdfmt (fk, _ : ssrfwdfmt) = pr_fwdkind fk

let wit_ssrfwdfmt = add_genarg "ssrfwdfmt" pr_fwdfmt

(* type ssrfwd = ssrfwdfmt * ssrterm *)

let mkFwdVal fk c = ((fk, []), c)
let mkssrFwdVal fk c = ((fk, []), (c,None))
let dC t = Glob_term.CastConv t

let same_ist { interp_env = x } { interp_env = y } =
  match x,y with
  | None, None -> true
  | Some a, Some b -> a == b
  | _ -> false

let mkFwdCast fk ?loc ?c t =
  let c = match c with
    | None -> mkCHole loc
    | Some c -> assert (same_ist t c); c.body in
  ((fk, [BFcast]),
   { t with annotation = `None;
            body = (CAst.make ?loc @@ CCast (c, dC t.body)) })

let mkssrFwdCast fk loc t c = ((fk, [BFcast]), (c, Some t))

let mkFwdHint s t =
  let loc =  Constrexpr_ops.constr_loc t.body in
  mkFwdCast (FwdHint (s,false)) ?loc t
let mkFwdHintNoTC s t =
  let loc =  Constrexpr_ops.constr_loc t.body in
  mkFwdCast (FwdHint (s,true)) ?loc t

let pr_gen_fwd prval prc prlc fk (bs, c) =
  let prc s = str s ++ spc () ++ prval prc prlc c in
  match fk, bs with
  | FwdHint (s,_), [Bcast t] -> str s ++ spc () ++ prlc t
  | FwdHint (s,_), _ ->  prc (s ^ "(* typeof *)")
  | FwdHave, [Bcast t] -> str ":" ++ spc () ++ prlc t ++ prc " :="
  | _, [] -> prc " :="
  | _, _ -> spc () ++ pr_list spc (pr_binder prlc) bs ++ prc " :="

let pr_fwd_guarded prval prval' = function
| (fk, h), c ->
  pr_gen_fwd prval pr_constr_expr prl_constr_expr fk (format_constr_expr h c.body)

let pr_unguarded prc prlc = prlc

let pr_fwd = pr_fwd_guarded pr_unguarded pr_unguarded
let pr_ssrfwd _ _ _ = pr_fwd
 
ARGUMENT EXTEND ssrfwd TYPED AS (ssrfwdfmt * ast_closure_lterm) PRINTED BY pr_ssrfwd
  | [ ":=" ast_closure_lterm(c) ] -> [ mkFwdVal FwdPose c ]
  | [ ":" ast_closure_lterm (t) ":=" ast_closure_lterm(c) ] -> [ mkFwdCast FwdPose ~loc t ~c ]
END

(** Independent parsing for binders *)

(* The pose, pose fix, and pose cofix tactics use these internally to  *)
(* parse argument fragments.                                           *)

let pr_ssrbvar prc _ _ v = prc v

ARGUMENT EXTEND ssrbvar TYPED AS constr PRINTED BY pr_ssrbvar
| [ ident(id) ] -> [ mkCVar ~loc id ]
| [ "_" ] -> [ mkCHole (Some loc) ]
END

let bvar_lname = let open CAst in function
  | { v = CRef (qid, _) } when qualid_is_ident qid ->
    CAst.make ?loc:qid.CAst.loc @@ Name (qualid_basename qid)
  | { loc = loc } -> CAst.make ?loc Anonymous

let pr_ssrbinder prc _ _ (_, c) = prc c

ARGUMENT EXTEND ssrbinder TYPED AS ssrfwdfmt * constr PRINTED BY pr_ssrbinder
 | [ ssrbvar(bv) ] ->
   [ let { CAst.loc=xloc } as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum([x],Default Explicit,mkCHole xloc)],mkCHole (Some loc)) ]
 | [ "(" ssrbvar(bv) ")" ] ->
   [ let { CAst.loc=xloc } as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum([x],Default Explicit,mkCHole xloc)],mkCHole (Some loc)) ]
 | [ "(" ssrbvar(bv) ":" lconstr(t) ")" ] ->
   [ let x = bvar_lname bv in
     (FwdPose, [BFdecl 1]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum([x], Default Explicit, t)], mkCHole (Some loc)) ]
 | [ "(" ssrbvar(bv) ne_ssrbvar_list(bvs) ":" lconstr(t) ")" ] ->
   [ let xs = List.map bvar_lname (bv :: bvs) in
     let n = List.length xs in
     (FwdPose, [BFdecl n]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum (xs, Default Explicit, t)], mkCHole (Some loc)) ]
 | [ "(" ssrbvar(id) ":" lconstr(t) ":=" lconstr(v) ")" ] ->
   [ (FwdPose,[BFdef]), CAst.make ~loc @@ CLetIn (bvar_lname id, v, Some t, mkCHole (Some loc)) ]
 | [ "(" ssrbvar(id) ":=" lconstr(v) ")" ] ->
   [ (FwdPose,[BFdef]), CAst.make ~loc @@ CLetIn (bvar_lname id, v, None, mkCHole (Some loc)) ]
     END

GEXTEND Gram
  GLOBAL: ssrbinder;
  ssrbinder: [
  [  ["of" | "&"]; c = operconstr LEVEL "99" ->
     let loc = !@loc in
     (FwdPose, [BFvar]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum ([CAst.make ~loc Anonymous],Default Explicit,c)],mkCHole (Some loc)) ]
  ];
END

let rec binders_fmts = function
  | ((_, h), _) :: bs -> h @ binders_fmts bs
  | _ -> []

let push_binders c2 bs =
  let loc2 = constr_loc c2 in let mkloc loc1 = Loc.merge_opt loc1 loc2 in
  let open CAst in
  let rec loop ty c = function
  | (_, { loc = loc1; v = CLambdaN (b, _) } ) :: bs when ty ->
      CAst.make ?loc:(mkloc loc1) @@ CProdN (b, loop ty c bs)
  | (_, { loc = loc1; v = CLambdaN (b, _) } ) :: bs ->
      CAst.make ?loc:(mkloc loc1) @@ CLambdaN (b, loop ty c bs)
  | (_, { loc = loc1; v = CLetIn (x, v, oty, _) } ) :: bs ->
      CAst.make ?loc:(mkloc loc1) @@ CLetIn (x, v, oty, loop ty c bs)
  | [] -> c
  | _ -> anomaly "binder not a lambda nor a let in" in
  match c2 with
  | { loc; v = CCast (ct, Glob_term.CastConv cty) } ->
      CAst.make ?loc @@ (CCast (loop false ct bs, Glob_term.CastConv (loop true cty bs)))
  | ct -> loop false ct bs

let rec fix_binders = let open CAst in function
  | (_, { v = CLambdaN ([CLocalAssum(xs, _, t)], _) } ) :: bs ->
      CLocalAssum (xs, Default Explicit, t) :: fix_binders bs
  | (_, { v = CLetIn (x, v, oty, _) } ) :: bs ->
    CLocalDef (x, v, oty) :: fix_binders bs
  | _ -> []

let pr_ssrstruct _ _ _ = function
  | Some id -> str "{struct " ++ pr_id id ++ str "}"
  | None -> mt ()

ARGUMENT EXTEND ssrstruct TYPED AS ident option PRINTED BY pr_ssrstruct
| [ "{" "struct" ident(id) "}" ] -> [ Some id ]
| [ ] -> [ None ]
END

(** The "pose" tactic *)

(* The plain pose form. *)

let bind_fwd bs ((fk, h), c) =
 (fk,binders_fmts bs @ h), { c with body = push_binders c.body bs }

ARGUMENT EXTEND ssrposefwd TYPED AS ssrfwd PRINTED BY pr_ssrfwd
  | [ ssrbinder_list(bs) ssrfwd(fwd) ] -> [ bind_fwd bs fwd ]
END

(* The pose fix form. *)

let pr_ssrfixfwd _ _ _ (id, fwd) = str " fix " ++ pr_id id ++ pr_fwd fwd

let bvar_locid = function
  | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
    CAst.make ?loc:qid.CAst.loc (qualid_basename qid)
  | _ -> CErrors.user_err (Pp.str "Missing identifier after \"(co)fix\"")


ARGUMENT EXTEND ssrfixfwd TYPED AS ident * ssrfwd PRINTED BY pr_ssrfixfwd
  | [ "fix" ssrbvar(bv) ssrbinder_list(bs) ssrstruct(sid) ssrfwd(fwd) ] ->
    [ let { CAst.v=id } as lid = bvar_locid bv in
      let (fk, h), ac = fwd in
      let c = ac.body in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, mkCHole (constr_loc c), c in
      let lb = fix_binders bs in
      let has_struct, i =
        let rec loop = function
          | {CAst.loc=l'; v=Name id'} :: _ when Option.equal Id.equal sid (Some id') ->
            true, CAst.make ?loc:l' id'
          | [{CAst.loc=l';v=Name id'}] when sid = None ->
            false, CAst.make ?loc:l' id'
          | _ :: bn -> loop bn
          | [] -> CErrors.user_err (Pp.str "Bad structural argument") in
        loop (names_of_local_assums lb) in
      let h' = BFrec (has_struct, has_cast) :: binders_fmts bs in
      let fix = CAst.make ~loc @@ CFix (lid, [lid, (Some i, CStructRec), lb, t', c']) in
      id, ((fk, h'),  { ac with body = fix }) ]
END


(* The pose cofix form. *)

let pr_ssrcofixfwd _ _ _ (id, fwd) = str " cofix " ++ pr_id id ++ pr_fwd fwd

ARGUMENT EXTEND ssrcofixfwd TYPED AS ssrfixfwd PRINTED BY pr_ssrcofixfwd
  | [ "cofix" ssrbvar(bv) ssrbinder_list(bs) ssrfwd(fwd) ] ->
    [ let { CAst.v=id } as lid = bvar_locid bv in
      let (fk, h), ac = fwd in
      let c = ac.body in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, mkCHole (constr_loc c), c in
      let h' = BFrec (false, has_cast) :: binders_fmts bs in
      let cofix = CAst.make ~loc @@ CCoFix (lid, [lid, fix_binders bs, t', c']) in
      id, ((fk, h'), { ac with body = cofix })
    ]
END

(* This does not print the type, it should be fixed... *)
let pr_ssrsetfwd _ _ _ (((fk,_),(t,_)), docc) =
  pr_gen_fwd (fun _ _ -> pr_cpattern)
    (fun _ -> mt()) (fun _ -> mt()) fk ([Bcast ()],t)

ARGUMENT EXTEND ssrsetfwd
TYPED AS (ssrfwdfmt * (lcpattern * ast_closure_lterm option)) * ssrdocc
PRINTED BY pr_ssrsetfwd
| [ ":" ast_closure_lterm(t) ":=" "{" ssrocc(occ) "}" cpattern(c) ] ->
  [ mkssrFwdCast FwdPose loc t c, mkocc occ ]
| [ ":" ast_closure_lterm(t) ":=" lcpattern(c) ] ->
  [ mkssrFwdCast FwdPose loc t c, nodocc ]
| [ ":=" "{" ssrocc(occ) "}" cpattern(c) ] ->
  [ mkssrFwdVal FwdPose c, mkocc occ ]
| [ ":=" lcpattern(c) ] -> [ mkssrFwdVal FwdPose c, nodocc ]
END


let pr_ssrhavefwd _ _ prt (fwd, hint) = pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrhavefwd TYPED AS ssrfwd * ssrhint PRINTED BY pr_ssrhavefwd
| [ ":" ast_closure_lterm(t) ssrhint(hint) ] -> [ mkFwdHint ":" t, hint ]
| [ ":" ast_closure_lterm(t) ":=" ast_closure_lterm(c) ] -> [ mkFwdCast FwdHave ~loc t ~c, nohint ]
| [ ":" ast_closure_lterm(t) ":=" ] -> [ mkFwdHintNoTC ":" t, nohint ]
| [ ":=" ast_closure_lterm(c) ] -> [ mkFwdVal FwdHave c, nohint ]
END

let intro_id_to_binder = List.map (function 
  | IPatId id ->
      let { CAst.loc=xloc } as x = bvar_lname (mkCVar id) in
      (FwdPose, [BFvar]),
        CAst.make @@ CLambdaN ([CLocalAssum([x], Default Explicit, mkCHole xloc)],
          mkCHole None)
  | _ -> anomaly "non-id accepted as binder")

let binder_to_intro_id = CAst.(List.map (function
  | (FwdPose, [BFvar]), { v = CLambdaN ([CLocalAssum(ids,_,_)],_) }
  | (FwdPose, [BFdecl _]), { v = CLambdaN ([CLocalAssum(ids,_,_)],_) } ->
      List.map (function {v=Name id} -> IPatId id | _ -> IPatAnon One) ids
  | (FwdPose, [BFdef]), { v = CLetIn ({v=Name id},_,_,_) } -> [IPatId id]
  | (FwdPose, [BFdef]), { v = CLetIn ({v=Anonymous},_,_,_) } -> [IPatAnon One]
  | _ -> anomaly "ssrbinder is not a binder"))

let pr_ssrhavefwdwbinders _ _ prt (tr,((hpats, (fwd, hint)))) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrhavefwdwbinders
  TYPED AS bool * (ssrhpats * (ssrfwd * ssrhint))
  PRINTED BY pr_ssrhavefwdwbinders
| [ ssrhpats_wtransp(trpats) ssrbinder_list(bs) ssrhavefwd(fwd) ] ->
  [ let tr, pats = trpats in
    let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let hint = bind_fwd allbs (fst fwd), snd fwd in
    tr, ((((clr, pats), allbinders), simpl), hint) ]
END


let pr_ssrdoarg prc _ prt (((n, m), tac), clauses) =
  pr_index n ++ pr_mmod m ++ pr_hintarg prt tac ++ pr_clauses clauses

ARGUMENT EXTEND ssrdoarg
  TYPED AS ((ssrindex * ssrmmod) * ssrhintarg) * ssrclauses
  PRINTED BY pr_ssrdoarg
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

(* type ssrseqarg = ssrindex * (ssrtacarg * ssrtac option) *)

let pr_seqtacarg prt = function
  | (is_first, []), _ -> str (if is_first then "first" else "last")
  | tac, Some dtac ->
    hv 0 (pr_hintarg prt tac ++ spc() ++ str "|| " ++ prt tacltop dtac)
  | tac, _ -> pr_hintarg prt tac

let pr_ssrseqarg _ _ prt = function
  | ArgArg 0, tac -> pr_seqtacarg prt tac
  | i, tac -> pr_index i ++ str " " ++ pr_seqtacarg prt tac

(* We must parse the index separately to resolve the conflict with *)
(* an unindexed tactic.                                            *)
ARGUMENT EXTEND ssrseqarg TYPED AS ssrindex * (ssrhintarg * tactic option)
                          PRINTED BY pr_ssrseqarg
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let sq_brace_tacnames =
   ["first"; "solve"; "do"; "rewrite"; "have"; "suffices"; "wlog"]
   (* "by" is a keyword *)
let accept_ssrseqvar strm =
  match stream_nth 0 strm with
  | Tok.IDENT id when not (List.mem id sq_brace_tacnames) ->
     accept_before_syms_or_ids ["["] ["first";"last"] strm
  | _ -> raise Stream.Failure

let test_ssrseqvar = Gram.Entry.of_parser "test_ssrseqvar" accept_ssrseqvar

let swaptacarg (loc, b) = (b, []), Some (TacId [])

let check_seqtacarg dir arg = match snd arg, dir with
  | ((true, []), Some (TacAtom (loc, _))), L2R ->
    CErrors.user_err ?loc (str "expected \"last\"")
  | ((false, []), Some (TacAtom (loc, _))), R2L ->
    CErrors.user_err ?loc (str "expected \"first\"")
  | _, _ -> arg

let ssrorelse = Entry.create "ssrorelse"
GEXTEND Gram
  GLOBAL: ssrorelse ssrseqarg;
  ssrseqidx: [
    [ test_ssrseqvar; id = Prim.ident -> ArgVar (CAst.make ~loc:!@loc id)
    | n = Prim.natural -> ArgArg (check_index ~loc:!@loc n)
    ] ];
  ssrswap: [[ IDENT "first" -> !@loc, true | IDENT "last" -> !@loc, false ]];
  ssrorelse: [[ "||"; tac = tactic_expr LEVEL "2" -> tac ]];
  ssrseqarg: [
    [ arg = ssrswap -> noindex, swaptacarg arg
    | i = ssrseqidx; tac = ssrortacarg; def = OPT ssrorelse -> i, (tac, def)
    | i = ssrseqidx; arg = ssrswap -> i, swaptacarg arg
    | tac = tactic_expr LEVEL "3" -> noindex, (mk_hint tac, None)
    ] ];
END

let tactic_expr = Pltac.tactic_expr

(** 1. Utilities *)

(** Tactic-level diagnosis *)

(* debug *)

(* Let's play with the new proof engine API *)
let old_tac = V82.tactic


(** Name generation *)(* {{{ *******************************************************)

(* Since Coq now does repeated internal checks of its external lexical *)
(* rules, we now need to carve ssreflect reserved identifiers out of   *)
(* out of the user namespace. We use identifiers of the form _id_ for  *)
(* this purpose, e.g., we "anonymize" an identifier id as _id_, adding *)
(* an extra leading _ if this might clash with an internal identifier. *)
(*    We check for ssreflect identifiers in the ident grammar rule;    *)
(* when the ssreflect Module is present this is normally an error,     *)
(* but we provide a compatibility flag to reduce this to a warning.    *)

let ssr_reserved_ids = Summary.ref ~name:"SSR:idents" true

let _ =
  Goptions.declare_bool_option
    { Goptions.optname  = "ssreflect identifiers";
      Goptions.optkey   = ["SsrIdents"];
      Goptions.optdepr  = false;
      Goptions.optread  = (fun _ -> !ssr_reserved_ids);
      Goptions.optwrite = (fun b -> ssr_reserved_ids := b)
    }

let is_ssr_reserved s =
  let n = String.length s in n > 2 && s.[0] = '_' && s.[n - 1] = '_'

let ssr_id_of_string loc s =
  if is_ssr_reserved s && is_ssr_loaded () then begin
    if !ssr_reserved_ids then
      CErrors.user_err ~loc (str ("The identifier " ^ s ^ " is reserved."))
    else if is_internal_name s then
      Feedback.msg_warning (str ("Conflict between " ^ s ^ " and ssreflect internal names."))
    else Feedback.msg_warning (str (
     "The name " ^ s ^ " fits the _xxx_ format used for anonymous variables.\n"
  ^ "Scripts with explicit references to anonymous variables are fragile."))
    end; Id.of_string s

let ssr_null_entry = Gram.Entry.of_parser "ssr_null" (fun _ -> ())

let (!@) = Pcoq.to_coqloc

GEXTEND Gram 
  GLOBAL: Prim.ident;
  Prim.ident: [[ s = IDENT; ssr_null_entry -> ssr_id_of_string !@loc s ]];
END

let perm_tag = "_perm_Hyp_"
let _ = add_internal_name (is_tagged perm_tag)
  
(* }}} *)

(* We must not anonymize context names discharged by the "in" tactical. *)

(** Tactical extensions. *)(* {{{ **************************************************)

(* The TACTIC EXTEND facility can't be used for defining new user   *)
(* tacticals, because:                                              *)
(*  - the concrete syntax must start with a fixed string            *)
(*   We use the following workaround:                               *)
(*  - We use the (unparsable) "YouShouldNotTypeThis"  token for tacticals that      *)
(*    don't start with a token, then redefine the grammar and       *)
(*    printer using GEXTEND and set_pr_ssrtac, respectively.        *)

type ssrargfmt = ArgSsr of string | ArgSep of string

let ssrtac_name name = {
  mltac_plugin = "ssreflect_plugin";
  mltac_tactic = "ssr" ^ name;
}

let ssrtac_entry name n = {
  mltac_name = ssrtac_name name; 
  mltac_index = n;
}

let set_pr_ssrtac name prec afmt = (* FIXME *) () (*
  let fmt = List.map (function
    | ArgSep s -> Egramml.GramTerminal s
    | ArgSsr s -> Egramml.GramTerminal s
    | ArgCoq at -> Egramml.GramTerminal "COQ_ARG") afmt in
  let tacname = ssrtac_name name in () *)

let ssrtac_atom ?loc name args = TacML (Loc.tag ?loc (ssrtac_entry name 0, args))
let ssrtac_expr ?loc name args = ssrtac_atom ?loc name args

let tclintros_expr ?loc tac ipats =
  let args = [Tacexpr.TacGeneric (in_gen (rawwit wit_ssrintrosarg) (tac, ipats))] in
  ssrtac_expr ?loc "tclintros" args

GEXTEND Gram
  GLOBAL: tactic_expr;
  tactic_expr: LEVEL "1" [ RIGHTA
    [ tac = tactic_expr; intros = ssrintros_ne -> tclintros_expr ~loc:!@loc tac intros
    ] ];
END

(* }}} *)


(** Bracketing tactical *)

(* The tactic pretty-printer doesn't know that some extended tactics *)
(* are actually tacticals. To prevent it from improperly removing    *)
(* parentheses we override the parsing rule for bracketed tactic     *)
(* expressions so that the pretty-print always reflects the input.   *)
(* (Removing user-specified parentheses is dubious anyway).          *)

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrparentacarg: [[ "("; tac = tactic_expr; ")" -> Loc.tag ~loc:!@loc (Tacexp tac) ]];
  tactic_expr: LEVEL "0" [[ arg = ssrparentacarg -> TacArg arg ]];
END

(** The internal "done" and "ssrautoprop" tactics. *)

(* For additional flexibility, "done" and "ssrautoprop" are  *)
(* defined in Ltac.                                          *)
(* Although we provide a default definition in ssreflect,    *)
(* we look up the definition dynamically at each call point, *)
(* to allow for user extensions. "ssrautoprop" defaults to   *)
(* trivial.                                                  *)

let ssrautoprop gl =
  try 
    let tacname = 
      try Tacenv.locate_tactic (qualid_of_ident (Id.of_string "ssrautoprop"))
      with Not_found -> Tacenv.locate_tactic (ssrqid "ssrautoprop") in
    let tacexpr = Loc.tag @@ Tacexpr.Reference (ArgArg (Loc.tag @@ tacname)) in
    V82.of_tactic (eval_tactic (Tacexpr.TacArg tacexpr)) gl
  with Not_found -> V82.of_tactic (Auto.full_trivial []) gl

let () = ssrautoprop_tac := ssrautoprop

let tclBY tac = Tacticals.tclTHEN tac (donetac ~-1)

(** Tactical arguments. *)

(* We have four kinds: simple tactics, [|]-bracketed lists, hints, and swaps *)
(* The latter two are used in forward-chaining tactics (have, suffice, wlog) *)
(* and subgoal reordering tacticals (; first & ; last), respectively.        *)

(* Force use of the tactic_expr parsing entry, to rule out tick marks. *)

(** The "by" tactical. *)


open Ssrfwd

TACTIC EXTEND ssrtclby
| [ "by" ssrhintarg(tac) ] -> [ V82.tactic (hinttac ist true tac) ]
END

(* }}} *)
(* We can't parse "by" in ARGUMENT EXTEND because it will only be made *)
(* into a keyword in ssreflect.v; so we anticipate this in GEXTEND.    *)

GEXTEND Gram
  GLOBAL: ssrhint simple_tactic;
  ssrhint: [[ "by"; arg = ssrhintarg -> arg ]];
END

(** The "do" tactical. ********************************************************)

(*
type ssrdoarg = ((ssrindex * ssrmmod) * ssrhint) * ssrclauses
*)
TACTIC EXTEND ssrtcldo
| [ "YouShouldNotTypeThis" "do" ssrdoarg(arg) ] -> [ V82.tactic (ssrdotac ist arg) ]
END
set_pr_ssrtac "tcldo" 3 [ArgSep "do "; ArgSsr "doarg"]

let ssrdotac_expr ?loc n m tac clauses =
  let arg = ((n, m), tac), clauses in
  ssrtac_expr ?loc "tcldo" [Tacexpr.TacGeneric (in_gen (rawwit wit_ssrdoarg) arg)]

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrdotac: [
    [ tac = tactic_expr LEVEL "3" -> mk_hint tac
    | tacs = ssrortacarg -> tacs
  ] ];
  tactic_expr: LEVEL "3" [ RIGHTA
    [ IDENT "do"; m = ssrmmod; tac = ssrdotac; clauses = ssrclauses ->
      ssrdotac_expr ~loc:!@loc noindex m tac clauses
    | IDENT "do"; tac = ssrortacarg; clauses = ssrclauses ->
      ssrdotac_expr ~loc:!@loc noindex Once tac clauses
    | IDENT "do"; n = int_or_var; m = ssrmmod;
                  tac = ssrdotac; clauses = ssrclauses ->
      ssrdotac_expr ~loc:!@loc (mk_index ~loc:!@loc n) m tac clauses
    ] ];
END
(* }}} *)


(* We can't actually parse the direction separately because this   *)
(* would introduce conflicts with the basic ltac syntax.           *)
let pr_ssrseqdir _ _ _ = function
  | L2R -> str ";" ++ spc () ++ str "first "
  | R2L -> str ";" ++ spc () ++ str "last "

ARGUMENT EXTEND ssrseqdir TYPED AS ssrdir PRINTED BY pr_ssrseqdir
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

TACTIC EXTEND ssrtclseq
| [ "YouShouldNotTypeThis" ssrtclarg(tac) ssrseqdir(dir) ssrseqarg(arg) ] ->
  [ V82.tactic (tclSEQAT ist tac dir arg) ]
END
set_pr_ssrtac "tclseq" 5 [ArgSsr "tclarg"; ArgSsr "seqdir"; ArgSsr "seqarg"]

let tclseq_expr ?loc tac dir arg =
  let arg1 = in_gen (rawwit wit_ssrtclarg) tac in
  let arg2 = in_gen (rawwit wit_ssrseqdir) dir in
  let arg3 = in_gen (rawwit wit_ssrseqarg) (check_seqtacarg dir arg) in
  ssrtac_expr ?loc "tclseq" (List.map (fun x -> Tacexpr.TacGeneric x) [arg1; arg2; arg3])

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssr_first: [
    [ tac = ssr_first; ipats = ssrintros_ne -> tclintros_expr ~loc:!@loc tac ipats
    | "["; tacl = LIST0 tactic_expr SEP "|"; "]" -> TacFirst tacl
    ] ];
  ssr_first_else: [
    [ tac1 = ssr_first; tac2 = ssrorelse -> TacOrelse (tac1, tac2)
    | tac = ssr_first -> tac ]];
  tactic_expr: LEVEL "4" [ LEFTA
    [ tac1 = tactic_expr; ";"; IDENT "first"; tac2 = ssr_first_else ->
      TacThen (tac1, tac2)
    | tac = tactic_expr; ";"; IDENT "first"; arg = ssrseqarg ->
      tclseq_expr ~loc:!@loc tac L2R arg
    | tac = tactic_expr; ";"; IDENT "last"; arg = ssrseqarg ->
      tclseq_expr ~loc:!@loc tac R2L arg
    ] ];
END
(* }}} *)

(** 5. Bookkeeping tactics (clear, move, case, elim) *)

(** Generalization (discharge) item *)

(* An item is a switch + term pair.                                     *)

(* type ssrgen = ssrdocc * ssrterm *)

let pr_gen (docc, dt) = pr_docc docc ++ pr_cpattern dt

let pr_ssrgen _ _ _ = pr_gen

ARGUMENT EXTEND ssrgen TYPED AS ssrdocc * cpattern PRINTED BY pr_ssrgen
| [ ssrdocc(docc) cpattern(dt) ] -> [
     match docc with
     | Some [], _ -> CErrors.user_err ~loc (str"Clear flag {} not allowed here")
     | _ -> docc, dt ]
| [ cpattern(dt) ] -> [ nodocc, dt ]
END

let has_occ ((_, occ), _) = occ <> None

(** Generalization (discharge) sequence *)

(* A discharge sequence is represented as a list of up to two   *)
(* lists of d-items, plus an ident list set (the possibly empty *)
(* final clear switch). The main list is empty iff the command  *)
(* is defective, and has length two if there is a sequence of   *)
(* dependent terms (and in that case it is the first of the two *)
(* lists). Thus, the first of the two lists is never empty.     *)

(* type ssrgens = ssrgen list *)
(* type ssrdgens = ssrgens list * ssrclear *)

let gens_sep = function [], [] -> mt | _ -> spc

let pr_dgens pr_gen (gensl, clr) =
  let prgens s gens = str s ++ pr_list spc pr_gen gens in
  let prdeps deps = prgens ": " deps ++ spc () ++ str "/" in
  match gensl with
  | [deps; []] -> prdeps deps ++ pr_clear pr_spc clr
  | [deps; gens] -> prdeps deps ++ prgens " " gens ++ pr_clear spc clr
  | [gens] -> prgens ": " gens ++ pr_clear spc clr
  | _ -> pr_clear pr_spc clr

let pr_ssrdgens _ _ _ = pr_dgens pr_gen

let cons_gen gen = function
  | gens :: gensl, clr -> (gen :: gens) :: gensl, clr
  | _ -> anomaly "missing gen list"

let cons_dep (gensl, clr) =
  if List.length gensl = 1 then ([] :: gensl, clr) else
  CErrors.user_err (Pp.str "multiple dependents switches '/'")

ARGUMENT EXTEND ssrdgens_tl TYPED AS ssrgen list list * ssrclear
                            PRINTED BY pr_ssrdgens
| [ "{" ne_ssrhyp_list(clr) "}" cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkclr clr, dt) dgens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] ->
  [ [[]], clr ]
| [ "{" ssrocc(occ) "}" cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkocc occ, dt) dgens ]
| [ "/" ssrdgens_tl(dgens) ] ->
  [ cons_dep dgens ]
| [ cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (nodocc, dt) dgens ]
| [ ] ->
  [ [[]], [] ]
END

ARGUMENT EXTEND ssrdgens TYPED AS ssrdgens_tl PRINTED BY pr_ssrdgens
| [ ":" ssrgen(gen) ssrdgens_tl(dgens) ] -> [ cons_gen gen dgens ]
END

(** Equations *)

(* argument *)

let pr_eqid = function Some pat -> str " " ++ pr_ipat pat | None -> mt ()
let pr_ssreqid _ _ _ = pr_eqid

(* We must use primitive parsing here to avoid conflicts with the  *)
(* basic move, case, and elim tactics.                             *)
ARGUMENT EXTEND ssreqid TYPED AS ssripatrep option PRINTED BY pr_ssreqid
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let accept_ssreqid strm =
  match Util.stream_nth 0 strm with
  | Tok.IDENT _ -> accept_before_syms [":"] strm
  | Tok.KEYWORD ":" -> ()
  | Tok.KEYWORD pat when List.mem pat ["_"; "?"; "->"; "<-"] ->
                      accept_before_syms [":"] strm
  | _ -> raise Stream.Failure

let test_ssreqid = Gram.Entry.of_parser "test_ssreqid" accept_ssreqid

GEXTEND Gram
  GLOBAL: ssreqid;
  ssreqpat: [
    [ id = Prim.ident -> IPatId id
    | "_" -> IPatAnon Drop
    | "?" -> IPatAnon One
    | occ = ssrdocc; "->" -> (match occ with
      | None, occ -> IPatRewrite (occ, L2R)
      | _ -> CErrors.user_err ~loc:!@loc (str"Only occurrences are allowed here"))
    | occ = ssrdocc; "<-" -> (match occ with
      | None, occ ->  IPatRewrite (occ, R2L)
      | _ -> CErrors.user_err ~loc:!@loc (str "Only occurrences are allowed here"))
    | "->" -> IPatRewrite (allocc, L2R)
    | "<-" -> IPatRewrite (allocc, R2L)
    ]];
  ssreqid: [
    [ test_ssreqid; pat = ssreqpat -> Some pat
    | test_ssreqid -> None
    ]];
END

(** Bookkeeping (discharge-intro) argument *)

(* Since all bookkeeping ssr commands have the same discharge-intro    *)
(* argument format we use a single grammar entry point to parse them.  *)
(* the entry point parses only non-empty arguments to avoid conflicts  *)
(* with the basic Coq tactics.                                         *)

(* type ssrarg = ssrbwdview * (ssreqid * (ssrdgens * ssripats)) *)

let pr_ssrarg _ _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view2 view ++ pr_eqid eqid ++ pr_dgens pr_gen dgens ++ pri ipats

ARGUMENT EXTEND ssrarg TYPED AS ssrfwdview * (ssreqid * (ssrdgens * ssrintros))
   PRINTED BY pr_ssrarg
| [ ssrfwdview(view) ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ view, (eqid, (dgens, ipats)) ]
| [ ssrfwdview(view) ssrclear(clr) ssrintros(ipats) ] ->
  [ view, (None, (([], clr), ipats)) ]
| [ ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ [], (eqid, (dgens, ipats)) ]
| [ ssrclear_ne(clr) ssrintros(ipats) ] ->
  [ [], (None, (([], clr), ipats)) ]
| [ ssrintros_ne(ipats) ] ->
  [ [], (None, (([], []), ipats)) ]
END

(** The "clear" tactic *)

(* We just add a numeric version that clears the n top assumptions. *)

TACTIC EXTEND ssrclear
  | [ "clear" natural(n) ] -> [ tclIPAT (List.init n (fun _ -> IPatAnon Drop)) ]
END

(** The "move" tactic *)

(* TODO: review this, in particular the => _ and => [] cases *)
let rec improper_intros = function
  | IPatSimpl _ :: ipats -> improper_intros ipats
  | (IPatId _ | IPatAnon _ | IPatCase _ | IPatDispatch _) :: _ -> false
  | _ -> true (* FIXME *)

let check_movearg = function
  | view, (eqid, _) when view <> [] && eqid <> None ->
    CErrors.user_err (Pp.str "incompatible view and equation in move tactic")
  | view, (_, (([gen :: _], _), _)) when view <> [] && has_occ gen ->
    CErrors.user_err (Pp.str "incompatible view and occurrence switch in move tactic")
  | _, (_, ((dgens, _), _)) when List.length dgens > 1 ->
    CErrors.user_err (Pp.str "dependents switch `/' in move tactic")
  | _, (eqid, (_, ipats)) when eqid <> None && improper_intros ipats ->
    CErrors.user_err (Pp.str "no proper intro pattern for equation in move tactic")
  | arg -> arg

ARGUMENT EXTEND ssrmovearg TYPED AS ssrarg PRINTED BY pr_ssrarg
| [ ssrarg(arg) ] -> [ check_movearg arg ]
END

let movearg_of_parsed_movearg (v,(eq,(dg,ip))) =
  (v,(eq,(ssrdgens_of_parsed_dgens dg,ip)))

TACTIC EXTEND ssrmove
| [ "move" ssrmovearg(arg) ssrrpat(pat) ] ->
  [ ssrmovetac (movearg_of_parsed_movearg arg) <*> tclIPAT [pat] ]
| [ "move" ssrmovearg(arg) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrmovetac (movearg_of_parsed_movearg arg)) clauses ]
| [ "move" ssrrpat(pat) ] -> [ tclIPAT [pat] ]
| [ "move" ] -> [ ssrsmovetac ]
END

let check_casearg = function
| view, (_, (([_; gen :: _], _), _)) when view <> [] && has_occ gen ->
  CErrors.user_err (Pp.str "incompatible view and occurrence switch in dependent case tactic")
| arg -> arg

ARGUMENT EXTEND ssrcasearg TYPED AS ssrarg PRINTED BY pr_ssrarg
| [ ssrarg(arg) ] -> [ check_casearg arg ]
END

TACTIC EXTEND ssrcase
| [ "case" ssrcasearg(arg) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrcasetac (movearg_of_parsed_movearg arg)) clauses ]
| [ "case" ] -> [ ssrscasetoptac ]
END

(** The "elim" tactic *)

TACTIC EXTEND ssrelim
| [ "elim" ssrarg(arg) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrelimtac (movearg_of_parsed_movearg arg)) clauses ]
| [ "elim" ] -> [ ssrselimtoptac ]
END

(** 6. Backward chaining tactics: apply, exact, congr. *)

(** The "apply" tactic *)

let pr_agen (docc, dt) = pr_docc docc ++ pr_term dt
let pr_ssragen _ _ _ = pr_agen
let pr_ssragens _ _ _ = pr_dgens pr_agen

ARGUMENT EXTEND ssragen TYPED AS ssrdocc * ssrterm PRINTED BY pr_ssragen
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ] -> [ mkclr clr, dt ]
| [ ssrterm(dt) ] -> [ nodocc, dt ]
END

ARGUMENT EXTEND ssragens TYPED AS ssragen list list * ssrclear 
PRINTED BY pr_ssragens
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (mkclr clr, dt) agens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ [[]], clr]
| [ ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (nodocc, dt) agens ]
| [ ] -> [ [[]], [] ]
END

let mk_applyarg views agens intros = views, (agens, intros)

let pr_ssraarg _ _ _ (view, (dgens, ipats)) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view view ++ pr_dgens pr_agen dgens ++ pri ipats

ARGUMENT EXTEND ssrapplyarg 
TYPED AS ssrbwdview * (ssragens * ssrintros)
PRINTED BY pr_ssraarg
| [ ":" ssragen(gen) ssragens(dgens) ssrintros(intros) ] ->
  [ mk_applyarg [] (cons_gen gen dgens) intros ]
| [ ssrclear_ne(clr) ssrintros(intros) ] ->
  [ mk_applyarg [] ([], clr) intros ]
| [ ssrintros_ne(intros) ] ->
  [ mk_applyarg [] ([], []) intros ]
| [ ssrbwdview(view) ":" ssragen(gen) ssragens(dgens) ssrintros(intros) ] ->
  [ mk_applyarg view (cons_gen gen dgens) intros ]
| [ ssrbwdview(view) ssrclear(clr) ssrintros(intros) ] ->
  [ mk_applyarg view ([], clr) intros ]
    END

TACTIC EXTEND ssrapply
| [ "apply" ssrapplyarg(arg) ] -> [
     let views, (gens_clr, intros) = arg in
     inner_ssrapplytac views gens_clr ist <*> tclIPATssr intros ]
| [ "apply" ] -> [ apply_top_tac ]
END

(** The "exact" tactic *)

let mk_exactarg views dgens = mk_applyarg views dgens []

ARGUMENT EXTEND ssrexactarg TYPED AS ssrapplyarg PRINTED BY pr_ssraarg
| [ ":" ssragen(gen) ssragens(dgens) ] ->
  [ mk_exactarg [] (cons_gen gen dgens) ]
| [ ssrbwdview(view) ssrclear(clr) ] ->
  [ mk_exactarg view ([], clr) ]
| [ ssrclear_ne(clr) ] ->
  [ mk_exactarg [] ([], clr) ]
END

let vmexacttac pf =
  Goal.nf_enter begin fun gl ->
  exact_no_check (EConstr.mkCast (pf, _vmcast, Tacmach.New.pf_concl gl))
  end

TACTIC EXTEND ssrexact
| [ "exact" ssrexactarg(arg) ] -> [
     let views, (gens_clr, _) = arg in
     V82.tactic (tclBY (V82.of_tactic (inner_ssrapplytac views gens_clr ist))) ]
| [ "exact" ] -> [
     V82.tactic (Tacticals.tclORELSE (donetac ~-1) (tclBY (V82.of_tactic apply_top_tac))) ]
| [ "exact" "<:" lconstr(pf) ] -> [ vmexacttac pf ]
END

(** The "congr" tactic *)

(* type ssrcongrarg = open_constr * (int * constr) *)

let pr_ssrcongrarg _ _ _ ((n, f), dgens) =
  (if n <= 0 then mt () else str " " ++ int n) ++
  str " " ++ pr_term f ++ pr_dgens pr_gen dgens

ARGUMENT EXTEND ssrcongrarg TYPED AS (int * ssrterm) * ssrdgens
  PRINTED BY pr_ssrcongrarg
| [ natural(n) constr(c) ssrdgens(dgens) ] -> [ (n, mk_term xNoFlag c), dgens ]
| [ natural(n) constr(c) ] -> [ (n, mk_term xNoFlag c),([[]],[]) ]
| [ constr(c) ssrdgens(dgens) ] -> [ (0, mk_term xNoFlag c), dgens ]
| [ constr(c) ] -> [ (0, mk_term xNoFlag c), ([[]],[]) ]
END



TACTIC EXTEND ssrcongr
| [ "congr" ssrcongrarg(arg) ] ->
[ let arg, dgens = arg in
  V82.tactic begin
    match dgens with
    | [gens], clr -> Tacticals.tclTHEN (genstac (gens,clr)) (newssrcongrtac arg ist)
    | _ -> errorstrm (str"Dependent family abstractions not allowed in congr")
  end]
END

(** 7. Rewriting tactics (rewrite, unlock) *)

(** Coq rewrite compatibility flag *)

(** Rewrite clear/occ switches *)

let pr_rwocc = function
  | None, None -> mt ()
  | None, occ -> pr_occ occ
  | Some clr,  _ ->  pr_clear_ne clr

let pr_ssrrwocc _ _ _ = pr_rwocc

ARGUMENT EXTEND ssrrwocc TYPED AS ssrdocc PRINTED BY pr_ssrrwocc
| [ "{" ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
| [ ] -> [ noclr ]
END

(** Rewrite rules *)

let pr_rwkind = function
  | RWred s -> pr_simpl s
  | RWdef -> str "/"
  | RWeq -> mt ()

let wit_ssrrwkind = add_genarg "ssrrwkind" pr_rwkind

let pr_rule = function
  | RWred s, _ -> pr_simpl s
  | RWdef, r-> str "/" ++ pr_term r
  | RWeq, r -> pr_term r

let pr_ssrrule _ _ _ = pr_rule

let noruleterm loc = mk_term xNoFlag (mkCProp loc)

ARGUMENT EXTEND ssrrule_ne TYPED AS ssrrwkind * ssrterm PRINTED BY pr_ssrrule
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

GEXTEND Gram
  GLOBAL: ssrrule_ne;
  ssrrule_ne : [
    [ test_not_ssrslashnum; x =
        [ "/"; t = ssrterm -> RWdef, t
        | t = ssrterm -> RWeq, t 
        | s = ssrsimpl_ne -> RWred s, noruleterm (Some !@loc)
        ] -> x
    | s = ssrsimpl_ne -> RWred s, noruleterm (Some !@loc)
  ]];
END

ARGUMENT EXTEND ssrrule TYPED AS ssrrule_ne PRINTED BY pr_ssrrule
  | [ ssrrule_ne(r) ] -> [ r ]
  | [ ] -> [ RWred Nop, noruleterm (Some loc) ]
END

(** Rewrite arguments *)

let pr_option f = function None -> mt() | Some x -> f x
let pr_pattern_squarep= pr_option (fun r -> str "[" ++ pr_rpattern r ++ str "]")
let pr_ssrpattern_squarep _ _ _ = pr_pattern_squarep
let pr_rwarg ((d, m), ((docc, rx), r)) =
  pr_rwdir d ++ pr_mult m ++ pr_rwocc docc ++ pr_pattern_squarep rx ++ pr_rule r

let pr_ssrrwarg _ _ _ = pr_rwarg

ARGUMENT EXTEND ssrpattern_squarep
TYPED AS rpattern option PRINTED BY pr_ssrpattern_squarep
  | [ "[" rpattern(rdx) "]" ] -> [ Some rdx ]
  | [ ] -> [ None ]
END

ARGUMENT EXTEND ssrpattern_ne_squarep
TYPED AS rpattern option PRINTED BY pr_ssrpattern_squarep
  | [ "[" rpattern(rdx) "]" ] -> [ Some rdx ]
END


ARGUMENT EXTEND ssrrwarg
  TYPED AS (ssrdir * ssrmult) * ((ssrdocc * rpattern option) * ssrrule)
  PRINTED BY pr_ssrrwarg
  | [ "-" ssrmult(m) ssrrwocc(docc) ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (R2L, m) (docc, rx) r ]
  | [ "-/" ssrterm(t) ] ->     (* just in case '-/' should become a token *)
    [ mk_rwarg (R2L, nomult) norwocc (RWdef, t) ]
  | [ ssrmult_ne(m) ssrrwocc(docc) ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (L2R, m) (docc, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrpattern_ne_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrrule(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, None) r ]
  | [ "{" ssrocc(occ) "}" ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkocc occ, rx) r ]
  | [ "{" "}" ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (nodocc, rx) r ]
  | [ ssrpattern_ne_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (noclr, rx) r ]
  | [ ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult norwocc r ]
END

TACTIC EXTEND ssrinstofruleL2R
| [ "ssrinstancesofruleL2R" ssrterm(arg) ] -> [ V82.tactic (ssrinstancesofrule ist L2R arg) ]
END
TACTIC EXTEND ssrinstofruleR2L
| [ "ssrinstancesofruleR2L" ssrterm(arg) ] -> [ V82.tactic (ssrinstancesofrule ist R2L arg) ]
END

(** Rewrite argument sequence *)

(* type ssrrwargs = ssrrwarg list *)

let pr_ssrrwargs _ _ _ rwargs = pr_list spc pr_rwarg rwargs

ARGUMENT EXTEND ssrrwargs TYPED AS ssrrwarg list PRINTED BY pr_ssrrwargs
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let ssr_rw_syntax = Summary.ref ~name:"SSR:rewrite" true

let _ =
  Goptions.declare_bool_option
    { Goptions.optname  = "ssreflect rewrite";
      Goptions.optkey   = ["SsrRewrite"];
      Goptions.optread  = (fun _ -> !ssr_rw_syntax);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b -> ssr_rw_syntax := b) }

let test_ssr_rw_syntax =
  let test strm  =
    if not !ssr_rw_syntax then raise Stream.Failure else
    if is_ssr_loaded () then () else
    match Util.stream_nth 0 strm with
    | Tok.KEYWORD key when List.mem key.[0] ['{'; '['; '/'] -> ()
    | _ -> raise Stream.Failure in
  Gram.Entry.of_parser "test_ssr_rw_syntax" test

GEXTEND Gram
  GLOBAL: ssrrwargs;
  ssrrwargs: [[ test_ssr_rw_syntax; a = LIST1 ssrrwarg -> a ]];
END

(** The "rewrite" tactic *)

TACTIC EXTEND ssrrewrite
  | [ "rewrite" ssrrwargs(args) ssrclauses(clauses) ] ->
    [ tclCLAUSES (old_tac (ssrrewritetac ist args)) clauses ]
END

(** The "unlock" tactic *)

let pr_unlockarg (occ, t) = pr_occ occ ++ pr_term t
let pr_ssrunlockarg _ _ _ = pr_unlockarg

ARGUMENT EXTEND ssrunlockarg TYPED AS ssrocc * ssrterm
  PRINTED BY pr_ssrunlockarg
  | [  "{" ssrocc(occ) "}" ssrterm(t) ] -> [ occ, t ]
  | [  ssrterm(t) ] -> [ None, t ]
END

let pr_ssrunlockargs _ _ _ args = pr_list spc pr_unlockarg args

ARGUMENT EXTEND ssrunlockargs TYPED AS ssrunlockarg list
  PRINTED BY pr_ssrunlockargs
  | [  ssrunlockarg_list(args) ] -> [ args ]
END

TACTIC EXTEND ssrunlock
  | [ "unlock" ssrunlockargs(args) ssrclauses(clauses) ] ->
    [ tclCLAUSES (old_tac (unlocktac ist args)) clauses ]
END

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)


TACTIC EXTEND ssrpose
| [ "pose" ssrfixfwd(ffwd) ] -> [ V82.tactic (ssrposetac ffwd) ]
| [ "pose" ssrcofixfwd(ffwd) ] -> [ V82.tactic (ssrposetac ffwd) ]
| [ "pose" ssrfwdid(id) ssrposefwd(fwd) ] -> [ V82.tactic (ssrposetac (id, fwd)) ]
END

(** The "set" tactic *)

(* type ssrsetfwd = ssrfwd * ssrdocc *)

TACTIC EXTEND ssrset
| [ "set" ssrfwdid(id) ssrsetfwd(fwd) ssrclauses(clauses) ] ->
  [ tclCLAUSES (old_tac (ssrsettac id fwd)) clauses ]
END

(** The "have" tactic *)

(* type ssrhavefwd = ssrfwd * ssrhint *)


(* Pltac. *)

(* The standard TACTIC EXTEND does not work for abstract *)
GEXTEND Gram
  GLOBAL: tactic_expr;
  tactic_expr: LEVEL "3"
    [ RIGHTA [ IDENT "abstract"; gens = ssrdgens ->
               ssrtac_expr ~loc:!@loc "abstract"
                [Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_ssrdgens) gens)] ]];
END
TACTIC EXTEND ssrabstract
| [ "abstract" ssrdgens(gens) ] -> [
    if List.length (fst gens) <> 1 then
      errorstrm (str"dependents switches '/' not allowed here");
    Ssripats.ssrabstract (ssrdgens_of_parsed_dgens gens) ]
END

TACTIC EXTEND ssrhave
| [ "have" ssrhavefwdwbinders(fwd) ] ->
  [ V82.tactic (havetac ist fwd false false) ]
END

TACTIC EXTEND ssrhavesuff
| [ "have" "suff" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ V82.tactic (havetac ist (false,(pats,fwd)) true false) ]
END

TACTIC EXTEND ssrhavesuffices
| [ "have" "suffices" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ V82.tactic (havetac ist (false,(pats,fwd)) true false) ]
END

TACTIC EXTEND ssrsuffhave
| [ "suff" "have" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ V82.tactic (havetac ist (false,(pats,fwd)) true true) ]
END

TACTIC EXTEND ssrsufficeshave
| [ "suffices" "have" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ V82.tactic (havetac ist (false,(pats,fwd)) true true) ]
END

(** The "suffice" tactic *)

let pr_ssrsufffwdwbinders _ _ prt (hpats, (fwd, hint)) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrsufffwd
  TYPED AS ssrhpats * (ssrfwd * ssrhint) PRINTED BY pr_ssrsufffwdwbinders
| [ ssrhpats(pats) ssrbinder_list(bs)  ":" ast_closure_lterm(t) ssrhint(hint) ] ->
  [ let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let fwd = mkFwdHint ":" t in
    (((clr, pats), allbinders), simpl), (bind_fwd allbs fwd, hint) ]
END


TACTIC EXTEND ssrsuff
| [ "suff" ssrsufffwd(fwd) ] -> [ V82.tactic (sufftac ist fwd) ]
END

TACTIC EXTEND ssrsuffices
| [ "suffices" ssrsufffwd(fwd) ] -> [ V82.tactic (sufftac ist fwd) ]
END

(** The "wlog" (Without Loss Of Generality) tactic *)

(* type ssrwlogfwd = ssrwgen list * ssrfwd *)

let pr_ssrwlogfwd _ _ _ (gens, t) =
  str ":" ++ pr_list mt pr_wgen gens ++ spc() ++ pr_fwd t

ARGUMENT EXTEND ssrwlogfwd TYPED AS ssrwgen list * ssrfwd
                         PRINTED BY pr_ssrwlogfwd
| [ ":" ssrwgen_list(gens) "/" ast_closure_lterm(t) ] -> [ gens, mkFwdHint "/" t]
END

        
TACTIC EXTEND ssrwlog
| [ "wlog" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ V82.tactic (wlogtac ist pats fwd hint false `NoGen) ]
END

TACTIC EXTEND ssrwlogs
| [ "wlog" "suff" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwlogss
| [ "wlog" "suffices" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ]->
  [ V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwithoutloss
| [ "without" "loss" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ V82.tactic (wlogtac ist pats fwd hint false `NoGen) ]
END

TACTIC EXTEND ssrwithoutlosss
| [ "without" "loss" "suff" 
    ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwithoutlossss
| [ "without" "loss" "suffices" 
    ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ]->
  [ V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

(* Generally have *)
let pr_idcomma _ _ _ = function
  | None -> mt()
  | Some None -> str"_, "
  | Some (Some id) -> pr_id id ++ str", "

ARGUMENT EXTEND ssr_idcomma TYPED AS ident option option PRINTED BY pr_idcomma
  | [ ] -> [ None ]
END

let accept_idcomma strm =
  match stream_nth 0 strm with
  | Tok.IDENT _ | Tok.KEYWORD "_" -> accept_before_syms [","] strm
  | _ -> raise Stream.Failure

let test_idcomma = Gram.Entry.of_parser "test_idcomma" accept_idcomma

GEXTEND Gram
  GLOBAL: ssr_idcomma;
  ssr_idcomma: [ [ test_idcomma; 
    ip = [ id = IDENT -> Some (Id.of_string id) | "_" -> None ]; "," ->
    Some ip
  ] ];
END

let augment_preclr clr1 (((clr0, x),y),z) = (((clr1 @ clr0, x),y),z)

TACTIC EXTEND ssrgenhave
| [ "gen" "have" ssrclear(clr)
    ssr_idcomma(id) ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ let pats = augment_preclr clr pats in
    V82.tactic (wlogtac ist pats fwd hint false (`Gen id)) ]
END

TACTIC EXTEND ssrgenhave2
| [ "generally" "have" ssrclear(clr)
    ssr_idcomma(id) ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ let pats = augment_preclr clr pats in
    V82.tactic (wlogtac ist pats fwd hint false (`Gen id)) ]
END

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.set_keyword_state frozen_lexer ;;


(* vim: set filetype=ocaml foldmethod=marker: *)
