(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Genarg
open Stdarg
open Tacarg
open Pcoq.Prim
open Pcoq.Constr
open Names
open Tacmach
open Tacexpr
open Taccoerce
open Tacinterp
open Locus

(** Adding scopes for generic arguments not defined through ARGUMENT EXTEND *)

let create_generic_quotation name e wit =
  let inject (loc, v) = Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit) v) in
  Tacentries.create_ltac_quotation name inject (e, None)

let () = create_generic_quotation "integer" Pcoq.Prim.integer Stdarg.wit_int
let () = create_generic_quotation "string" Pcoq.Prim.string Stdarg.wit_string

let () = create_generic_quotation "ident" Pcoq.Prim.ident Stdarg.wit_ident
let () = create_generic_quotation "reference" Pcoq.Prim.reference Stdarg.wit_ref
let () = create_generic_quotation "uconstr" Pcoq.Constr.lconstr Stdarg.wit_uconstr
let () = create_generic_quotation "constr" Pcoq.Constr.lconstr Stdarg.wit_constr
let () = create_generic_quotation "ipattern" Pltac.simple_intropattern wit_intro_pattern
let () = create_generic_quotation "open_constr" Pcoq.Constr.lconstr Stdarg.wit_open_constr
let () =
  let inject (loc, v) = Tacexpr.Tacexp v in
  Tacentries.create_ltac_quotation "ltac" inject (Pltac.tactic_expr, Some 5)

(** Backward-compatible tactic notation entry names *)

let () =
  let register name entry = Tacentries.register_tactic_notation_entry name entry in
  register "hyp" wit_var;
  register "simple_intropattern" wit_intro_pattern;
  register "integer" wit_integer;
  register "reference" wit_ref;
  ()

(* Rewriting orientation *)

let _ =
  Mltop.declare_cache_obj
    (fun () -> Metasyntax.add_token_obj "<-";
               Metasyntax.add_token_obj "->")
    "ltac_plugin"

let pr_orient _prc _prlc _prt = function
  | true -> Pp.mt ()
  | false -> Pp.str " <-"

ARGUMENT EXTEND orient TYPED AS bool PRINTED BY pr_orient
| [ "->" ] -> [ true ]
| [ "<-" ] -> [ false ]
| [ ] -> [ true ]
END

let pr_int _ _ _ i = Pp.int i

let _natural = Pcoq.Prim.natural

ARGUMENT EXTEND natural TYPED AS int PRINTED BY pr_int
| [ _natural(i) ] -> [ i ]
END

let pr_orient = pr_orient () () ()


let pr_int_list = Pp.pr_sequence Pp.int
let pr_int_list_full _prc _prlc _prt l = pr_int_list l

let pr_occurrences _prc _prlc _prt l =
  match l with
    | ArgArg x -> pr_int_list x
    | ArgVar { CAst.loc = loc; v=id } -> Id.print id

let occurrences_of = function
  | [] -> NoOccurrences
  | n::_ as nl when n < 0 -> AllOccurrencesBut (List.map abs nl)
  | nl ->
      if List.exists (fun n -> n < 0) nl then
        CErrors.user_err Pp.(str "Illegal negative occurrence number.");
      OnlyOccurrences nl

let coerce_to_int v = match Value.to_int v with
  | None -> raise (CannotCoerceTo "an integer")
  | Some n -> n

let int_list_of_VList v = match Value.to_list v with
| Some l -> List.map (fun n -> coerce_to_int n) l
| _ -> raise (CannotCoerceTo "an integer")

let interp_occs ist gl l =
  match l with
    | ArgArg x -> x
    | ArgVar ({ CAst.v = id } as locid) ->
	(try int_list_of_VList (Id.Map.find id ist.lfun)
	  with Not_found | CannotCoerceTo _ -> [interp_int ist locid])
let interp_occs ist gl l =
  Tacmach.project gl , interp_occs ist gl l

let glob_occs ist l = l

let subst_occs evm l = l

ARGUMENT EXTEND occurrences
  TYPED AS int list
  PRINTED BY pr_int_list_full

  INTERPRETED BY interp_occs
  GLOBALIZED BY glob_occs
  SUBSTITUTED BY subst_occs

  RAW_PRINTED BY pr_occurrences
  GLOB_PRINTED BY pr_occurrences

| [ ne_integer_list(l) ] -> [ ArgArg l ]
| [ var(id) ] -> [ ArgVar id ]
END

let pr_occurrences = pr_occurrences () () ()

let pr_gen prc _prlc _prtac c = prc c

let pr_globc _prc _prlc _prtac (_,glob) =
  let _, env = Pfedit.get_current_context () in
  Printer.pr_glob_constr_env env glob

let interp_glob ist gl (t,_) = Tacmach.project gl , (ist,t)

let glob_glob = Tacintern.intern_constr

let pr_lconstr _ prc _ c = prc c

let subst_glob = Tacsubst.subst_glob_constr_and_expr

ARGUMENT EXTEND glob
    PRINTED BY pr_globc

     INTERPRETED BY interp_glob
     GLOBALIZED BY glob_glob
     SUBSTITUTED BY subst_glob

     RAW_PRINTED BY pr_gen
     GLOB_PRINTED BY pr_gen
  [ constr(c) ] -> [ c ]
END

let l_constr = Pcoq.Constr.lconstr

ARGUMENT EXTEND lconstr
    TYPED AS constr
    PRINTED BY pr_lconstr
  [ l_constr(c) ] -> [ c ]
END

ARGUMENT EXTEND lglob
  TYPED AS glob
    PRINTED BY pr_globc

     INTERPRETED BY interp_glob
     GLOBALIZED BY glob_glob
     SUBSTITUTED BY subst_glob

     RAW_PRINTED BY pr_gen
     GLOB_PRINTED BY pr_gen
  [ lconstr(c) ] -> [ c ]
END

let interp_casted_constr ist gl c =
  interp_constr_gen (Pretyping.OfType (pf_concl gl)) ist (pf_env gl) (project gl) c

ARGUMENT EXTEND casted_constr
  TYPED AS constr
  PRINTED BY pr_gen
  INTERPRETED BY interp_casted_constr
  [ constr(c) ] -> [ c ]
END

type 'id gen_place= ('id * hyp_location_flag,unit) location

type loc_place = lident gen_place
type place = Id.t gen_place

let pr_gen_place pr_id = function
    ConclLocation () -> Pp.mt ()
  | HypLocation (id,InHyp) -> str "in " ++ pr_id id
  | HypLocation (id,InHypTypeOnly) ->
      str "in (Type of " ++ pr_id id ++ str ")"
  | HypLocation (id,InHypValueOnly) ->
      str "in (Value of " ++ pr_id id ++ str ")"

let pr_loc_place _ _ _ = pr_gen_place (fun { CAst.v = id } -> Id.print id)
let pr_place _ _ _ = pr_gen_place Id.print
let pr_hloc = pr_loc_place () () ()

let intern_place ist = function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id,hl) -> HypLocation (Tacintern.intern_hyp ist id,hl)

let interp_place ist env sigma = function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id,hl) -> HypLocation (Tacinterp.interp_hyp ist env sigma id,hl)

let interp_place ist gl p =
  Tacmach.project gl , interp_place ist (Tacmach.pf_env gl) (Tacmach.project gl) p

let subst_place subst pl = pl

ARGUMENT EXTEND hloc
    PRINTED BY pr_place
    INTERPRETED BY interp_place
    GLOBALIZED BY intern_place
    SUBSTITUTED BY subst_place
    RAW_PRINTED BY pr_loc_place
    GLOB_PRINTED BY pr_loc_place
  [ ] ->
    [ ConclLocation () ]
  |  [ "in" "|-" "*" ] ->
    [ ConclLocation () ]
| [ "in" ident(id) ] ->
    [ HypLocation ((CAst.make id),InHyp) ]
| [ "in" "(" "Type" "of" ident(id) ")" ] ->
    [ HypLocation ((CAst.make id),InHypTypeOnly) ]
| [ "in" "(" "Value" "of" ident(id) ")" ] ->
    [ HypLocation ((CAst.make id),InHypValueOnly) ]

 END

let pr_rename _ _ _ (n, m) = Id.print n ++ str " into " ++ Id.print m

ARGUMENT EXTEND rename
  TYPED AS ident * ident
  PRINTED BY pr_rename
| [ ident(n) "into" ident(m) ] -> [ (n, m) ]
END

(* Julien: Mise en commun des differentes version de replace with in by *)

let pr_by_arg_tac _prc _prlc prtac opt_c =
  match opt_c with
    | None -> mt ()
    | Some t -> hov 2 (str "by" ++ spc () ++ prtac (3,Notation_gram.E) t)

ARGUMENT EXTEND by_arg_tac
  TYPED AS tactic_opt
  PRINTED BY pr_by_arg_tac
| [ "by" tactic3(c) ] -> [ Some c ]
| [ ] -> [ None ]
END

let pr_by_arg_tac prtac opt_c = pr_by_arg_tac () () prtac opt_c

let pr_in_clause _ _ _ cl = Pptactic.pr_in_clause Ppconstr.pr_lident cl
let pr_in_top_clause _ _ _ cl = Pptactic.pr_in_clause Id.print cl
let in_clause' = Pltac.in_clause

ARGUMENT EXTEND in_clause
  TYPED AS clause_dft_concl
  PRINTED BY pr_in_top_clause
  RAW_TYPED AS clause_dft_concl
  RAW_PRINTED BY pr_in_clause
  GLOB_TYPED AS clause_dft_concl
  GLOB_PRINTED BY pr_in_clause
| [ in_clause'(cl) ] -> [ cl ]
END

let local_test_lpar_id_colon =
  let err () = raise Stream.Failure in
  Pcoq.Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
      match Util.stream_nth 0 strm with
        | Tok.KEYWORD "(" ->
            (match Util.stream_nth 1 strm with
              | Tok.IDENT _ ->
                  (match Util.stream_nth 2 strm with
                    | Tok.KEYWORD ":" -> ()
                    | _ -> err ())
              | _ -> err ())
        | _ -> err ())

let pr_lpar_id_colon _ _ _ _ = mt ()

ARGUMENT EXTEND test_lpar_id_colon TYPED AS unit PRINTED BY pr_lpar_id_colon
| [ local_test_lpar_id_colon(x) ] -> [ () ]
END

(* spiwack: the print functions are incomplete, but I don't know what they are
	used for *)
let pr_r_int31_field i31f =
  str "int31 " ++
  match i31f with
    | Retroknowledge.Int31Bits -> str "bits"
    | Retroknowledge.Int31Type -> str "type"
    | Retroknowledge.Int31Twice -> str "twice"
    | Retroknowledge.Int31TwicePlusOne -> str "twice plus one"
    | Retroknowledge.Int31Phi -> str "phi"
    | Retroknowledge.Int31PhiInv -> str "phi inv"
    | Retroknowledge.Int31Plus -> str "plus"
    | Retroknowledge.Int31Times -> str "times"
    | Retroknowledge.Int31Constructor -> assert false
    | Retroknowledge.Int31PlusC -> str "plusc"
    | Retroknowledge.Int31PlusCarryC -> str "pluscarryc"
    | Retroknowledge.Int31Minus -> str "minus"
    | Retroknowledge.Int31MinusC -> str "minusc"
    | Retroknowledge.Int31MinusCarryC -> str "minuscarryc"
    | Retroknowledge.Int31TimesC -> str "timesc"
    | Retroknowledge.Int31Div21 -> str "div21"
    | Retroknowledge.Int31Div -> str "div"
    | Retroknowledge.Int31Diveucl -> str "diveucl"
    | Retroknowledge.Int31AddMulDiv -> str "addmuldiv"
    | Retroknowledge.Int31Compare -> str "compare"
    | Retroknowledge.Int31Head0 -> str "head0"
    | Retroknowledge.Int31Tail0 -> str "tail0"
    | Retroknowledge.Int31Lor -> str "lor"
    | Retroknowledge.Int31Land -> str "land"
    | Retroknowledge.Int31Lxor -> str "lxor"

let pr_retroknowledge_field f =
  match f with
 (* | Retroknowledge.KEq -> str "equality"
  | Retroknowledge.KNat natf -> pr_r_nat_field () () () natf
  | Retroknowledge.KN nf -> pr_r_n_field () () () nf *)
  | Retroknowledge.KInt31 (group, i31f) -> (pr_r_int31_field i31f) ++
                                           spc () ++ str "in " ++ qs group

VERNAC ARGUMENT EXTEND retroknowledge_int31
PRINTED BY pr_r_int31_field
| [ "int31" "bits" ] -> [ Retroknowledge.Int31Bits ]
| [ "int31" "type" ] -> [ Retroknowledge.Int31Type ]
| [ "int31" "twice" ] -> [ Retroknowledge.Int31Twice ]
| [ "int31" "twice" "plus" "one" ] -> [ Retroknowledge.Int31TwicePlusOne ]
| [ "int31" "phi" ] -> [ Retroknowledge.Int31Phi ]
| [ "int31" "phi" "inv" ] -> [ Retroknowledge.Int31PhiInv ]
| [ "int31" "plus" ] -> [ Retroknowledge.Int31Plus ]
| [ "int31" "plusc" ] -> [ Retroknowledge.Int31PlusC ]
| [ "int31" "pluscarryc" ] -> [ Retroknowledge.Int31PlusCarryC ]
| [ "int31" "minus" ] -> [ Retroknowledge.Int31Minus ]
| [ "int31" "minusc" ] -> [ Retroknowledge.Int31MinusC ]
| [ "int31" "minuscarryc" ] -> [ Retroknowledge.Int31MinusCarryC ]
| [ "int31" "times" ] -> [ Retroknowledge.Int31Times ]
| [ "int31" "timesc" ] -> [ Retroknowledge.Int31TimesC ]
| [ "int31" "div21" ] -> [ Retroknowledge.Int31Div21 ]
| [ "int31" "div" ] -> [ Retroknowledge.Int31Div ]
| [ "int31" "diveucl" ] -> [ Retroknowledge.Int31Diveucl ]
| [ "int31" "addmuldiv" ] -> [ Retroknowledge.Int31AddMulDiv ]
| [ "int31" "compare" ] -> [ Retroknowledge.Int31Compare ]
| [ "int31" "head0" ] -> [ Retroknowledge.Int31Head0 ]
| [ "int31" "tail0" ] -> [ Retroknowledge.Int31Tail0 ]
| [ "int31" "lor" ] -> [ Retroknowledge.Int31Lor ]
| [ "int31" "land" ] -> [ Retroknowledge.Int31Land ]
| [ "int31" "lxor" ] -> [ Retroknowledge.Int31Lxor ]
END

VERNAC ARGUMENT EXTEND retroknowledge_field
PRINTED BY pr_retroknowledge_field
(*| [ "equality" ] -> [ Retroknowledge.KEq ]
| [ retroknowledge_nat(n)] -> [ Retroknowledge.KNat n ]
| [ retroknowledge_binary_n (n)] -> [ Retroknowledge.KN n ]*)
| [ retroknowledge_int31 (i) "in" string(g)] -> [ Retroknowledge.KInt31(g,i) ]
END
