(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Pp
open Genarg
open Names
open Tacexpr
open Taccoerce
open Tacinterp
open Misctypes
open Locus

(* Rewriting orientation *)

let _ = Metasyntax.add_token_obj "<-"
let _ = Metasyntax.add_token_obj "->"

let pr_orient _prc _prlc _prt = function
  | true -> Pp.mt ()
  | false -> Pp.str " <-"

ARGUMENT EXTEND orient TYPED AS bool PRINTED BY pr_orient
| [ "->" ] -> [ true ]
| [ "<-" ] -> [ false ]
| [ ] -> [ true ]
END

let pr_orient = pr_orient () () ()


let pr_int_list = Pp.pr_sequence Pp.int
let pr_int_list_full _prc _prlc _prt l = pr_int_list l

let pr_occurrences _prc _prlc _prt l =
  match l with
    | ArgArg x -> pr_int_list x
    | ArgVar (loc, id) -> Nameops.pr_id id

let occurrences_of = function
  | [] -> NoOccurrences
  | n::_ as nl when n < 0 -> AllOccurrencesBut (List.map abs nl)
  | nl ->
      if List.exists (fun n -> n < 0) nl then
        Errors.error "Illegal negative occurrence number.";
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
    | ArgVar (_,id as locid) ->
	(try int_list_of_VList (Id.Map.find id ist.lfun)
	  with Not_found | CannotCoerceTo _ -> [interp_int ist locid])
let interp_occs ist gl l =
  Tacmach.project gl , interp_occs ist gl l

let glob_occs ist l = l

let subst_occs evm l = l

ARGUMENT EXTEND occurrences
  PRINTED BY pr_int_list_full

  INTERPRETED BY interp_occs
  GLOBALIZED BY glob_occs
  SUBSTITUTED BY subst_occs

  RAW_TYPED AS occurrences_or_var
  RAW_PRINTED BY pr_occurrences

  GLOB_TYPED AS occurrences_or_var
  GLOB_PRINTED BY pr_occurrences

| [ ne_integer_list(l) ] -> [ ArgArg l ]
| [ var(id) ] -> [ ArgVar id ]
END

let pr_occurrences = pr_occurrences () () ()

let pr_gen prc _prlc _prtac c = prc c

let pr_globc _prc _prlc _prtac (_,glob) = Printer.pr_glob_constr glob

let interp_glob ist gl (t,_) = Tacmach.project gl , (ist,t)

let glob_glob = Tacintern.intern_constr

let subst_glob = Tacsubst.subst_glob_constr_and_expr

ARGUMENT EXTEND glob
    PRINTED BY pr_globc

     INTERPRETED BY interp_glob
     GLOBALIZED BY glob_glob
     SUBSTITUTED BY subst_glob

     RAW_TYPED AS constr_expr
     RAW_PRINTED BY pr_gen

     GLOB_TYPED AS glob_constr_and_expr
     GLOB_PRINTED BY pr_gen
  [ constr(c) ] -> [ c ]
END

ARGUMENT EXTEND lglob
    PRINTED BY pr_globc

     INTERPRETED BY interp_glob
     GLOBALIZED BY glob_glob
     SUBSTITUTED BY subst_glob

     RAW_TYPED AS constr_expr
     RAW_PRINTED BY pr_gen

     GLOB_TYPED AS glob_constr_and_expr
     GLOB_PRINTED BY pr_gen
  [ lconstr(c) ] -> [ c ]
END

type 'id gen_place= ('id * hyp_location_flag,unit) location

type loc_place = Id.t Loc.located gen_place
type place = Id.t gen_place

let pr_gen_place pr_id = function
    ConclLocation () -> Pp.mt ()
  | HypLocation (id,InHyp) -> str "in " ++ pr_id id
  | HypLocation (id,InHypTypeOnly) ->
      str "in (Type of " ++ pr_id id ++ str ")"
  | HypLocation (id,InHypValueOnly) ->
      str "in (Value of " ++ pr_id id ++ str ")"

let pr_loc_place _ _ _ = pr_gen_place (fun (_,id) -> Nameops.pr_id id)
let pr_place _ _ _ = pr_gen_place Nameops.pr_id
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
    RAW_TYPED AS loc_place
    RAW_PRINTED BY pr_loc_place
    GLOB_TYPED AS loc_place
    GLOB_PRINTED BY pr_loc_place
  [ ] ->
    [ ConclLocation () ]
  |  [ "in" "|-" "*" ] ->
    [ ConclLocation () ]
| [ "in" ident(id) ] ->
    [ HypLocation ((Loc.ghost,id),InHyp) ]
| [ "in" "(" "Type" "of" ident(id) ")" ] ->
    [ HypLocation ((Loc.ghost,id),InHypTypeOnly) ]
| [ "in" "(" "Value" "of" ident(id) ")" ] ->
    [ HypLocation ((Loc.ghost,id),InHypValueOnly) ]

 END







(* Julien: Mise en commun des differentes version de replace with in by *)

let pr_by_arg_tac _prc _prlc prtac opt_c =
  match opt_c with
    | None -> mt ()
    | Some t -> hov 2 (str "by" ++ spc () ++ prtac (3,Ppextend.E) t)

ARGUMENT EXTEND by_arg_tac
  TYPED AS tactic_opt
  PRINTED BY pr_by_arg_tac
| [ "by" tactic3(c) ] -> [ Some c ]
| [ ] -> [ None ]
END

let pr_by_arg_tac prtac opt_c = pr_by_arg_tac () () prtac opt_c

(* spiwack: the print functions are incomplete, but I don't know what they are
	used for *)
let pr_r_nat_field natf =
  str "nat " ++
  match natf with
    | Retroknowledge.NatType -> str "type"
    | Retroknowledge.NatPlus -> str "plus"
    | Retroknowledge.NatTimes -> str "times"

let pr_r_n_field  nf =
  str "binary N " ++
  match nf with
    | Retroknowledge.NPositive -> str "positive"
    | Retroknowledge.NType -> str "type"
    | Retroknowledge.NTwice -> str "twice"
    | Retroknowledge.NTwicePlusOne -> str "twice plus one"
    | Retroknowledge.NPhi -> str "phi"
    | Retroknowledge.NPhiInv -> str "phi inv"
    | Retroknowledge.NPlus -> str "plus"
    | Retroknowledge.NTimes -> str "times"

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
    | _ -> assert false

let pr_retroknowledge_field f =
  match f with
 (* | Retroknowledge.KEq -> str "equality"
  | Retroknowledge.KNat natf -> pr_r_nat_field () () () natf
  | Retroknowledge.KN nf -> pr_r_n_field () () () nf *)
  | Retroknowledge.KInt31 (group, i31f) -> (pr_r_int31_field i31f) ++
                                           str "in " ++ str group

VERNAC ARGUMENT EXTEND retroknowledge_nat
PRINTED BY pr_r_nat_field
| [ "nat" "type" ] -> [ Retroknowledge.NatType ]
| [ "nat" "plus" ] -> [ Retroknowledge.NatPlus ]
| [ "nat" "times" ] -> [ Retroknowledge.NatTimes ]
END


VERNAC ARGUMENT EXTEND retroknowledge_binary_n
PRINTED BY pr_r_n_field
| [ "binary" "N" "positive" ] -> [ Retroknowledge.NPositive ]
| [ "binary" "N" "type" ] -> [ Retroknowledge.NType ]
| [ "binary" "N" "twice" ] -> [ Retroknowledge.NTwice ]
| [ "binary" "N" "twice" "plus" "one" ] -> [ Retroknowledge.NTwicePlusOne ]
| [ "binary" "N" "phi" ] -> [ Retroknowledge.NPhi ]
| [ "binary" "N" "phi" "inv" ] -> [ Retroknowledge.NPhiInv ]
| [ "binary" "N" "plus" ] -> [ Retroknowledge.NPlus ]
| [ "binary" "N" "times" ] -> [ Retroknowledge.NTimes ]
END

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
