(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Pp
open Pcoq
open Genarg
open Names
open Tacexpr
open Tacinterp
open Termops

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

let pr_int_list_full _prc _prlc _prt l =
  let rec aux = function
    | i :: l -> Pp.int i ++ Pp.spc () ++ aux l
    | [] -> Pp.mt()
  in aux l

ARGUMENT EXTEND int_nelist
  TYPED AS int list
  PRINTED BY pr_int_list_full
  RAW_TYPED AS int list
  RAW_PRINTED BY pr_int_list_full
  GLOB_TYPED AS int list
  GLOB_PRINTED BY pr_int_list_full
| [ integer(x) int_nelist(l) ] -> [x::l]
| [ integer(x) ] -> [ [x] ]
END

let pr_int_list = pr_int_list_full () () ()

open Rawterm

let pr_occurrences _prc _prlc _prt l =
  match l with
    | ArgArg x -> pr_int_list x
    | ArgVar (loc, id) -> Nameops.pr_id id

let coerce_to_int = function
  | VInteger n -> n
  | v -> raise (CannotCoerceTo "an integer")

let int_list_of_VList = function
  | VList l -> List.map (fun n -> coerce_to_int n) l
  | _ -> raise Not_found

let interp_occs ist gl l =
  match l with
    | ArgArg x -> x
    | ArgVar (_,id as locid) ->
	(try int_list_of_VList (List.assoc id ist.lfun)
	  with Not_found | CannotCoerceTo _ -> [interp_int ist locid])

let glob_occs ist l = l

let subst_occs evm l = l

type occurrences_or_var = int list or_var
type occurrences = int list

ARGUMENT EXTEND occurrences
  TYPED AS occurrences
  PRINTED BY pr_int_list_full

  INTERPRETED BY interp_occs
  GLOBALIZED BY glob_occs
  SUBSTITUTED BY subst_occs

  RAW_TYPED AS occurrences_or_var
  RAW_PRINTED BY pr_occurrences

  GLOB_TYPED AS occurrences_or_var
  GLOB_PRINTED BY pr_occurrences

| [ int_nelist(l) ] -> [ ArgArg l ]
| [ var(id) ] -> [ ArgVar id ]
END

let pr_occurrences = pr_occurrences () () ()

let pr_gen prc _prlc _prtac c = prc c

let pr_rawc _prc _prlc _prtac (_,raw) = Printer.pr_rawconstr raw
let pr_raw = pr_rawc () () ()

let interp_raw ist gl (t,_) = (ist,t)

let glob_raw = Tacinterp.intern_constr

let subst_raw = Tacinterp.subst_rawconstr_and_expr

ARGUMENT EXTEND raw
    TYPED AS rawconstr
    PRINTED BY pr_rawc

     INTERPRETED BY interp_raw
     GLOBALIZED BY glob_raw
     SUBSTITUTED BY subst_raw

     RAW_TYPED AS constr_expr
     RAW_PRINTED BY pr_gen

     GLOB_TYPED AS rawconstr_and_expr
     GLOB_PRINTED BY pr_gen
  [ lconstr(c) ] -> [ c ]
END


type 'id gen_place= ('id * hyp_location_flag,unit) location

type loc_place = identifier Util.located gen_place
type place = identifier gen_place

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
  | HypLocation (id,hl) -> HypLocation (intern_hyp ist id,hl)

let interp_place ist gl = function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id,hl) -> HypLocation (interp_hyp ist gl id,hl)

let subst_place subst pl = pl

ARGUMENT EXTEND hloc
    TYPED AS place
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
    [ HypLocation ((Util.dummy_loc,id),InHyp) ]
| [ "in" "(" "Type" "of" ident(id) ")" ] ->
    [ HypLocation ((Util.dummy_loc,id),InHypTypeOnly) ]
| [ "in" "(" "Value" "of" ident(id) ")" ] ->
    [ HypLocation ((Util.dummy_loc,id),InHypValueOnly) ]

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

let pr_in_hyp  pr_id (lo,concl) :  Pp.std_ppcmds =
  match lo,concl with
    | Some [],true -> mt ()
    | None,true -> str "in" ++ spc () ++ str "*"
    | None,false -> str "in" ++ spc () ++ str "*" ++ spc () ++ str "|-"
    | Some l,_ ->
	str "in" ++
	  Util.prlist (fun id -> spc () ++ pr_id id) l ++
	  match concl with
	    | true -> spc () ++ str "|-" ++ spc () ++ str "*"
	    | _ -> mt ()


let pr_in_arg_hyp _ _ _ = pr_in_hyp (fun (_,id) -> Ppconstr.pr_id id)

let pr_in_arg_hyp_typed  _ _  _  = pr_in_hyp Ppconstr.pr_id


let pr_var_list_gen pr_id = Util.prlist_with_sep (fun () -> str ",") pr_id

let pr_var_list_typed _ _ _ =  pr_var_list_gen Ppconstr.pr_id

let pr_var_list _ _ _ = pr_var_list_gen (fun (_,id) -> Ppconstr.pr_id id)


ARGUMENT EXTEND comma_var_lne
  TYPED AS var list
  PRINTED BY pr_var_list_typed
  RAW_TYPED AS var list
  RAW_PRINTED BY pr_var_list
  GLOB_TYPED AS var list
  GLOB_PRINTED BY pr_var_list
| [ var(x) ] -> [ [x] ]
| [ var(x) "," comma_var_lne(l) ] -> [x::l]
END

ARGUMENT EXTEND comma_var_l
  TYPED AS var list
  PRINTED BY pr_var_list_typed
  RAW_TYPED AS var list
  RAW_PRINTED BY pr_var_list
  GLOB_TYPED AS var list
  GLOB_PRINTED BY pr_var_list
| [  comma_var_lne(l) ] -> [l]
| [] -> [ [] ]
END

let pr_in_concl _ _ _ = function true -> str "|- " ++ spc () ++ str "*" | _ -> str "|-"

ARGUMENT EXTEND inconcl
  TYPED AS bool
  PRINTED BY pr_in_concl
| [ "|-" "*" ] -> [ true ]
| [ "|-" ] -> [ false ]
END



ARGUMENT EXTEND in_arg_hyp
  TYPED AS var list option * bool
  PRINTED BY pr_in_arg_hyp_typed
  RAW_TYPED AS var list option * bool
  RAW_PRINTED BY pr_in_arg_hyp
  GLOB_TYPED AS var list option * bool
  GLOB_PRINTED BY pr_in_arg_hyp
| [ "in" "*" ] -> [(None,true)]
| [ "in" "*" inconcl_opt(b) ] -> [let onconcl = match b with Some b -> b | None -> true in (None,onconcl)]
| [ "in" comma_var_l(l) inconcl_opt(b) ] -> [ let onconcl = match b with Some b -> b | None -> false in
					      Some l, onconcl
					   ]
| [ ] -> [ (Some [],true) ]
END

let pr_in_arg_hyp = pr_in_arg_hyp_typed () () ()

let gen_in_arg_hyp_to_clause trad_id (hyps ,concl) : Tacticals.clause =
  {Tacexpr.onhyps=
   Option.map
     (fun l ->
	List.map
	  (fun id -> ( (all_occurrences_expr,trad_id id),InHyp))
	  l
     )
     hyps;
   Tacexpr.concl_occs = if concl then all_occurrences_expr else no_occurrences_expr}


let raw_in_arg_hyp_to_clause = gen_in_arg_hyp_to_clause snd
let glob_in_arg_hyp_to_clause = gen_in_arg_hyp_to_clause (fun x -> x)

