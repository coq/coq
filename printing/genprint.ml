(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Genarg

type 'a printer_without_level = 'a -> std_ppcmds
type 'a printer_with_level = Ppextend.tolerability -> 'a -> std_ppcmds
type 'a printer = Ppextend.tolerability option -> 'a -> std_ppcmds

type ('raw, 'glb, 'top) genprinter = {
  raw : 'raw printer;
  glb : 'glb printer;
  top : 'top printer;
}

module PrintObj =
struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) genprinter
  let name = "printer"
  let default wit = match wit with
  | ExtraArg tag ->
    let name = ArgT.repr tag in
    let printer = {
      raw = (fun _ _ -> str "<genarg:" ++ str name ++ str ">");
      glb = (fun _ _ -> str "<genarg:" ++ str name ++ str ">");
      top = (fun _ _ -> str "<genarg:" ++ str name ++ str ">");
    } in
    Some printer
  | _ -> assert false
end

module Print = Register (PrintObj)

let register_print0 wit raw glb top =
  let raw = function None -> raw | _ -> raw in
  let glb = function None -> glb | _ -> glb in
  let top = function None -> top | _ -> top in
  let printer = { raw; glb; top; } in
  Print.register0 wit printer

let register_print_with_level0 wit raw glb top =
  let raw = function Some l -> raw l | _ -> CErrors.anomaly (Pp.str "Level expected") in
  let glb = function Some l -> glb l | _ -> CErrors.anomaly (Pp.str "Level expected") in
  let top = function Some l -> top l | _ -> CErrors.anomaly (Pp.str "Level expected") in
  let printer = { raw; glb; top; } in
  Print.register0 wit printer

let raw_print wit v = (Print.obj wit).raw v
let glb_print wit v = (Print.obj wit).glb v
let top_print wit v = (Print.obj wit).top v

let generic_raw_print x (GenArg (Rawwit w, v)) = raw_print w x v
let generic_glb_print x (GenArg (Glbwit w, v)) = glb_print w x v
let generic_top_print x (GenArg (Topwit w, v)) = top_print w x v

let hov_if_not_empty n p = if Pp.ismt p then p else hov n p

let rec pr_raw_generic env lev (GenArg (Rawwit wit, x)) =
  match wit with
    | ListArg wit ->
      let map x = pr_raw_generic env lev (in_gen (rawwit wit) x) in
      let ans = pr_sequence map x in
      hov_if_not_empty 0 ans
    | OptArg wit ->
      let ans = match x with
        | None -> mt ()
        | Some x -> pr_raw_generic env lev (in_gen (rawwit wit) x)
      in
      hov_if_not_empty 0 ans
    | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = in_gen (rawwit wit1) p in
      let q = in_gen (rawwit wit2) q in
      hov_if_not_empty 0 (pr_sequence (pr_raw_generic env lev) [p; q])
    | ExtraArg s ->
      generic_raw_print lev (in_gen (rawwit wit) x)

let rec pr_glb_generic env lev (GenArg (Glbwit wit, x)) =
  match wit with
    | ListArg wit ->
      let map x = pr_glb_generic env lev (in_gen (glbwit wit) x) in
      let ans = pr_sequence map x in
      hov_if_not_empty 0 ans
    | OptArg wit ->
      let ans = match x with
        | None -> mt ()
        | Some x -> pr_glb_generic env lev (in_gen (glbwit wit) x)
      in
      hov_if_not_empty 0 ans
    | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = in_gen (glbwit wit1) p in
      let q = in_gen (glbwit wit2) q in
      let ans = pr_sequence (pr_glb_generic env lev) [p; q] in
      hov_if_not_empty 0 ans
    | ExtraArg s ->
      generic_glb_print lev (in_gen (glbwit wit) x)

let is_genarg tag wit =
  let ArgT.Any tag = tag in
  argument_type_eq (ArgumentType (ExtraArg tag)) wit
                   
let get_list : type l. l generic_argument -> l generic_argument list option =
  function (GenArg (wit, arg)) -> match wit with
  | Rawwit (ListArg wit) -> Some (List.map (in_gen (rawwit wit)) arg)
  | Glbwit (ListArg wit) -> Some (List.map (in_gen (glbwit wit)) arg)
  | _ -> None

let get_opt : type l. l generic_argument -> l generic_argument option option =
  function (GenArg (wit, arg)) -> match wit with
  | Rawwit (OptArg wit) -> Some (Option.map (in_gen (rawwit wit)) arg)
  | Glbwit (OptArg wit) -> Some (Option.map (in_gen (glbwit wit)) arg)
  | _ -> None

let rec pr_any_arg : type l. (_ -> l generic_argument -> std_ppcmds) -> _ -> l generic_argument -> std_ppcmds =
  fun pr_gen symb arg -> match symb with
  | Extend.Uentry tag when is_genarg tag (genarg_tag arg) -> pr_gen (Some (5,Ppextend.E) (* FIXME: ok for tactic but meaningless otherwise *)) arg
  | Extend.Uentryl (tag,n) when is_genarg tag (genarg_tag arg) -> pr_gen (Some (n,Ppextend.E)) arg
  | Extend.Ulist1 s | Extend.Ulist0 s ->
    begin match get_list arg with
    | None -> assert false
    | Some l -> pr_sequence (pr_any_arg pr_gen s) l
    end
  | Extend.Ulist1sep (s, sep) | Extend.Ulist0sep (s, sep) ->
    begin match get_list arg with
    | None -> assert false
    | Some l -> prlist_with_sep (fun () -> spc () ++ str sep ++ spc ()) (pr_any_arg pr_gen s) l
    end
  | Extend.Uopt s ->
    begin match get_opt arg with
    | None -> assert false
    | Some l -> pr_opt (pr_any_arg pr_gen s) l
    end
  | Extend.Uentry _ | Extend.Uentryl _ -> assert false

type 'a arguments_production =
| ArgTerm of string
| ArgNonTerm of Genarg.ArgT.any Extend.user_symbol * 'a

module Make
  (Taggers  : sig
    val tag_keyword : std_ppcmds -> std_ppcmds
    val tag_primitive  : std_ppcmds -> std_ppcmds
  end)
= struct

  open Taggers

  let keyword x = tag_keyword (str x)
  let primitive x = tag_primitive (str x)

  let rec pr_extension_using_rule_tail pr_gen = function
  | [] -> []
  | ArgTerm s :: l -> keyword s :: pr_extension_using_rule_tail pr_gen l
  | ArgNonTerm (symb, arg) :: l  ->
     pr_gen symb arg :: pr_extension_using_rule_tail pr_gen l
                                                
  let pr_extension_using_rule pr_gen l =
  let l = match l with
    | ArgTerm s :: l ->
       (** First terminal token should be considered as the name of the tactic,
          so we tag it differently than the other terminal tokens. *)
       primitive s :: pr_extension_using_rule_tail pr_gen l
    | _ -> pr_extension_using_rule_tail pr_gen l
  in
  pr_sequence (fun x -> x) l

end
