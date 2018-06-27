(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Format
open Cic
open Names

let chk_pp fmt = Pp.pp_with fmt
let pp_arrayi pp fmt a = Array.iteri (fun i x -> pp fmt (i,x)) a
let pp_instance fmt i = chk_pp fmt (Univ.Instance.pr i)
let pp_id fmt id = fprintf fmt "%s" (Id.to_string id)

let print_pure_constr fmt csr =
  let rec pp_term fmt c = match  c with
  | Rel n  -> fprintf fmt "#%d" n
  | Meta n -> fprintf fmt "Meta(%d)" n
  | Var id -> pp_id fmt id
  | Sort s -> pp_sort fmt s
  | Cast (c,_, t) ->
    fprintf fmt "@[<hov 1>(%a@;::%a)@]" pp_term c pp_term t
  | Prod (Name(id),t,c) ->
    fprintf fmt "@[<hov 1>(%a:%a)@;@[%a@]@]" pp_id id pp_term t pp_term c
  | Prod (Anonymous,t,c) ->
    fprintf fmt "(%a@,->@[%a@])" pp_term t pp_term c
  | Lambda (na,t,c) ->
    fprintf fmt "[%a:@[%a@]]@,@[%a@]" pp_name na pp_term t pp_term c
  | LetIn (na,b,t,c) ->
    fprintf fmt "[%a=@[%a@]@,:@[%a@]]@,@[%a@]" pp_name na pp_term b pp_term t pp_term c
  | App (c,l) ->
    fprintf fmt "(@[%a@]@, @[<hov 1>%a@])" pp_term c (pp_arrayi (fun _ (_,s) -> fprintf fmt "@[%a@]@," pp_term s)) l;
  | Evar _ -> pp_print_string fmt "Evar#"
  | Const (c,u) ->
    fprintf fmt "Cons(@[%a,%a@])" sp_con_display c pp_instance u
  | Ind ((sp,i),u) ->
    fprintf fmt "Ind(@[%a,%d,%a@])" sp_display sp i pp_instance u
  | Construct (((sp,i),j),u) ->
    fprintf fmt "Constr(%a,%d,%d,%a)" sp_display sp i j pp_instance u
  | Case (ci,p,c,bl) ->
    let pp_match fmt (_,mc) = fprintf fmt " @[%a@]" pp_term mc in
    fprintf fmt "@[<v><@[%a@]>@,Case@ @[%a@]@ of@[<v>%a@]@,end@]" pp_term p pp_term c (pp_arrayi pp_match) bl
  | Fix ((t,i),(lna,tl,bl)) ->
    let pp_fixc fmt (k,_) =
      fprintf fmt "@[<v 0> %a/%d@,:@[%a@]@,:=@[%a@]@]@," pp_name lna.(k) t.(k) pp_term tl.(k) pp_term bl.(k) in
    fprintf fmt "Fix(%d)@,@[<v>{%a}@]" i (pp_arrayi pp_fixc) tl
  | CoFix(i,(lna,tl,bl)) ->
    let pp_fixc fmt (k,_) =
      fprintf fmt "@[<v 0> %a@,:@[%a@]@,:=@[%a@]@]@," pp_name lna.(k) pp_term tl.(k) pp_term bl.(k) in
    fprintf fmt "CoFix(%d)@,@[<v>{%a}@]" i (pp_arrayi pp_fixc) tl
  | Proj (p, c) ->
    fprintf fmt "Proj(%a,@,@[%a@])" sp_con_display (Projection.constant p) pp_term c

  and pp_sort fmt = function
    | Set -> pp_print_string fmt  "Set"
    | Prop -> pp_print_string fmt "Prop"
    | Type u -> fprintf fmt "Type(%a)" chk_pp (Univ.pr_uni u)

  and pp_name fmt = function
    | Name id -> pp_id fmt id
    | Anonymous -> pp_print_string fmt "_"

(* Remove the top names for library and Scratch to avoid long names *)
  and sp_display fmt sp =
(*  let dir,l = decode_kn sp in
    let ls =
      match List.rev_map Id.to_string (DirPath.repr dir) with
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
    pp_print_string fmt (MutInd.debug_to_string sp)

  and sp_con_display fmt sp =
    (*
    let dir,l = decode_kn sp in
    let ls =
      match List.rev_map Id.to_string (DirPath.repr dir) with
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
    pp_print_string fmt (Constant.debug_to_string sp)

  in
  try
    fprintf fmt "@[%a@]%!" pp_term csr
  with e ->
    pp_print_string fmt (Printexc.to_string e);
    print_flush ();
    raise e
