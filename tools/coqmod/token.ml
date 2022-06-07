(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Loc = struct
  type t = {start : Lexing.position; finish : Lexing.position}

  let to_string ?(sep = ", ") ?(range_sep = "-") ?(line = "Ln ")
      ?(lines = "Ln ") ?(char = "Col ") ?(chars = "Col ") t =
    (* Configurable printing of locations *)
    let line1 = t.start.Lexing.pos_lnum in
    let line2 = t.finish.Lexing.pos_lnum in
    let col1 = t.start.Lexing.pos_cnum - t.start.Lexing.pos_bol + 1 in
    let col2 = t.finish.Lexing.pos_cnum - t.finish.Lexing.pos_bol + 1 in
    let line_range =
      if Int.equal line1 line2 then line ^ string_of_int line1
      else lines ^ string_of_int line1 ^ range_sep ^ string_of_int line2
    in
    let col_range =
      if Int.equal col1 col2 then char ^ string_of_int col1
      else chars ^ string_of_int col1 ^ range_sep ^ string_of_int col2
    in
    line_range ^ sep ^ col_range

  let dummy = {start = Lexing.dummy_pos; finish = Lexing.dummy_pos}

  let of_lexbuf lexbuf =
    Lexing.{start = lexeme_start_p lexbuf; finish = lexeme_end_p lexbuf}

  let pos_to_sexp pos =
    let open Csexp in
    List
      [
        Atom (string_of_int pos.Lexing.pos_lnum);
        Atom (string_of_int (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1));
      ]

  let to_sexp t =
    let open Csexp in
    List [Atom "Loc"; pos_to_sexp t.start; pos_to_sexp t.finish]
end

module Module = struct
  type t = {loc : Loc.t; logical_name : string}

  let make loc logical_name = {loc; logical_name}

  let to_string t = Loc.to_string t.loc ^ " Require " ^ t.logical_name

  let to_string_as_prefix t = Loc.to_string t.loc ^ " From " ^ t.logical_name

  let to_string_as_declare t =
    Loc.to_string t.loc ^ " Declare ML Module " ^ to_string t

  let to_sexp t =
    let open Csexp in
    List [Loc.to_sexp t.loc; Atom t.logical_name]

  let compare x y = String.compare x.logical_name y.logical_name
end

module From = struct
  type t = {prefix : Module.t option; require : Module.t}

  let to_string t =
    match t.prefix with
    | None -> Module.to_string t.require
    | Some prefix ->
        Module.to_string_as_prefix prefix ^ " " ^ Module.to_string t.require

  let to_sexp t =
    let open Csexp in
    match t.prefix with
    | None -> List [Module.to_sexp t.require]
    | Some prefix -> List [Module.to_sexp prefix; Module.to_sexp t.require]

  let compare x y =
    (* When comparing we ignore the locations *)
    if
      Option.equal
        Module.(fun x y -> x.logical_name = y.logical_name)
        x.prefix y.prefix
    then Module.compare x.require y.require
    else Option.compare Module.compare x.prefix y.prefix
end

module Load = struct
  type t = {loc : Loc.t; path : string}

  let to_string t =
    Loc.to_string t.loc ^ " " ^ "Physical " ^ "\"" ^ t.path ^ "\""

  let to_sexp t =
    let open Csexp in
    List [Loc.to_sexp t.loc; Atom t.path]

  let compare x y = String.compare x.path y.path
end

module ExtraDep = struct
  type t = {loc : Loc.t; from : Module.t; file : string}

  let to_string t =
    Loc.to_string t.loc ^ " From " ^ Module.to_string t.from
    ^ " Extra Dependency " ^ "\"" ^ t.file ^ "\""

  let to_sexp t =
    let open Csexp in
    List [Module.to_sexp t.from; Loc.to_sexp t.loc; Atom t.file]

  (* TODO *)
  let compare x y =
    let open Module in
    if x.from.logical_name = y.from.logical_name then
      String.compare x.file y.file
    else Module.compare x.from y.from
end

type t = {
  filename : string option;
  froms : From.t list;
  declares : Module.t list;
  loads : Load.t list;
  extradeps : ExtraDep.t list;
}

let get_filename t = Option.get t.filename

let empty =
  {filename = None; froms = []; declares = []; loads = []; extradeps = []}

let set_filename t filename = {t with filename = Some filename}

let add_from t prefix require =
  {t with froms = From.{prefix; require} :: t.froms}

let add_from_list t prefix requires =
  let froms = List.map (fun require -> From.{prefix; require}) requires in
  {t with froms = froms @ t.froms}

let add_require t require = add_from t None require

let add_require_list t requires = add_from_list t None requires

let add_declare_list t declares = {t with declares = declares @ t.declares}

let add_load t loc path = {t with loads = Load.{loc; path} :: t.loads}

let add_extrdep t loc from file =
  {t with extradeps = ExtraDep.{loc; from; file} :: t.extradeps}

let to_string t =
  let default_filename = "<!!Unknown File!!>" in
  [
    ["Begin " ^ Option.default default_filename t.filename];
    List.map From.to_string t.froms;
    List.map Module.to_string_as_declare t.declares;
    List.map Load.to_string t.loads;
    List.map ExtraDep.to_string t.extradeps;
    ["End " ^ Option.default default_filename t.filename];
  ]
  |> List.flatten |> String.concat "\n"

let sexp_of_declares = function
  | [] -> []
  | declares ->
      Csexp.[List (Atom "Declare" :: List.map Module.to_sexp declares)]

let sexp_of_froms = function
  | [] -> []
  | froms -> Csexp.[List (Atom "Require" :: List.map From.to_sexp froms)]

let sexp_of_loads = function
  | [] -> []
  | loads -> Csexp.[List (Atom "Load" :: List.map Load.to_sexp loads)]

let sexp_extradeps = function
  | [] -> []
  | extradeps ->
      Csexp.[List (Atom "ExtraDep" :: List.map ExtraDep.to_sexp extradeps)]

let to_sexp t =
  [
    sexp_of_froms t.froms;
    sexp_of_declares t.declares;
    sexp_of_loads t.loads;
    sexp_extradeps t.extradeps;
  ]
  |> List.flatten
  |> fun x ->
  let open Csexp in
  List
    ( Atom "Document"
    :: List [Atom "Name"; Atom (Option.default "Unknown" t.filename)]
    :: x )

let sort_uniq t =
  {
    t with
    froms = List.sort_uniq From.compare t.froms;
    declares = List.sort_uniq Module.compare t.declares;
    loads = List.sort_uniq Load.compare t.loads;
    extradeps = List.sort_uniq ExtraDep.compare t.extradeps;
  }

module Sexp = struct
  open Csexp

  let rec pp fmt =
    let pp_list = Format.pp_print_list pp ~pp_sep:Format.pp_print_space in
    function
    | Atom s -> Format.pp_print_string fmt s
    (* Only vertically formatted s-expressions need to be included *)
    | List (Atom "Load" :: ts) ->
        Format.fprintf fmt "@[<v1>(Load@ %a@])" pp_list ts
    | List (Atom "Declare" :: ts) ->
        Format.fprintf fmt "@[<v1>(Declare@ %a@])" pp_list ts
    | List (Atom "Require" :: ts) ->
        Format.fprintf fmt "@[<v1>(Require@ %a@])" pp_list ts
    | List (Atom "Document" :: ts) ->
        Format.fprintf fmt "@[<v1>(Document@ %a@])" pp_list ts
    | List (Atom "ExtraDep" :: ts) ->
        Format.fprintf fmt "@[<v1>(ExtraDep@ %a@])" pp_list ts
    | List ts ->
        Format.fprintf fmt "@[<h1>(%a)@]"
          (Format.pp_print_list pp ~pp_sep:Format.pp_print_space)
          ts
end
