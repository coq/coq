(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Makefile's escaping rules are awful: $ is escaped by doubling and
   other special characters are escaped by backslash prefixing while
   backslashes themselves must be escaped only if part of a sequence
   followed by a special character (i.e. in case of ambiguity with a
   use of it as escaping character).  Moreover (even if not crucial)
   it is apparently not possible to directly escape ';' and leading '\t'. *)

let escape =
  let s' = Buffer.create 10 in
  fun s ->
    Buffer.clear s';
    for i = 0 to String.length s - 1 do
      let c = s.[i] in
      if c = ' ' || c = '#' || c = ':' (* separators and comments *)
        || c = '%' (* pattern *)
        || c = '?' || c = '[' || c = ']' || c = '*' (* expansion in filenames *)
        || i=0 && c = '~' && (String.length s = 1 || s.[1] = '/' ||
            'A' <= s.[1] && s.[1] <= 'Z' ||
            'a' <= s.[1] && s.[1] <= 'z') (* homedir expansion *)
      then begin
        let j = ref (i-1) in
        while !j >= 0 && s.[!j] = '\\' do
          Buffer.add_char s' '\\'; decr j (* escape all preceding '\' *)
        done;
        Buffer.add_char s' '\\';
      end;
      if c = '$' then Buffer.add_char s' '$';
      Buffer.add_char s' c
    done;
    Buffer.contents s'

open Format

type dynlink = Opt | Byte | Both | No | Variable
let option_dynlink = ref Both

let set_dyndep = function
  | "no" -> option_dynlink := No
  | "opt" -> option_dynlink := Opt
  | "byte" -> option_dynlink := Byte
  | "both" -> option_dynlink := Both
  | "var" -> option_dynlink := Variable
  | o -> CErrors.user_err Pp.(str "Incorrect -dyndep option: " ++ str o)

let mldep_to_make base =
  match !option_dynlink with
  | No -> []
  | Byte -> [sprintf "%s.cma" base]
  | Opt -> [sprintf "%s.cmxs" base]
  | Both ->
    [sprintf "%s.cma" base; sprintf "%s.cmxs" base]
  | Variable ->
    [sprintf "%s%s" base "$(DYNLIB)"]

let string_of_dep ~suffix = let open Dep_info.Dep in
  function
  | Require basename -> [escape basename ^ suffix]
  | Ml base -> mldep_to_make (escape base)
  | Other s -> [escape s]

let string_of_dependency_list ~suffix deps =
  List.map (string_of_dep ~suffix) deps
  |> List.concat |> String.concat " "

let option_noglob = ref false
let option_write_vos = ref false
let set_noglob glob = option_noglob := glob
let set_write_vos vos = option_write_vos := vos

let print_dep fmt { Dep_info.name; deps } =
  let ename = escape name in
    let glob = if !option_noglob then "" else ename^".glob " in
  fprintf fmt "%s.vo %s%s.v.beautified %s.required_vo: %s.v %s\n" ename glob ename ename ename
    (string_of_dependency_list ~suffix:".vo" deps);
  if !option_write_vos then
    fprintf fmt "%s.vos %s.vok %s.required_vos: %s.v %s\n" ename ename ename ename
      (string_of_dependency_list ~suffix:".vos" deps);
  fprintf fmt "%!"
