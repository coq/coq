(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

type t = A of string | Path of Path.t

let adjust ~lvl = function
  | A arg -> A arg
  | Path p -> Path (Path.adjust ~lvl p)

let to_string = function A arg -> arg | Path p -> Path.to_string p

module List = struct
  let to_string args = List.map to_string args |> String.concat " "
end
