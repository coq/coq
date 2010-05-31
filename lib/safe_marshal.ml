(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*
let uuencode s =
  let norm_s = s ^ (String.make (String.length s mod 3) '\000') in
  let rec y f x = f (y f) x in
  let chop rem = function
    | "" -> []
    | s -> String.sub s 0 3 :: (rem (String.sub s 3 (String.length (s - 3)))) in
  let chunks = y chop norm_s in
 *)

let hobcnv = Array.init 256 (fun i -> Printf.sprintf "%.2x" i)
let bohcnv = Array.init 256 (fun i -> i -
                                      (if 0x30 <= i then 0x30 else 0) -
                                      (if 0x41 <= i then 0x7 else 0) -
                                      (if 0x61 <= i then 0x20 else 0))

let hex_of_bin ch = hobcnv.(int_of_char ch)
let bin_of_hex s = char_of_int (bohcnv.(int_of_char s.[0]) * 16 + bohcnv.(int_of_char s.[1]))

let send cout expr =
  let mshl_expr = Marshal.to_string expr [] in
  let payload = Buffer.create (String.length mshl_expr * 2) in
  String.iter (fun c -> Buffer.add_string payload (hex_of_bin c)) mshl_expr;
  Buffer.add_char payload '\n';
  output_string cout (Buffer.contents payload);
  flush cout


let receive cin =
  let payload = input_line cin in
  let mshl_expr_len = String.length payload / 2 in
  let mshl_expr = Buffer.create mshl_expr_len in
  let buf = String.create 2 in
  for i = 0 to mshl_expr_len - 1 do
    String.blit payload (2*i) buf 0 2;
    Buffer.add_char mshl_expr (bin_of_hex buf)
  done;
  Marshal.from_string (Buffer.contents mshl_expr) 0

