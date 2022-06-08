let theorem_loc : Loc.t option ref = ref None
let proof_loc: Loc.t option ref = ref None
let section_vars_loc : Loc.t option ref = ref None

let fname : string option ref = ref None
let offset = ref 0
let fin : in_channel ref = ref stdin
let fout : out_channel ref = ref stdout

let tmp_file fn = fn ^ "_update"

let start_file f =
  try
    offset := 0;
    fin := open_in_bin f;
        fout := open_out_bin (tmp_file f);
        fname := Some f
  with e -> () (* todo: print message *)

let save_theorem loc =
  theorem_loc := Some loc;
  proof_loc := None;
  section_vars_loc := None

let save_proof loc =
  proof_loc := Some loc

let save_section_vars_list loc =
  section_vars_loc := Some loc

let bufsize = 1024
let buf = Bytes.create bufsize

let of_some = function
  | Some x -> x
  | None -> failwith "of_some"

(* copy range from bp to ep+1 inclusive *)
let copy bp ep =
  assert (bp <= ep);
  seek_in !fin bp;
  let rec aux len =
    if len <= 0 then ()
    else begin
      let actlen = input !fin buf 0 (min len bufsize) in
      output !fout buf 0 actlen;
      aux (len - actlen)
    end
  in
  let len = 1 + ep - bp in
  aux len;
  offset := !offset + len

let save_needed syms =
  let open Loc in
  if !fname <> None && !theorem_loc <> None then begin
    let insert = String.concat " " syms in
    let insert = if insert = "" then "" else " " ^ insert in
    copy !offset (of_some (!theorem_loc)).ep;
    match !proof_loc with
    | None -> output_string !fout (Printf.sprintf "\nProof using%s." insert)
    | Some ploc ->
      let using = match !section_vars_loc with
        | None -> copy !offset (ploc.ep - 1); " using"  (* add "using ...", keep "." *)
        | Some svs -> copy !offset (svs.bp-2); offset := svs.ep; "" (* replace items in "using ..." *)
      in
      output_string !fout (Printf.sprintf "%s%s" using insert)
  end;
  theorem_loc := None;
  proof_loc := None;
  section_vars_loc := None

let end_file () =
  match !fname with
  | Some _ ->
    let fn = of_some !fname in
    let flen = (Unix.stat fn).st_size in
    copy !offset (flen-1);
    fname := None;
    close_in !fin;
    close_out !fout;
    Unix.rename (tmp_file fn) fn
  | None -> ()
