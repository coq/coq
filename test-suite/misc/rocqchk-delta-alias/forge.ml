(* Replace a declaration in B by an incompatible declaration from another
   compiled copy of the same logical library, while retaining the target's
   resolver that aliases B's declaration to A's. The code is deliberately
   independent of Rocq's OCaml libraries: this is an untrusted file producer,
   not another path through the kernel API. *)

type segment = {
  name : string;
  pos : int64;
  len : int64;
  hash : string;
}

let input_int64 ch =
  let rec go i accu =
    if i = 0 then accu
    else
      go (i - 1)
        (Int64.logor (Int64.shift_left accu 8)
           (Int64.of_int (input_byte ch)))
  in
  go 8 0L

let output_int64 ch n =
  for shift = 7 downto 0 do
    output_byte ch
      (Int64.to_int (Int64.logand 255L (Int64.shift_right_logical n (8 * shift))))
  done

let read_segments ch =
  seek_in ch 8;
  let summary_pos = input_int64 ch in
  LargeFile.seek_in ch summary_pos;
  let n = input_binary_int ch in
  Array.init n (fun _ ->
      let name = really_input_string ch (input_binary_int ch) in
      let pos = input_int64 ch in
      let len = input_int64 ch in
      let hash = really_input_string ch 16 in
      { name; pos; len; hash })

let field v i = Obj.field v i

let structure_of_module mb =
  let signature = field mb 1 in
  if Obj.is_int signature || Obj.tag signature <> 0 || Obj.size signature <> 1
  then failwith "unexpected functorized module";
  field signature 0

let find_field name structure =
  let rec loop cell =
    if Obj.is_int cell then failwith ("missing structure field " ^ name)
    else
      let item = field cell 0 in
      let label = field item 0 in
      if not (Obj.is_int label) && Obj.tag label = Obj.string_tag
         && String.equal (Obj.obj label) name
      then field item 1
      else loop (field cell 1)
  in
  loop structure

let find_declaration expected_tag kind module_body name =
  let body = find_field name (structure_of_module module_body) in
  if Obj.is_int body || Obj.tag body <> expected_tag || Obj.size body <> 1 then
    failwith (name ^ " is not " ^ kind);
  body

let root_module data =
  let disk = Obj.repr (Marshal.from_string data 0) in
  disk, structure_of_module (field (field disk 0) 1)

let module_from root name =
  let body = find_field name root in
  if Obj.is_int body || Obj.tag body <> 3 || Obj.size body <> 1 then
    failwith (name ^ " is not a module");
  field body 0

let poison_library mode data donor_data =
  let disk, root = root_module data in
  let _, donor_root = root_module donor_data in
  let name, tag, kind = match mode with
    | "constant" -> "x", 0, "a constant"
    | "inductive" -> "inhabited", 1, "an inductive"
    | _ -> failwith "expected mutation kind constant or inductive"
  in
  let target = find_declaration tag kind (module_from root "B") name in
  let donor = find_declaration tag kind (module_from donor_root "B") name in
  Obj.set_field target 0 (field donor 0);
  Marshal.to_string (Obj.obj disk) []

let library_data file =
  let input = open_in_bin file in
  let segments = read_segments input in
  let rec find i =
    if i = Array.length segments then failwith "missing library segment"
    else if String.equal segments.(i).name "library" then segments.(i)
    else find (i + 1)
  in
  let segment = find 0 in
  LargeFile.seek_in input segment.pos;
  let data = really_input_string input (Int64.to_int segment.len) in
  close_in input;
  data

let () =
  let file = Sys.argv.(1) in
  let donor_data = library_data Sys.argv.(2) in
  let mode = Sys.argv.(3) in
  let input = open_in_bin file in
  let header = really_input_string input 8 in
  let segments = read_segments input in
  let contents =
    Array.map
      (fun segment ->
        LargeFile.seek_in input segment.pos;
        let data = really_input_string input (Int64.to_int segment.len) in
        let data =
          if String.equal segment.name "library" then
            poison_library mode data donor_data
          else data
        in
        segment.name, data)
      segments
  in
  close_in input;
  let temporary = file ^ ".forged" in
  let output = open_out_bin temporary in
  output_string output header;
  output_int64 output 0L;
  let rewritten =
    Array.map
      (fun (name, data) ->
        let pos = LargeFile.pos_out output in
        output_string output data;
        let hash = Digest.string data in
        output_string output hash;
        { name; pos; len = Int64.of_int (String.length data); hash })
      contents
  in
  let summary_pos = LargeFile.pos_out output in
  output_binary_int output (Array.length rewritten);
  Array.iter
    (fun segment ->
      output_binary_int output (String.length segment.name);
      output_string output segment.name;
      output_int64 output segment.pos;
      output_int64 output segment.len;
      output_string output segment.hash)
    rewritten;
  LargeFile.seek_out output 8L;
  output_int64 output summary_pos;
  close_out output;
  Sys.rename temporary file
