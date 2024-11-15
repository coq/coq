type sized_string = { str : string; size : int }

let size s = s.size

type header = sized_string

type row = sized_string list list

module Align = struct
  type t =
    | Left
    | MidLeft
    | Middle
    | MidRight
    | Right
end

let rec map3 f l1 l2 l3 =
  match (l1, l2, l3) with
  | ([], [], []) -> []
  | (a1::l1, a2::l2, a3::l3) -> let r = f a1 a2 a3 in r :: map3 f l1 l2 l3
  | (_, _, _) -> invalid_arg "Table.map3"

let val_padding = 2
(* Padding between data in the same row *)
let row_padding = 1
(* Padding between rows *)

let homogeneous b = if b then () else failwith "Heterogeneous data"

let vert_split (ls : 'a list list) =
  let split l = match l with
  | [] -> failwith "vert_split"
  | x :: l -> (x, l)
  in
  let ls = CList.map split ls in
  CList.split ls

let justify align n s =
  let len = s.size in
  let s = s.str in
  let () = assert (len <= n) in
  let pad = n - len in
  match align with
  | Align.Left -> s ^ String.make pad ' '
  | Align.Right -> String.make pad ' ' ^ s
  | Align.Middle ->
    let pad = pad / 2 in
    String.make pad ' ' ^ s ^ String.make (n - pad - len) ' '
  | Align.MidLeft ->
    let pad = pad / 5 in
    String.make pad ' ' ^ s ^ String.make (n - pad - len) ' '
  | Align.MidRight ->
      let pad = pad / 5 in
      String.make (n - pad - len) ' ' ^ s ^ String.make pad ' '

let justify_row align_row layout data =
  let data = map3 justify align_row layout data in
  { str = String.concat (String.make val_padding ' ') data;
    size = List.fold_left (+) (val_padding * (List.length data - 1)) layout; }

let angle hkind vkind = match hkind, vkind with
| `Lft, `Top -> "┌"
| `Rgt, `Top -> "┐"
| `Mid, `Top -> "┬"
| `Lft, `Mid -> "├"
| `Rgt, `Mid -> "┤"
| `Mid, `Mid -> "┼"
| `Lft, `Bot -> "└"
| `Rgt, `Bot -> "┘"
| `Mid, `Bot -> "┴"

let print_separator vkind col_size =
  let rec dashes n = if n = 0 then "" else "─" ^ dashes (n - 1) in
  let len = CList.length col_size in
  let pad = dashes row_padding in
  let () = assert (0 < len) in
  let map n = dashes n in
  angle `Lft vkind ^ pad ^
  String.concat (pad ^ angle `Mid vkind ^ pad) (CList.map map col_size) ^
  pad ^ angle `Rgt vkind

let print_blank col_size =
  let len = CList.length col_size in
  let () = assert (0 < len) in
  let pad = String.make row_padding ' ' in
  let map n = String.make n ' ' in
  "│" ^ pad ^ String.concat (pad ^ "│" ^ pad) (CList.map map col_size) ^ pad ^ "│"

let print_row row =
  let len = CList.length row in
  let () = assert (0 < len) in
  let pad = String.make row_padding ' ' in
  "│" ^ pad ^ String.concat (pad ^ "│" ^ pad) row ^ pad ^ "│"

let default_align_headers = CList.map (fun _ -> Align.Middle)
let default_align_top = CList.map @@ CList.map (fun _ -> Align.Middle)
let default_align_rows rows =
  CList.hd rows
  |> CList.map @@ CList.map (fun _ -> Align.Right)

(* Invariant : all rows must have the same shape *)

let print (headers : header list) (top : row) (rows : row list)
  ?(align_headers = default_align_headers headers)
  ?(align_top = default_align_top top)
  ?(align_rows = default_align_rows rows)
  () =
  (* Sanitize input *)
  let ncolums = CList.length headers in
  let shape = ref None in
  let check row =
    let () = homogeneous (CList.length row = ncolums) in
    let rshape : int list = CList.map (fun data -> CList.length data) row in
    match !shape with
    | None -> shape := Some rshape
    | Some s -> homogeneous (rshape = s)
  in
  let () = CList.iter check rows in
  (* TODO: check is broken please fix *)
  (* let () = CList.iter check (CList.map (CList.map (fun _ -> [])) align_rows) in *)
  let () = homogeneous (CList.length align_headers = ncolums) in
  (* Compute layout *)
  let rec layout n (rows : row list) =
    if n = 0 then []
    else
      let (col, rows) = vert_split rows in
      let ans = layout (n - 1) rows in
      let data = ref None in
      let iter args =
        let size = CList.map size args in
        match !data with
        | None -> data := Some size
        | Some s ->
          data := Some (CList.map2 (fun len1 len2 -> max len1 len2) s size)
      in
      let () = CList.iter iter col in
      let data = match !data with None -> [] | Some s -> s in
      data :: ans
  in
  let layout = layout ncolums (top::rows) in
  let map hd shape =
    let data_size = match shape with
    | [] -> 0
    | n :: shape -> CList.fold_left (fun accu n -> accu + n + val_padding) n shape
    in
    max (size hd) data_size
  in
  let col_size = CList.map2 map headers layout in
  (* Justify the data *)
  let headers = map3 justify align_headers col_size headers in
  let top = CList.map2 (justify Align.Middle) col_size (map3 justify_row align_top layout top) in

  let rows = CList.map (fun row -> CList.map2 (justify Align.Right) col_size (map3 justify_row align_rows layout row)) rows in
  (* Print the table *)
  let lines =
    print_separator `Top col_size ::
    print_row headers ::
    print_blank col_size ::
    print_row top ::
    print_separator `Mid col_size ::
    CList.map print_row rows @
    print_separator `Bot col_size ::
    []
  in
  String.concat "\n" lines

type raw_header = string
type raw_row = string list list

let raw_str s = { str = s; size = String.length s }

let raw_row r : row = List.map (List.map raw_str) r

let raw_print (headers : raw_header list) (top : raw_row) (rows : raw_row list)
  ?align_headers
  ?align_top
  ?align_rows
  () =
  let headers = List.map raw_str headers in
  let top = raw_row top in
  let rows = List.map raw_row rows in
  print headers top rows ?align_headers ?align_top ?align_rows ()
