type header = string

type row = string list list

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
  let ls = List.map split ls in
  List.split ls

let justify align n s =
  let len = String.length s in
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
  String.concat (String.make val_padding ' ') data

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
  let len = List.length col_size in
  let pad = dashes row_padding in
  let () = assert (0 < len) in
  let map n = dashes n in
  angle `Lft vkind ^ pad ^
  String.concat (pad ^ angle `Mid vkind ^ pad) (List.map map col_size) ^
  pad ^ angle `Rgt vkind

let print_blank col_size =
  let len = List.length col_size in
  let () = assert (0 < len) in
  let pad = String.make row_padding ' ' in
  let map n = String.make n ' ' in
  "│" ^ pad ^ String.concat (pad ^ "│" ^ pad) (List.map map col_size) ^ pad ^ "│"

let print_row row =
  let len = List.length row in
  let () = assert (0 < len) in
  let pad = String.make row_padding ' ' in
  "│" ^ pad ^ String.concat (pad ^ "│" ^ pad) row ^ pad ^ "│"

let default_align_headers = List.map (fun _ -> Align.Middle)
let default_align_top = List.map @@ List.map (fun _ -> Align.Middle)
let default_align_rows rows =
  List.hd rows
  |> List.map @@ List.map (fun _ -> Align.Right)

(* Invariant : all rows must have the same shape *)

let print (headers : header list) (top : row) (rows : row list)
  ?(align_headers = default_align_headers headers)
  ?(align_top = default_align_top top)
  ?(align_rows = default_align_rows rows)
  () =
  (* Sanitize input *)
  let ncolums = List.length headers in
  let shape = ref None in
  let check row =
    let () = homogeneous (List.length row = ncolums) in
    let rshape : int list = List.map (fun data -> List.length data) row in
    match !shape with
    | None -> shape := Some rshape
    | Some s -> homogeneous (rshape = s)
  in
  let () = List.iter check rows in
  (* TODO: check is broken please fix *)
  (* let () = List.iter check (List.map (List.map (fun _ -> [])) align_rows) in *)
  let () = homogeneous (List.length align_headers = ncolums) in
  (* Compute layout *)
  let rec layout n (rows : row list) =
    if n = 0 then []
    else
      let (col, rows) = vert_split rows in
      let ans = layout (n - 1) rows in
      let data = ref None in
      let iter args =
        let size = List.map String.length args in
        match !data with
        | None -> data := Some size
        | Some s ->
          data := Some (List.map2 (fun len1 len2 -> max len1 len2) s size)
      in
      let () = List.iter iter col in
      let data = match !data with None -> [] | Some s -> s in
      data :: ans
  in
  let layout = layout ncolums (top::rows) in
  let map hd shape =
    let data_size = match shape with
    | [] -> 0
    | n :: shape -> List.fold_left (fun accu n -> accu + n + val_padding) n shape
    in
    max (String.length hd) data_size
  in
  let col_size = List.map2 map headers layout in
  (* Justify the data *)
  let headers = map3 justify align_headers col_size headers in
  let top = List.map2 (justify Align.Middle) col_size (map3 justify_row align_top layout top) in

  let rows = List.map (fun row -> List.map2 (justify Align.Right) col_size (map3 justify_row align_rows layout row)) rows in
  (* Print the table *)
  let lines =
    print_separator `Top col_size ::
    print_row headers ::
    print_blank col_size ::
    print_row top ::
    print_separator `Mid col_size ::
    List.map print_row rows @
    print_separator `Bot col_size ::
    []
  in
  String.concat "\n" lines
