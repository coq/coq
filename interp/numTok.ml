type t = {
  int : string;
  frac : string;
  exp : string
}

let equal n1 n2 =
  String.(equal n1.int n2.int && equal n1.frac n2.frac && equal n1.exp n2.exp)

let int s = { int = s; frac = ""; exp = "" }

let to_string n = n.int ^ (if n.frac = "" then "" else "." ^ n.frac) ^ n.exp

let parse =
  let buff = ref (Bytes.create 80) in
  let store len x =
    let open Bytes in
    if len >= length !buff then
      buff := cat !buff (create (length !buff));
    set !buff len x;
    succ len in
  let get_buff len = Bytes.sub_string !buff 0 len in
  (* reads [0-9]* *)
  let rec number len s = match Stream.peek s with
    | Some (('0'..'9') as c) -> Stream.junk s; number (store len c) s
    | _ -> len in
  fun s ->
  let i = get_buff (number 0 s) in
  let f =
    match Stream.npeek 2 s with
    | '.' :: (('0'..'9') as c) :: _ ->
       Stream.junk s; Stream.junk s; get_buff (number (store 0 c) s)
    | _ -> "" in
  let e =
    match (Stream.npeek 2 s) with
    | (('e'|'E') as e) :: ('0'..'9' as c) :: _ ->
       Stream.junk s; Stream.junk s; get_buff (number (store (store 0 e) c) s)
    | (('e'|'E') as e) :: (('+'|'-') as sign) :: _ ->
       begin match Stream.npeek 3 s with
       | _ :: _ :: ('0'..'9' as c) :: _ ->
          Stream.junk s; Stream.junk s; Stream.junk s;
          get_buff (number (store (store (store 0 e) sign) c) s)
       | _ -> ""
       end
    | _ -> "" in
  { int = i; frac = f; exp = e }

let of_string s =
  if s = "" || s.[0] < '0' || s.[0] > '9' then None else
    let strm = Stream.of_string (s ^ "  ") in
    let n = parse strm in
    if Stream.count strm >= String.length s then Some n else None
