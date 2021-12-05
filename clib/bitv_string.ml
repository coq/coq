
(*s An alternative implementation using strings *)

let byte s i = Char.code (Bytes.unsafe_get s i)
let set_byte s i x = Bytes.unsafe_set s i (Char.chr x)

type t = {
  length : int;
  bits   : Bytes.t }

let length v = v.length

let[@inline] equal (v1:t) (v2:t) = v1 = v2
(*s Perhaps the polymorphic equality is actually faster or good enough?
    Did not test it. *)

let max_length = Sys.max_string_length * 8

let exceeds_max_length n =
  let s = n / 8 in
  (if n mod 8 = 0 then s else s + 1) > Sys.max_string_length

let low_mask = Array.init 9 (fun i -> (1 lsl i) - 1)

let create n b =
  if n < 0 || n > max_length then invalid_arg "Bitv.create";
  let initv = if b then 255 else 0 in
  let q = n lsr 3 in
  let r = n land 7 in
  if r = 0 then
    { length = n; bits = Bytes.make q (Char.chr initv) }
  else begin
    let s = Bytes.make (q + 1) (Char.chr initv) in
    set_byte s q (initv land low_mask.(r));
    { length = n; bits = s }
  end

let normalize v =
  let r = v.length land 7 in
  if r > 0 then
    let b = v.bits in
    let s = Bytes.length b in
    set_byte b (s-1) ((byte b (s-1)) land low_mask.(r))

let copy v = { length = v.length; bits = Bytes.copy v.bits }

let unsafe_get v n =
  let i = n lsr 3 in
  (byte v.bits i) land (1 lsl (n land 7)) > 0

let get v n =
  if n < 0 || n >= v.length then invalid_arg "Bitv.get";
  unsafe_get v n

let unsafe_set v n b =
  let i = n lsr 3 in
  let c = byte v.bits i in
  let mask = 1 lsl (n land 7) in
  set_byte v.bits i (if b then c lor mask else c land (lnot mask))

let set v n b =
  if n < 0 || n >= v.length then invalid_arg "Bitv.set";
  unsafe_set v n b

(*s [init] is implemented naively using [unsafe_set]. *)

let init n f =
  let v = create n false in
  for i = 0 to pred n do
    unsafe_set v i (f i)
  done;
  v

let fill v ofs len b =
  if ofs < 0 || len < 0 || ofs + len > v.length then invalid_arg "Bitv.fill";
  (* FIXME: more efficient version using blit_ones and blit_zeros *)
  for i = ofs to ofs + len - 1 do unsafe_set v i b done

(*s All the iterators are implemented as for traditional arrays, using
    [unsafe_get]. For [iter] and [map], we do not precompute [(f
    true)] and [(f false)] since [f] may have side-effects. *)

let iter f v =
  for i = 0 to v.length - 1 do f (unsafe_get v i) done

let map f v =
  let l = v.length in
  let r = create l false in
  for i = 0 to l - 1 do
    unsafe_set r i (f (unsafe_get v i))
  done;
  r

let iteri f v =
  for i = 0 to v.length - 1 do f i (unsafe_get v i) done

let mapi f v =
  let l = v.length in
  let r = create l false in
  for i = 0 to l - 1 do
    unsafe_set r i (f i (unsafe_get v i))
  done;
  r

let fold_left f x v =
  let r = ref x in
  for i = 0 to v.length - 1 do
    r := f !r (unsafe_get v i)
  done;
  !r

let fold_right f v x =
  let r = ref x in
  for i = v.length - 1 downto 0 do
    r := f (unsafe_get v i) !r
  done;
  !r

let foldi_left f x v =
  let r = ref x in
  for i = 0 to v.length - 1 do
    r := f !r i (unsafe_get v i)
  done;
  !r

let foldi_right f v x =
  let r = ref x in
  for i = v.length - 1 downto 0 do
    r := f i (unsafe_get v i) !r
  done;
  !r

let iteri_true f v =
  Bytes.iteri
    (fun i x -> let x = Char.code x in if x != 0 then begin
      let i = i lsl 3 in
      for j = 0 to 7 do if x land (1 lsl j) > 0 then f (i + j) done
    end)
    v.bits

(*s Population count *)

let rec naive_pop x =
  assert (x < 0x100);
  if x = 0 then 0 else 1 + naive_pop (x - (x land -x))

let pop8 = Array.init 0x100 naive_pop
let pop8 n = Array.unsafe_get pop8 n

let pop v =
  let n = Bytes.length v.bits in
  let rec loop acc i =
    if i >= n then acc else loop (acc + pop8 (byte v.bits i)) (i + 1) in
  loop 0 0

(*s Bitwise operations. It is straigthforward, since bitwise operations
    can be realized by the corresponding bitwise operations over integers.
    However, one has to take care of normalizing the result of [bwnot]
    which introduces ones in highest significant positions. *)

let bw_and v1 v2 =
  let l = v1.length in
  if l <> v2.length then invalid_arg "Bitv.bw_and";
  let b1 = v1.bits
  and b2 = v2.bits in
  let n = Bytes.length b1 in
  let a = Bytes.make n (Char.chr 0) in
  for i = 0 to n - 1 do
    set_byte a i ((byte b1 i) land (byte b2 i))
  done;
  { length = l; bits = a }

let bw_or v1 v2 =
  let l = v1.length in
  if l <> v2.length then invalid_arg "Bitv.bw_or";
  let b1 = v1.bits
  and b2 = v2.bits in
  let n = Bytes.length b1 in
  let a = Bytes.make n (Char.chr 0) in
  for i = 0 to n - 1 do
    set_byte a i ((byte b1 i) lor (byte b2 i))
  done;
  { length = l; bits = a }

let bw_xor v1 v2 =
  let l = v1.length in
  if l <> v2.length then invalid_arg "Bitv.bw_or";
  let b1 = v1.bits
  and b2 = v2.bits in
  let n = Bytes.length b1 in
  let a = Bytes.make n (Char.chr 0) in
  for i = 0 to n - 1 do
    set_byte a i ((byte b1 i) lxor (byte b2 i))
  done;
  { length = l; bits = a }

let bw_not v =
  let b = v.bits in
  let n = Bytes.length b in
  let a = Bytes.make n (Char.chr 0) in
  for i = 0 to n - 1 do
    set_byte a i (255 land (lnot (byte b i)))
  done;
  let r = { length = v.length; bits = a } in
  normalize r;
  r

(*s Coercions to/from lists of integers *)

let of_list l =
  let n = List.fold_left max 0 l in
  let b = create (succ n) false in
  let add_element i =
    (* negative numbers are invalid *)
    if i < 0 then invalid_arg "Bitv.of_list";
    unsafe_set b i true
  in
  List.iter add_element l;
  b

let of_list_mapi l f =
  let b = create (List.length l) false in
  List.iteri (fun i a -> if f i a then unsafe_set b i true) l;
  b

let of_list_with_length l len =
  let b = create len false in
  let add_element i =
    if i < 0 || i >= len then invalid_arg "Bitv.of_list_with_length";
    unsafe_set b i true
  in
  List.iter add_element l;
  b

let to_list b =
  let n = length b in
  let rec make i acc =
    if i < 0 then acc
    else make (pred i) (if unsafe_get b i then i :: acc else acc)
  in
  make (pred n) []

let append x y =
  (* FIXME slow *)
  let len_x = length x in
  let len_y = length y in
  let res = create (len_x + len_y) false in
  for i = 0 to len_x - 1 do
    unsafe_set res i (unsafe_get x i)
  done;
  for i = 0 to len_y - 1 do
    unsafe_set res (i + len_x) (unsafe_get y i)
  done;
  res

let all_true v =
  let r = v.length land 7 in
  let len = Bytes.length v.bits in
  try
    for i = 0 to len - (if r = 0 then 1 else 2) do
      if byte v.bits i <> 255 then raise_notrace Exit
    done;
    if r <> 0 && byte v.bits (len - 1) lor (255 - low_mask.(r)) <> 255 then
      raise_notrace Exit;
    true
  with Exit -> false

let compose v1 v2 =
  if length v1 <> length v2 then invalid_arg "bitv_string.compose";
  let len_res = pop v1 in
  let res = create len_res false in
  let offset = ref 0  in
  for i = 0 to len_res - 1 do
    while not (unsafe_get v1 (i + !offset)) do
      incr offset
    done;
    unsafe_set res i (unsafe_get v2 (i + !offset))
  done;
  res
