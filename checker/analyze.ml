(** Headers *)

let prefix_small_block =         0x80
let prefix_small_int =           0x40
let prefix_small_string =        0x20

[@@@ocaml.warning "-32"]
let code_int8 =                  0x00
let code_int16 =                 0x01
let code_int32 =                 0x02
let code_int64 =                 0x03
let code_shared8 =               0x04
let code_shared16 =              0x05
let code_shared32 =              0x06
let code_double_array32_little = 0x07
let code_block32 =               0x08
let code_string8 =               0x09
let code_string32 =              0x0A
let code_double_big =            0x0B
let code_double_little =         0x0C
let code_double_array8_big =     0x0D
let code_double_array8_little =  0x0E
let code_double_array32_big =    0x0F
let code_codepointer =           0x10
let code_infixpointer =          0x11
let code_custom =                0x12
let code_block64 =               0x13

[@@@ocaml.warning "-37"]
type code_descr =
| CODE_INT8
| CODE_INT16
| CODE_INT32
| CODE_INT64
| CODE_SHARED8
| CODE_SHARED16
| CODE_SHARED32
| CODE_DOUBLE_ARRAY32_LITTLE
| CODE_BLOCK32
| CODE_STRING8
| CODE_STRING32
| CODE_DOUBLE_BIG
| CODE_DOUBLE_LITTLE
| CODE_DOUBLE_ARRAY8_BIG
| CODE_DOUBLE_ARRAY8_LITTLE
| CODE_DOUBLE_ARRAY32_BIG
| CODE_CODEPOINTER
| CODE_INFIXPOINTER
| CODE_CUSTOM
| CODE_BLOCK64

let code_max = 0x13

let magic_number = "\132\149\166\190"

(** Memory reification *)

module LargeArray :
sig
  type 'a t
  val empty : 'a t
  val length : 'a t -> int
  val make : int -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val set : 'a t -> int -> 'a -> unit
end =
struct

  let max_length = Sys.max_array_length

  type 'a t = 'a array array * 'a array
  (** Invariants:
      - All subarrays of the left array have length [max_length].
      - The right array has length < [max_length].
  *)

  let empty = [||], [||]

  let length (vl, vr) =
    (max_length * Array.length vl) + Array.length vr

  let make n x =
    let k = n / max_length in
    let r = n mod max_length in
    let vl = Array.init k (fun _ -> Array.make max_length x) in
    let vr = Array.make r x in
    (vl, vr)

  let get (vl, vr) n =
    let k = n / max_length in
    let r = n mod max_length in
    let len = Array.length vl in
    if k < len then vl.(k).(r)
    else if k == len then vr.(r)
    else invalid_arg "index out of bounds"

  let set (vl, vr) n x =
    let k = n / max_length in
    let r = n mod max_length in
    let len = Array.length vl in
    if k < len then vl.(k).(r) <- x
    else if k == len then vr.(r) <- x
    else invalid_arg "index out of bounds"

end

type repr =
| RInt of int
| RInt63 of Uint63.t
| RBlock of (int * int) (* tag × len *)
| RString of string
| RPointer of int
| RCode of int

type data =
| Int of int (* value *)
| Ptr of int (* pointer *)
| Atm of int (* tag *)
| Fun of int (* address *)

type obj =
| Struct of int * data array (* tag × data *)
| Int63 of Uint63.t (* Primitive integer *)
| String of string

module type Input =
sig
  type t
  val input_byte : t -> int
  val input_binary_int : t -> int
end

module type S =
sig
  type input
  val parse : input -> (data * obj LargeArray.t)
end

module Make(M : Input) =
struct

open M

type input = M.t

let current_offset = ref 0

let input_byte chan =
  let () = incr current_offset in
  input_byte chan

let input_binary_int chan =
  let () = current_offset := !current_offset + 4 in
  input_binary_int chan

let input_char chan = Char.chr (input_byte chan)
let input_string len chan = String.init len (fun _ -> input_char chan)

let parse_header chan =
  let () = current_offset := 0 in
  let magic = input_string 4 chan in
  let length = input_binary_int chan in
  let objects = input_binary_int chan in
  let size32 = input_binary_int chan in
  let size64 = input_binary_int chan in
  (magic, length, size32, size64, objects)

let input_int8s chan =
  let i = input_byte chan in
  if i land 0x80 = 0
    then i
    else i lor ((-1) lsl 8)

let input_int8u = input_byte

let input_int16s chan =
  let i = input_byte chan in
  let j = input_byte chan in
  let ans = (i lsl 8) lor j in
  if i land 0x80 = 0
    then ans
    else ans lor ((-1) lsl 16)

let input_int16u chan =
  let i = input_byte chan in
  let j = input_byte chan in
  (i lsl 8) lor j

let input_int32s chan =
  let i = input_byte chan in
  let j = input_byte chan in
  let k = input_byte chan in
  let l = input_byte chan in
  let ans = (i lsl 24) lor (j lsl 16) lor (k lsl 8) lor l in
  if i land 0x80 = 0
    then ans
    else ans lor ((-1) lsl 31)

let input_int32u chan =
  let i = input_byte chan in
  let j = input_byte chan in
  let k = input_byte chan in
  let l = input_byte chan in
  (i lsl 24) lor (j lsl 16) lor (k lsl 8) lor l

let input_int64s chan =
  let i = input_byte chan in
  let j = input_byte chan in
  let k = input_byte chan in
  let l = input_byte chan in
  let m = input_byte chan in
  let n = input_byte chan in
  let o = input_byte chan in
  let p = input_byte chan in
  let ans =
    (i lsl 56) lor (j lsl 48) lor (k lsl 40) lor (l lsl 32) lor
    (m lsl 24) lor (n lsl 16) lor (o lsl 8) lor p
  in
  if i land 0x80 = 0
    then ans
    else ans lor ((-1) lsl 63)

let input_int64u chan =
  let i = input_byte chan in
  let j = input_byte chan in
  let k = input_byte chan in
  let l = input_byte chan in
  let m = input_byte chan in
  let n = input_byte chan in
  let o = input_byte chan in
  let p = input_byte chan in
  (i lsl 56) lor (j lsl 48) lor (k lsl 40) lor (l lsl 32) lor
  (m lsl 24) lor (n lsl 16) lor (o lsl 8) lor p

let input_header32 chan =
  let i = input_byte chan in
  let j = input_byte chan in
  let k = input_byte chan in
  let l = input_byte chan in
  let tag = l in
  let len = (i lsl 14) lor (j lsl 6) lor (k lsr 2) in
  (tag, len)

let input_header64 chan =
  let i = input_byte chan in
  let j = input_byte chan in
  let k = input_byte chan in
  let l = input_byte chan in
  let m = input_byte chan in
  let n = input_byte chan in
  let o = input_byte chan in
  let p = input_byte chan in
  let tag = p in
  let len =
    (i lsl 46) lor (j lsl 38) lor (k lsl 30) lor (l lsl 22) lor
    (m lsl 14) lor (n lsl 6) lor (o lsr 2)
  in
  (tag, len)

let input_cstring chan : string =
  let buff = Buffer.create 17 in
  let rec loop () =
    match input_char chan with
    | '\o000' -> Buffer.contents buff
    | c -> Buffer.add_char buff c |> loop
  in loop ()

let input_intL chan : int64 =
  let i = input_byte chan in
  let j = input_byte chan in
  let k = input_byte chan in
  let l = input_byte chan in
  let m = input_byte chan in
  let n = input_byte chan in
  let o = input_byte chan in
  let p = input_byte chan in
  let ( lsl ) x y = Int64.(shift_left (of_int x) y) in
  let ( lor ) = Int64.logor in
  (i lsl 56) lor (j lsl 48) lor (k lsl 40) lor (l lsl 32) lor
  (m lsl 24) lor (n lsl 16) lor (o lsl 8) lor (Int64.of_int p)

let parse_object chan =
  let data = input_byte chan in
  if prefix_small_block <= data then
    let tag = data land 0x0F in
    let len = (data lsr 4) land 0x07 in
    RBlock (tag, len)
  else if prefix_small_int <= data then
    RInt (data land 0x3F)
  else if prefix_small_string <= data then
    let len = data land 0x1F in
    RString (input_string len chan)
  else if data > code_max then
    assert false
  else match (Obj.magic data) with
  | CODE_INT8 ->
    RInt (input_int8s chan)
  | CODE_INT16 ->
    RInt (input_int16s chan)
  | CODE_INT32 ->
    RInt (input_int32s chan)
  | CODE_INT64 ->
    RInt (input_int64s chan)
  | CODE_SHARED8 ->
    RPointer (input_int8u chan)
  | CODE_SHARED16 ->
    RPointer (input_int16u chan)
  | CODE_SHARED32 ->
    RPointer (input_int32u chan)
  | CODE_BLOCK32 ->
    RBlock (input_header32 chan)
  | CODE_BLOCK64 ->
    RBlock (input_header64 chan)
  | CODE_STRING8 ->
    let len = input_int8u chan in
    RString (input_string len chan)
  | CODE_STRING32 ->
    let len = input_int32u chan in
    RString (input_string len chan)
  | CODE_CODEPOINTER ->
    let addr = input_int32u chan in
    for _i = 0 to 15 do ignore (input_byte chan); done;
    RCode addr
  | CODE_CUSTOM ->
    begin match input_cstring chan with
    | "_j" -> RInt63 (Uint63.of_int64 (input_intL chan))
    | s -> Printf.eprintf "Unhandled custom code: %s" s; assert false
    end
  | CODE_DOUBLE_ARRAY32_LITTLE
  | CODE_DOUBLE_BIG
  | CODE_DOUBLE_LITTLE
  | CODE_DOUBLE_ARRAY8_BIG
  | CODE_DOUBLE_ARRAY8_LITTLE
  | CODE_DOUBLE_ARRAY32_BIG
  | CODE_INFIXPOINTER
    -> Printf.eprintf "Unhandled code %04x\n%!" data; assert false

let parse chan =
  let (magic, len, _, _, size) = parse_header chan in
  let () = assert (magic = magic_number) in
  let memory = LargeArray.make size (Struct ((-1), [||])) in
  let current_object = ref 0 in
  let fill_obj = function
  | RPointer n ->
    let data = Ptr (!current_object - n) in
    data, None
  | RInt n ->
    let data = Int n in
    data, None
  | RString s ->
    let data = Ptr !current_object in
    let () = LargeArray.set memory !current_object (String s) in
    let () = incr current_object in
    data, None
  | RBlock (tag, 0) ->
    (* Atoms are never shared *)
    let data = Atm tag in
    data, None
  | RBlock (tag, len) ->
    let data = Ptr !current_object in
    let nblock = Array.make len (Atm (-1)) in
    let () = LargeArray.set memory !current_object (Struct (tag, nblock)) in
    let () = incr current_object in
    data, Some nblock
  | RCode addr ->
    let data = Fun addr in
    data, None
  | RInt63 i ->
    let data = Ptr !current_object in
    let () = LargeArray.set memory !current_object (Int63 i) in
    let () = incr current_object in
    data, None
  in

  let rec fill block off accu =
    if Array.length block = off then
      match accu with
      | [] -> ()
      | (block, off) :: accu -> fill block off accu
    else
      let data, nobj = fill_obj (parse_object chan) in
      let () = block.(off) <- data in
      let block, off, accu = match nobj with
      | None -> block, succ off, accu
      | Some nblock -> nblock, 0, ((block, succ off) :: accu)
      in
      fill block off accu
  in
  let ans = [|Atm (-1)|] in
  let () = fill ans 0 [] in
  (ans.(0), memory)

end

module IChannel =
struct
  type t = in_channel
  let input_byte = Pervasives.input_byte
  let input_binary_int = Pervasives.input_binary_int
end

module IString =
struct
  type t = (string * int ref)

  let input_byte (s, off) =
    let ans = Char.code (s.[!off]) in
    let () = incr off in
    ans

  let input_binary_int chan =
    let i = input_byte chan in
    let j = input_byte chan in
    let k = input_byte chan in
    let l = input_byte chan in
    let ans = (i lsl 24) lor (j lsl 16) lor (k lsl 8) lor l in
    if i land 0x80 = 0
      then ans
      else ans lor ((-1) lsl 31)

end

module PChannel = Make(IChannel)
module PString = Make(IString)

let parse_channel = PChannel.parse
let parse_string s = PString.parse (s, ref 0)

let instantiate (p, mem) =
  let len = LargeArray.length mem in
  let ans = LargeArray.make len (Obj.repr 0) in
  (* First pass: initialize the subobjects *)
  for i = 0 to len - 1 do
    let obj = match LargeArray.get mem i with
    | Struct (tag, blk) -> Obj.new_block tag (Array.length blk)
    | Int63 i -> Obj.repr i
    | String str -> Obj.repr str
    in
    LargeArray.set ans i obj
  done;
  let get_data = function
  | Int n -> Obj.repr n
  | Ptr p -> LargeArray.get ans p
  | Atm tag -> Obj.new_block tag 0
  | Fun _ -> assert false (* We shouldn't serialize closures *)
  in
  (* Second pass: set the pointers *)
  for i = 0 to len - 1 do
    match LargeArray.get mem i with
    | Struct (_, blk) ->
      let obj = LargeArray.get ans i in
      for k = 0 to Array.length blk - 1 do
        Obj.set_field obj k (get_data blk.(k))
      done
    | Int63 _
    | String _ -> ()
  done;
  get_data p
