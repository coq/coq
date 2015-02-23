  (* Invariant: For arch64 all extra bytes are set to 0 *)
type t = int 
    
  (* to be used only on 32 bits architectures *)
let maxuint31 = Int32.of_string "0x7FFFFFFF"
let uint_32 i =  Int32.logand (Int32.of_int i) maxuint31
    
let select f32 f64 = if Sys.word_size = 64 then f64 else f32
 
    (* conversion to an int *)
let to_int i = i 

let of_int_32 i = i
let of_int_64 i = i land 0x7FFFFFFF

let of_int = select of_int_32 of_int_64
let of_uint i = i
 	
    (* conversion of an uint31 to a string *)
let to_string_32 i = Int32.to_string (uint_32 i)
let to_string_64 = string_of_int 

let to_string = select to_string_32 to_string_64
let of_string s = 
  let i32 = Int32.of_string s in
  if Int32.compare Int32.zero i32 <= 0
      && Int32.compare i32 maxuint31 <= 0 
  then Int32.to_int i32
  else raise (Failure "int_of_string")

      

    (* logical shift *)
let l_sl x y = 
  of_int (if 0 <= y && y < 31 then x lsl y else 0)
    
let l_sr x y = 
  if 0 <= y && y < 31 then x lsr y else 0
    
let l_and x y = x land y
let l_or x y = x lor y
let l_xor x y = x lxor y

    (* addition of int31 *)
let add x y = of_int (x + y)
 
    (* subtraction *)
let sub x y = of_int (x - y)
   
    (* multiplication *)
let mul x y = of_int (x * y)
    
    (* exact multiplication *)
let mulc_32 x y =
  let x = Int64.of_int32 (uint_32 x) in
  let y = Int64.of_int32 (uint_32 y) in
  let m = Int64.mul x y in
  let l = Int64.to_int m in
  let h = Int64.to_int (Int64.shift_right_logical m 31) in
  h,l

let mulc_64 x y =
  let m = x * y in
  let l = of_int_64 m in
  let h = of_int_64 (m lsr 31) in
  h, l
let mulc = select mulc_32 mulc_64

    (* division *)
let div_32 x y = 
  if y = 0 then 0 else
  Int32.to_int (Int32.div (uint_32 x) (uint_32 y)) 
let div_64 x y = if y = 0 then 0 else  x / y
let div = select div_32 div_64
    
    (* modulo *)
let rem_32 x y = 
  if y = 0 then 0 
  else Int32.to_int (Int32.rem (uint_32 x) (uint_32 y))
let rem_64 x y = if y = 0 then 0 else x mod y
let rem = select rem_32 rem_64
    
    (* division of two numbers by one *)
let div21_32 xh xl y =
  if y = 0 then (0,0) 
  else
    let x = 
      Int64.logor 
	(Int64.shift_left (Int64.of_int32 (uint_32 xh)) 31) 
	(Int64.of_int32 (uint_32 xl)) in
    let y = Int64.of_int32 (uint_32 y) in
    let q = Int64.div x y in
    let r = Int64.rem x y in
    Int64.to_int q, Int64.to_int r
let div21_64 xh xl y =
  if y = 0 then (0,0) 
  else
    let x = (xh lsl 31) lor xl in
    let q = x / y in
    let r = x mod y in
    q, r
let div21 = select div21_32 div21_64
    
    (* comparison *)
let lt_32 x y = (x lxor 0x40000000) < (y lxor 0x40000000)

(* Do not remove the type information it is really important for 
   efficiency *)
let lt_64 (x:int) (y:int) = x < y
let lt = select lt_32 lt_64

let le_32 x y = 
 (x lxor 0x40000000) <= (y lxor 0x40000000)

(* Do not remove the type information it is really important for
   efficiency *)
let le_64 (x:int) (y:int) = x <= y
let le = select le_32 le_64

let equal (x:int) (y:int) = x == y
    
let cmp_32 x y = Int32.compare (uint_32 x) (uint_32 y)
(* Do not remove the type information it is really important for 
   efficiency *)
let cmp_64 (x:int) (y:int) = compare x y
let compare = select cmp_32 cmp_64
  
    (* head tail *)

let head0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0x7FFF0000 = 0 then r := !r + 15
  else x := !x lsr 15;
  if !x land 0xFF00 = 0 then (x := !x lsl 8; r := !r + 8);
  if !x land 0xF000 = 0 then (x := !x lsl 4; r := !r + 4);
  if !x land 0xC000 = 0 then (x := !x lsl 2; r := !r + 2);
  if !x land 0x8000 = 0 then (x := !x lsl 1; r := !r + 1);
  if !x land 0x8000 = 0 then (               r := !r + 1);
  !r;;

let tail0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0xFFFF = 0 then (x := !x lsr 16; r := !r + 16);
  if !x land 0xFF = 0   then (x := !x lsr 8;  r := !r + 8);
  if !x land 0xF = 0    then (x := !x lsr 4;  r := !r + 4);
  if !x land 0x3 = 0    then (x := !x lsr 2;  r := !r + 2);
  if !x land 0x1 = 0    then (                r := !r + 1);
  !r

let add_digit x d =
  (x lsl 1) lor d
