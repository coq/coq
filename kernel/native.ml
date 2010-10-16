type caml_prim =
  (* Int31 operations *)
  | Int31print
 
  (* Array operations *)
  | ArrayMake
  | ArrayGet
  | ArrayGetdefault
  | ArraySet
  | ArrayCopy
  | ArrayReroot
  | ArrayLength

type iterator =
  | Int31foldi
  | Int31foldi_down
 
type prim_op = 
  | Int31head0
  | Int31tail0

  | Int31add
  | Int31sub
  | Int31mul
  | Int31div
  | Int31mod
  | Int31lsr
  | Int31lsl
  | Int31land
  | Int31lor
  | Int31lxor

  | Int31addc
  | Int31subc
  | Int31addCarryC
  | Int31subCarryC

  | Int31mulc
  | Int31diveucl
  | Int31div21

  | Int31addMulDiv

  | Int31eq
  | Int31lt
  | Int31le

  | Int31compare
  | Int31eqb_correct

type op =
  | Oprim of prim_op
  | Ocaml_prim of caml_prim
  | Oiterator of iterator



let caml_prim_to_string = function
  | Int31print -> "print"
  | ArrayMake -> "make"
  | ArrayGet -> "get"
  | ArrayGetdefault -> "default"
  | ArraySet -> "set"
  | ArrayCopy -> "copy"
  | ArrayReroot -> "reroot"
  | ArrayLength -> "length"
  
let iterator_to_string = function
  | Int31foldi -> "foldi"
  | Int31foldi_down -> "foldi_down"

let prim_to_string = function 
  | Int31head0     -> "head0"
  | Int31tail0     -> "tail0"
  | Int31add       -> "add"
  | Int31sub       -> "sub"
  | Int31mul       -> "mul"
  | Int31div       -> "div"
  | Int31mod       -> "mod"
  | Int31lsr       -> "lsr"
  | Int31lsl       -> "lsl"
  | Int31land      -> "land"
  | Int31lor       -> "lor"
  | Int31lxor      -> "lxor"

  | Int31addc      -> "addc"
  | Int31subc      -> "subc"
  | Int31addCarryC -> "addcarryc"
  | Int31subCarryC -> "subcarryc"

  | Int31mulc      -> "mulc"
  | Int31diveucl   -> "diveucl"
  | Int31div21     -> "div21"

  | Int31addMulDiv -> "addmuldiv"

  | Int31eq        -> "eq"
  | Int31lt        -> "lt"
  | Int31le        -> "le"

  | Int31compare   -> "compare"
  | Int31eqb_correct -> "eqb_correct"

let to_string = function
  | Ocaml_prim op -> caml_prim_to_string op
  | Oiterator op  -> iterator_to_string op
  | Oprim op      -> prim_to_string op

type arg_kind =
  | Kparam (* not needed for the elavuation of the primitive*)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf *)

type args_red = arg_kind list

(* Invariant only argument of type int31, array or an inductive can
   have kind Kwhnf *)

let caml_prim_kind = function
  | Int31print  -> [Kwhnf] 
  | ArrayMake   -> [Kparam;Kwhnf;Karg]
  | ArrayGet    -> [Kparam;Kwhnf;Kwhnf]
  | ArraySet    -> [Kparam;Kwhnf;Kwhnf;Karg]
  | ArrayGetdefault | ArrayCopy | ArrayReroot 
  | ArrayLength -> [Kparam;Kwhnf]
	
let iterator_kind _ = [Kparam;Kparam;Karg;Kwhnf;Kwhnf;Karg]
    
let prim_kind = function
  | Int31head0 | Int31tail0 -> [Kwhnf]
	
  | Int31add | Int31sub | Int31mul 
  | Int31div | Int31mod
  | Int31lsr | Int31lsl
  | Int31land | Int31lor | Int31lxor
  | Int31addc | Int31subc
  | Int31addCarryC | Int31subCarryC  | Int31mulc | Int31diveucl
  | Int31eq | Int31lt | Int31le | Int31compare -> [Kwhnf; Kwhnf]

  | Int31div21 | Int31addMulDiv -> [Kwhnf; Kwhnf; Kwhnf]
  | Int31eqb_correct -> [Karg;Karg;Kwhnf]

let op_kind = function
  | Ocaml_prim op -> caml_prim_kind op
  | Oiterator op  -> iterator_kind op
  | Oprim op      -> prim_kind op
	
	
let caml_prim_arity = function
  | ArrayMake -> (1,2)
  | ArrayGet -> (1,2)
  | ArrayGetdefault -> (1,1)
  | ArraySet -> (1,3)
  | ArrayCopy | ArrayReroot -> (1,1)
  | ArrayLength -> (1,1)
  | Int31print -> (0,1)
	
let iterator_arity _ = (2, 4)
    
let prim_arity = function
  | Int31head0 | Int31tail0 -> (0,1)
  | Int31add | Int31sub | Int31mul 
  | Int31div | Int31mod
  | Int31lsr | Int31lsl
  | Int31land | Int31lor | Int31lxor
  | Int31addc | Int31subc
  | Int31addCarryC | Int31subCarryC  | Int31mulc | Int31diveucl 
  | Int31eq | Int31lt | Int31le  
  | Int31compare -> (0,2)
	
  | Int31div21 | Int31addMulDiv -> (0,3)
  | Int31eqb_correct -> (0,3)

let arity = function
  | Ocaml_prim op -> caml_prim_arity op
  | Oiterator op  -> iterator_arity op
  | Oprim op      -> prim_arity op
  
module type UINT31 =
    sig 
      type t

      (* conversion to int *)
      val to_int : t -> int
      val of_int : int -> t

     (* convertion to a string *)
      val to_string : t -> string
      val of_string : string -> t

      (* logical operations *)
      val l_sl    : t -> t -> t
      val l_sr    : t -> t -> t
      val l_and   : t -> t -> t
      val l_xor   : t -> t -> t
      val l_or    : t -> t -> t

      (* Arithmetic operations *) 
      val add     : t -> t -> t
      val sub     : t -> t -> t
      val mul     : t -> t -> t
      val div     : t -> t -> t
      val rem     : t -> t -> t
      
      (* Specific arithmetic operations *)
      val mulc    : t -> t -> t * t
      val div21   : t -> t -> t -> t * t
      
      (* comparison *)
      val lt      : t -> t -> bool
      val eq      : t -> t -> bool
      val le      : t -> t -> bool
      val compare : t -> t -> int

      (* head and tail *)
      val head0   : t -> t
      val tail0   : t -> t
      
   end

module Uint31 : UINT31 =
  struct
    (* Invariant: For arch64 all extra bytes are set to 0 *)
    type t = int 
    
  
    (* to be used only on 32 bits achitectures *)
    let maxuint31 = Int32.of_string "0x7FFFFFFF"
    let uint_32 i =  Int32.logand (Int32.of_int i) maxuint31

    let select f32 f64 = if Sys.word_size = 64 then f64 else f32
 
    (* conversion to an int *)
    let to_int i = i 

    let of_int_32 i = i
    let of_int_64 i = i land 0x7FFFFFFF

    let of_int = select of_int_32 of_int_64
	
    (* convertion of an uint31 to a string *)
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
      l, h
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
    let rem_64 x y = if y = 0 then 0 else x / y
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
    let lt_32 x y = Int32.compare (uint_32 x) (uint_32 y) < 0
    let lt_64 x y = x < y
    let lt = select lt_32 lt_64
    
    let le_32 x y = Int32.compare (uint_32 x) (uint_32 y) <= 0
    let le_64 x y = x <= y
    let le = select le_32 le_64

    let eq x y = x = y

    let cmp_32 x y = Int32.compare (uint_32 x) (uint_32 y)
    let cmp_64 x y = compare x y
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

    (* digit *)

(*    let get_digit x p =
      if 0 <= p && p < 31 then x land (1 lsl p) <> 0
      else false

    let set_digit x p b =
      if 0 <= p && p < 31 then x 
      else 
	if b then x lor (1 lsl p)
	else x land ((-1) lxor (1 lsl p)) *)
  end

module type PARRAY = 
  sig 
    type 'a t
    val length  : 'a t -> Uint31.t
    val get     : 'a t -> Uint31.t -> 'a
    val set     : 'a t -> Uint31.t -> 'a -> 'a t
    val default : 'a t -> 'a 
    val make    : Uint31.t -> 'a -> 'a t
    val init    : Uint31.t -> (int -> 'a) -> 'a -> 'a t
    val copy    : 'a t -> 'a t
    val reroot  : 'a t -> 'a t

    val map : ('a -> 'b) -> 'a t -> 'b t
  
    (* /!\ Unsafe function *)
    val of_array : 'a array -> 'a t

 end

let max_array_length32 = 4194303 (* Sys.max_array_length on arch32 *) 

module Parray : PARRAY = 
  struct
    type 'a t = ('a kind) ref
    and 'a kind =
      | Array of 'a array 
      (* | Matrix of 'a array array *)
      | Updated of int * 'a * 'a t

    let of_array t = ref (Array t)
      
    let warn s =
      if Flags.vm_array_warn () then
	(Printf.fprintf stderr "WARNING %s\n" s; flush stderr)
	  
    let rec length p =
      match !p with
      | Array t -> Uint31.of_int (Array.length t - 1) (* The default value *)
      | Updated (_, _, p) -> length p

    let length p = 
      match !p with
      | Array t -> Uint31.of_int (Array.length t - 1)
      | Updated (_, _, p) -> warn "Array.length"; length p

    let rec get_updated p n =
      match !p with
      | Array t ->
	  let l =  Array.length t in
	  if 0 <= n && n < l then Array.unsafe_get t n
	  else (warn "Array.get: out of bound";Array.unsafe_get t (l-1))
      | Updated (k,e,p) -> if n = k then e else get_updated p n

    let get p n =
      let n = Uint31.to_int n in
      match !p with
      | Array t ->
	  let l = Array.length t in
	  if 0 <= n && n < l then Array.unsafe_get t n
	  else (warn "Array.get: out of bound";Array.unsafe_get t (l-1))
      | Updated _ -> warn "Array.get";get_updated p n
	    
    let set p n e =
      let kind = !p in
      let n = Uint31.to_int n in
      match kind with
      | Array t ->
	  if 0 <= n && n < Array.length t - 1 then
	    let res = ref kind in
	    p := Updated (n, Array.unsafe_get t n, res);
	    Array.unsafe_set t n e;
	    res
	  else (warn "Array.set: out of bound"; p)
      | Updated _ ->
	  warn "Array.set";
	  if 0 <= n && n < Uint31.to_int (length p) then
	    ref (Updated(n, e, p))   
	  else (warn "Array.set: out of bound"; p)

    let rec default_updated p =
      match !p with
      | Array t -> Array.unsafe_get t (Array.length t - 1)
      | Updated (_,_,p) -> default_updated p
	    
    let default p =
      match !p with
      | Array t -> Array.unsafe_get t (Array.length t - 1)
      | Updated (_,_,p) -> warn "Array.default";default_updated p

    let make n def = 
      let n = Uint31.to_int n in
      let n = 
	if 0 <= n && n < max_array_length32 then n + 1 
	else max_array_length32 in
      ref (Array (Array.make n def))
	
    let init n f def =
      let n = Uint31.to_int n in
      let n = 
	if 0 <= n && n < max_array_length32 then n + 1 
	else max_array_length32 in
      let t = Array.make n def in
      for i = 0 to n - 2 do t.(i) <- f i done;
      ref (Array t)
	
    let rec copy_updated p =
      match !p with
      | Array t -> Array.copy t
      | Updated (n,e,p) -> 
	  let t = copy_updated p in 
	  Array.unsafe_set t n e; t 
	  
    let copy p =
      let t = 
	match !p with
	| Array t -> Array.copy t
	| Updated _ -> warn "Array.copy"; copy_updated p in
      ref (Array t)
	
    let rec rerootk t k = 
      match !t with
      | Array _ -> k ()
      | Updated (i, v, t') -> 
	  let k' () =
	    begin match !t' with
	    | Array a as n ->
		let v' = a.(i) in
		a.(i) <- v;
		t := n;
		t' := Updated (i, v', t)
	    | Updated _ -> assert false 
	    end; k() in
	  rerootk t' k'
	    
    let reroot t = rerootk t (fun () -> t)

    let map f p =
      match !p with
      | Array t -> ref (Array (Array.map f t))
      | _ ->
	  let len = Uint31.to_int (length p) in
	  ref (Array 
		 (Array.init (len + 1) 
		    (fun i -> f (get p (Uint31.of_int i)))))
  end
	    
module Narray : PARRAY with type 'a t = 'a array =
  struct
    type 'a t = 'a array

    let of_array t = assert false

    let length p = Uint31.of_int (Array.length p - 1)

    let get p i = 
      let i = Uint31.to_int i in
      if 0 <= i && i < Array.length p then p.(i)
      else p.(Array.length p - 1)

    let set p i a = 
      let i = Uint31.to_int i in
      if 0 <= i && i < Array.length p - 1 then
	let p' = Array.copy p in p'.(i) <- a; p'
      else p

    let default p = p.(Array.length p - 1)

    let make n def = 
      let n = Uint31.to_int n in
      let n = 
	if 0 <= n && n < max_array_length32 then n + 1 
	else max_array_length32 in
      Array.make n def
	
    let init n f def =
      let n = Uint31.to_int n in
      let n = 
	if 0 <= n && n < max_array_length32 then n + 1 
	else max_array_length32 in
      let t = Array.make n def in
      for i = 0 to n - 2 do t.(i) <- f i done;
      t

    let copy p = p
    let reroot p = p

    let map = Array.map

  end


(** Special Entries for Register **)

type prim_ind =
  | PIT_bool
  | PIT_carry
  | PIT_pair
  | PIT_cmp
  | PIT_eq

type prim_type =
  | PT_int31
  | PT_array

type retro_action =
  | Retro_ind of prim_ind
  | Retro_type of prim_type
  | Retro_inline 

type op_or_type = 
  | OT_op of op
  | OT_type of prim_type


let prim_ind_to_string = function
  | PIT_bool -> "bool"
  | PIT_carry -> "carry"
  | PIT_pair -> "pair"
  | PIT_cmp -> "cmp"
  | PIT_eq -> "eq"

let prim_type_to_string = function
  | PT_int31 -> "int31"
  | PT_array -> "array"

let op_or_type_to_string = function
  | OT_op op -> to_string op
  | OT_type t -> prim_type_to_string t

