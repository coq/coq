open Utest

let log_out_ch = open_log_out_ch __FILE__

let reference_filter =
  let rec filter f = function
    | [] -> []
    | x :: tl as l ->
      if f x then
        let tl' = filter f tl in
        if tl == tl' then l else x :: tl'
      else filter f tl
  in
  filter

let () =
  let () = Random.self_init () in
  let seed = Random.bits() in
  Printf.fprintf log_out_ch "seed = %d\n" seed;
  Random.init seed

let lists =
  List.init 100 (fun _ ->
      let len = Random.int 100 in
      List.init len (fun _ ->
          let b = Random.bool() in
          let v = Random.bits() in
          b,v))

let t1 = mk_bool_test "clib-clist0"
    "filter produces correct values"
    (List.for_all (fun l ->
         let expected : (bool * int) list = reference_filter fst l in
         let generated = CList.filter fst l in
         expected = generated)
        lists)

let lists' =
  List.init 100 (fun _ ->
      let len = Random.int 100 in
      let keepafter = if len = 0 then 0 else Random.int len in
      let l = List.init len (fun i ->
          let b = i >= keepafter || Random.bool () in
          let v = Random.bits() in
          b, v) in
      keepafter, l)

let t2 = mk_bool_test "clib-clist1"
    "filter correctly preserves physical equality of tails"
    (List.for_all (fun (keepafter,l) ->
         flush log_out_ch;
         let generated = CList.filter fst l in
         let tl = CList.skipn keepafter l in
         let generated_tl = CList.lastn (List.length tl) generated in
         tl == generated_tl)
       lists')

let tests = [ t1; t2 ]

let _ = run_tests __FILE__ log_out_ch tests
