{

  open Lexing
}

let space = 
  [' ' '\010' '\013' '\009' '\012']
let char = ['A'-'Z' 'a'-'z' '_' '0'-'9']

let ident = char+

let value = ('"'|'[')( [^ '='] | ('\\''"') )*('"'|']')
let list_value = [^';']+ ';'

rule next_config = parse
  | ident 
      { let id = lexeme lexbuf in 
        let v = value lexbuf in
        (id,v)
      }
  | _    { next_config lexbuf}
  | eof  { raise End_of_file }

and value = parse
  | value { let s = lexeme lexbuf in
	    String.sub s 1 (String.length s - 2)}
  | _    { value lexbuf }
  | eof  { raise End_of_file }

and split_list = parse
  | list_value {
      let h = lexeme lexbuf in
      h::(split_list lexbuf)
    }
  | _ { split_list lexbuf}
  | eof {[]}

{
  let get_config f = 
    let ci = open_in f in
    let lb = from_channel ci in 
    let result = ref [] in
    begin try 
      while true do 
	let r = next_config lb in
	result := r::!result
      done
    with End_of_file -> close_in ci; 
    end;
    !result

  let split s = 
    let cs = ref "" in
    let l = ref [] in
    String.iter 
      (fun c -> if c = ';' then begin l:= !cs::!l; cs:="" end 
       else cs := !cs^(Char.escaped c))
      s;
    if !cs ="" then !l else !cs::!l
}
