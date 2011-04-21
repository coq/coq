(* OCaml-Win32
 * mkwinapp.ml
 * Copyright (c) 2002-2004 by Harry Chomsky
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Library General Public License for more details.
 *
 * You should have received a copy of the GNU Library General Public
 * License along with this library; if not, write to the Free
 * Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *)

(*********************************************************************
 * This program alters an .exe file to make it use the "windows subsystem"
 * instead of the "console subsystem".  In other words, when Windows runs
 * the program, it will not create a console for it.
 *)

(* Pierre Letouzey 23/12/2010 : modification to allow selecting the
   subsystem to use instead of just setting the windows subsystem *)

(* This tool can be run directly via :
   ocaml unix.cma mkwinapp.ml [-set|-unset] <filename>
*)

exception Invalid_file_format

let input_word ic =
    let lo = input_byte ic in
    let hi = input_byte ic in
    (hi lsl 8) + lo

let find_pe_header ic =
    seek_in ic 0x3C;
    let peheader = input_word ic in
    seek_in ic peheader;
    if input_char ic <> 'P' then
        raise Invalid_file_format;
    if input_char ic <> 'E' then
        raise Invalid_file_format;
    peheader

let find_optional_header ic =
    let peheader = find_pe_header ic in
    let coffheader = peheader + 4 in
    seek_in ic (coffheader + 16);
    let optsize = input_word ic in
    if optsize < 96 then
        raise Invalid_file_format;
    let optheader = coffheader + 20 in
    seek_in ic optheader;
    let magic = input_word ic in
    if magic <> 0x010B && magic <> 0x020B then
        raise Invalid_file_format;
    optheader

let change flag ic oc =
    let optheader = find_optional_header ic in
    seek_out oc (optheader + 64);
    for i = 1 to 4 do
        output_byte oc 0
    done;
    output_byte oc (if flag then 2 else 3)

let usage () =
  print_endline "Alters a Win32 executable file to use the Windows subsystem or not.";
  print_endline "Usage: mkwinapp [-set|-unset] <filename>";
  print_endline "Giving no option is equivalent to -set";
  exit 1

let main () =
  let n = Array.length Sys.argv - 1 in
  if not (n = 1 || n = 2) then usage ();
  let flag =
    if n = 1 then true
    else if Sys.argv.(1) = "-set" then true
    else if Sys.argv.(1) = "-unset" then false
    else usage ()
  in
  let filename = Sys.argv.(n) in
  let f = Unix.openfile filename [Unix.O_RDWR] 0 in
  let ic = Unix.in_channel_of_descr f and oc = Unix.out_channel_of_descr f in
  change flag ic oc

let _ = main ()
