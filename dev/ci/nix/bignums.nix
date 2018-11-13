{ ocamlPackages }:

{
  buildInputs = with ocamlPackages; [ ocaml findlib camlp5 ];
}
