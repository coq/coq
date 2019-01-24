{ coq, unicoq }:
{
  buildInputs = with coq.ocamlPackages; [ ocaml findlib camlp5 ];
  coqBuildInputs = [ unicoq ];
  configure = "./configure.sh";
}
