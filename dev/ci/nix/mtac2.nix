{ coq, unicoq }:
{
  buildInputs = [ unicoq ] ++ (with coq.ocamlPackages; [ ocaml findlib camlp5 ]);
  configure = "./configure.sh";
}
