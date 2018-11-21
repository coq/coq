{ stdenv, coq }:

stdenv.mkDerivation {
  name = "coq${coq.coq-version}-unicoq-0.0-git";
  src = fetchTarball https://github.com/unicoq/unicoq/archive/master.tar.gz;

  buildInputs = [ coq ] ++ (with coq.ocamlPackages; [ ocaml findlib camlp5 num ]);

  configurePhase = "coq_makefile -f Make -o Makefile";
  installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
}
