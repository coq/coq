{ stdenv, fetchzip, coq }:

stdenv.mkDerivation {
  name = "coq${coq.coq-version}-unicoq-0.0-git";
  src = fetchzip {
    url = "https://github.com/vbgl/unicoq/archive/8b33e37700e92bfd404bf8bf9fe03f1be8928d97.tar.gz";
    sha256 = "0s4z0wjxlp56ccgzxgk04z7skw90rdnz39v730ffkgrjl38rr9il";
  };

  buildInputs = [ coq ] ++ (with coq.ocamlPackages; [ ocaml findlib camlp5 num ]);

  configurePhase = "coq_makefile -f Make -o Makefile";
  installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
}
