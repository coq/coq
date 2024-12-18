{ stdenv, writeText, coq }:

let META = writeText "META" ''
  archive(native) = "unicoq.cmxa"
  plugin(native) = "unicoq.cmxs"
''; in


stdenv.mkDerivation {
  name = "coq${coq.coq-version}-unicoq-0.0-git";
  src = fetchTarball https://github.com/unicoq/unicoq/archive/master.tar.gz;

  patches = [ ./unicoq-num.patch ];

  buildInputs = [ coq ] ++ (with coq.ocamlPackages; [ ocaml findlib camlp5 num ]);

  configurePhase = "coq_makefile -f Make -o Makefile";
  installFlags = [ "ROCQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

  postInstall = ''
    cp ${META} META
    install -d $OCAMLFIND_DESTDIR
    ln -s $out/lib/coq/${coq.coq-version}/user-contrib/Unicoq $OCAMLFIND_DESTDIR/
    install -m 0644 META src/unicoq.a $OCAMLFIND_DESTDIR/Unicoq
  '';
}
