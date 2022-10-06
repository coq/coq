{ lib, stdenv, hostname, writeText
, ocamlPackages, dune_3, ocamlformat
, python3, time, glib, wrapGAppsHook, pkg-config
, antlr4, ncurses, rsync, which, jq, curl, gitFull, gnupg, graphviz, gnome
, buildIde ? true
, buildDoc ? true
, doInstallCheck ? true
, shell ? true
, coq-version ? "8.17-git"
, ...
}:

with lib;

stdenv.mkDerivation rec {

  pname = "coq-full";
  version = "dev";

  buildInputs = [
    hostname
    python3
    # coq-makefile timing tools
    time
    dune_3
  ]
  ++ optionals buildIde [
    ocamlPackages.lablgtk3-sourceview3
    glib
    gnome.adwaita-icon-theme
    wrapGAppsHook
  ]
  ++ optionals buildDoc [
    # Sphinx doc dependencies
    pkg-config (python3.withPackages
      (ps: [ ps.sphinx ps.sphinx_rtd_theme ps.pexpect ps.beautifulsoup4
             ps.antlr4-python3-runtime ps.sphinxcontrib-bibtex ]))
    antlr4
    ocamlPackages.odoc
  ]
  ++ optionals doInstallCheck [
    # Test-suite dependencies
    ocamlPackages.ounit
    rsync
    which
  ]
  ++ optionals shell (
    [ # Dependencies of the merging script
      jq
      curl
      gitFull
      gnupg
    ]
    ++ (with ocamlPackages; [
      # Dev tools
      ocaml-lsp
      merlin
      ocp-indent
      ocp-index
      utop
      ocamlformat
      ])
    ++ [
      # Useful for STM debugging
      graphviz
    ]
  );

  # OCaml and findlib are needed so that native_compute works
  # This follows a similar change in the nixpkgs repo (cf. NixOS/nixpkgs#101058)
  # ocamlfind looks for zarith when building plugins
  # This follows a similar change in the nixpkgs repo (cf. NixOS/nixpkgs#94230)
  propagatedBuildInputs = with ocamlPackages; [ ocaml findlib zarith ];
  ocamlBuildInputs = propagatedBuildInputs;

  propagatedUserEnvPkgs = with ocamlPackages; [ ocaml findlib ];

  src = lib.cleanSourceWith {
      filter = name: type:
        ! ( ( type == "directory" ) && ( elem ( baseNameOf name ) ["_build" "_build_ci" ".nix"] ) );
      src = lib.cleanSource ../../..;
  };

  preConfigure = ''
    patchShebangs dev/tools/ doc/stdlib
  '';

  prefixKey = "-prefix ";

  enableParallelBuilding = true;

  buildFlags = [ "world" ];

  # TODO, building of documentation package when not in dev mode
  # https://github.com/coq/coq/issues/16198
  # buildFlags = [ "world" ] ++ optional buildDoc "refman-html";

  # From https://github.com/NixOS/nixpkgs/blob/master/pkgs/build-support/ocaml/dune.nix
  installPhase = ''
    runHook preInstall
    dune install --prefix $out --libdir $OCAMLFIND_DESTDIR coq-core coq-stdlib coq coqide-server coqide
    runHook postInstall
  '';

  # installTargets =
  #   [ "install" ];
    # fixme, do we have to do a target, or can we just do a copy?
    # ++ optional buildDoc "install-doc-html";

  createFindlibDestdir = !shell;

  postInstall = "ln -s $out/lib/coq-core $OCAMLFIND_DESTDIR/coq-core";

  inherit doInstallCheck;

  preInstallCheck = ''
    patchShebangs tools/
    patchShebangs test-suite/
    export OCAMLPATH=$OCAMLFIND_DESTDIR:$OCAMLPATH
  '';

  installCheckTarget = [ "check" ];

  passthru = {
    inherit coq-version ocamlPackages;
    dontFilter = true; # Useful to use mkCoqPackages from <nixpkgs>
  };

  setupHook = writeText "setupHook.sh" "
    addCoqPath () {
      if test -d \"$1/lib/coq/${coq-version}/user-contrib\"; then
        export COQPATH=\"\${COQPATH-}\${COQPATH:+:}$1/lib/coq/${coq-version}/user-contrib/\"
      fi
    }

    addEnvHooks \"$targetOffset\" addCoqPath
  ";

  meta = {
    description = "Coq proof assistant";
    longDescription = ''
      Coq is a formal proof management system.  It provides a formal language
      to write mathematical definitions, executable algorithms and theorems
      together with an environment for semi-interactive development of
      machine-checked proofs.
    '';
    homepage = http://coq.inria.fr;
    license = licenses.lgpl21;
    platforms = platforms.unix;
  };

}
