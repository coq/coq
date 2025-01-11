{ pkgs ? import ../../nixpkgs.nix {}
, branch
, wd
, project ? "xyz"
, withCoq ? true
, bn ? "master"
}:

with pkgs;

# Rocq from this directory
let coq = callPackage ./coq.nix { inherit branch wd; }; in

# Third-party libraries, built with this Rocq
let coqPackages = mkCoqPackages coq; in
let mathcomp = coqPackages.mathcomp.overrideAttrs (o: {
    name = "coq-git-mathcomp-git";
    src = fetchTarball https://github.com/math-comp/math-comp/archive/master.tar.gz;
  }); in
let ssreflect = coqPackages.ssreflect.overrideAttrs (o: {
  inherit (mathcomp) src;
  }); in

let coq-ext-lib = coqPackages.coq-ext-lib.overrideAttrs (o: {
    src = fetchTarball "https://github.com/coq-community/coq-ext-lib/tarball/master";
  }); in

let simple-io =
  (coqPackages.simple-io.override { inherit coq-ext-lib; })
  .overrideAttrs (o: {
    src = fetchTarball "https://github.com/Lysxia/coq-simple-io/tarball/master";
  }); in

let bignums = coqPackages.bignums.overrideAttrs (o:
    if bn == "release" then {} else
    if bn == "master" then { src = fetchTarball https://github.com/coq/bignums/archive/master.tar.gz; } else
    { src = fetchTarball bn; }
  ); in
let coqprime = coqPackages.coqprime.override { inherit coq bignums; }; in
let math-classes =
  (coqPackages.math-classes.override { inherit coq bignums; })
  .overrideAttrs (o: {
    src = fetchTarball "https://github.com/coq-community/math-classes/archive/master.tar.gz";
  }); in

let corn = (coqPackages.corn.override { inherit coq bignums math-classes; })
  .overrideAttrs (o: {
    src = fetchTarball "https://github.com/coq-community/corn/archive/master.tar.gz";
  }); in

let stdpp = coqPackages.stdpp.overrideAttrs (o: {
    src = fetchTarball "https://gitlab.mpi-sws.org/iris/stdpp/-/archive/master/stdpp-master.tar.bz2";
  }); in

let iris = (coqPackages.iris.override { inherit coq stdpp; })
  .overrideAttrs (o: {
    src = fetchTarball "https://gitlab.mpi-sws.org/iris/iris/-/archive/master/iris-master.tar.bz2";
    propagatedBuildInputs = [ stdpp ];
  }); in

let unicoq = callPackage ./unicoq { inherit coq; }; in

let StructTact = coqPackages.StructTact.overrideAttrs (o: {
    src = fetchTarball "https://github.com/uwplse/StructTact/tarball/master";
  }); in

let Cheerios = (coqPackages.Cheerios.override { inherit StructTact; })
  .overrideAttrs (o: {
    src = fetchTarball "https://github.com/uwplse/cheerios/tarball/master";
  }); in

let Verdi = (coqPackages.Verdi.override { inherit Cheerios ssreflect; })
  .overrideAttrs (o: {
    src = fetchTarball "https://github.com/uwplse/verdi/tarball/master";
  }); in

let flocq = coqPackages.flocq.overrideAttrs (o: {
    src = fetchTarball "https://gitlab.inria.fr/flocq/flocq/-/archive/master/flocq-master.tar.gz";
    configurePhase = ''
      autoreconf
      ${bash}/bin/bash configure --libdir=$out/lib/coq/${coq.coq-version}/user-contrib/Flocq
    '';
    buildPhase = ''
      ./remake
    '';
  }); in

let callPackage = newScope { inherit coq
  bignums coq-ext-lib coqprime corn iris math-classes
  mathcomp simple-io ssreflect stdpp unicoq Verdi flocq;
}; in

# Environments for building CI libraries with this Rocq
let projects = {
  bedrock2 = callPackage ./bedrock2.nix {};
  bignums = callPackage ./bignums.nix {};
  CoLoR = callPackage ./CoLoR.nix {};
  CompCert = callPackage ./CompCert.nix {};
  coq_dpdgraph = callPackage ./coq_dpdgraph.nix {};
  coquelicot = callPackage ./coquelicot.nix {};
  Corn = callPackage ./Corn.nix {};
  cross_crypto = callPackage ./cross_crypto.nix {};
  Elpi = callPackage ./Elpi.nix {};
  fiat_crypto = callPackage ./fiat_crypto.nix {};
  flocq = callPackage ./flocq.nix {};
  formal-topology = callPackage ./formal-topology.nix {};
  HoTT = callPackage ./HoTT.nix {};
  iris = callPackage ./iris.nix {};
  lambda-rust = callPackage ./lambda-rust.nix {};
  math_classes = callPackage ./math_classes.nix {};
  mathcomp = {};
  mtac2 = callPackage ./mtac2.nix {};
  oddorder = callPackage ./oddorder.nix {};
  quickchick = callPackage ./quickchick.nix {};
  simple-io = callPackage ./simple-io.nix {};
  verdi-raft = callPackage ./verdi-raft.nix {};
  VST = callPackage ./VST.nix {};
}; in

if !builtins.hasAttr project projects
then throw "Unknown project “${project}”; choose from: ${pkgs.lib.concatStringsSep ", " (builtins.attrNames projects)}."
else

let prj = projects."${project}"; in

let inherit (stdenv.lib) optional optionals; in

stdenv.mkDerivation {
  name = "shell-for-${project}-in-${branch}";

  buildInputs =
    [ python ]
  ++  optional withCoq coq
  ++ (prj.buildInputs or [])
  ++ optionals withCoq (prj.coqBuildInputs or [])
  ;

  configure = prj.configure or "true";
  make = prj.make or "make";
  clean = prj.clean or "make clean";

}
