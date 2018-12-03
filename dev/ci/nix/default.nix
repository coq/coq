{ pkgs ? import <nixpkgs> {}
, branch
, wd
, project ? "xyz"
, bn ? "master"
}:

with pkgs;

# Coq from this directory
let coq = callPackage ./coq.nix { inherit branch wd; }; in

# Third-party libraries, built with this Coq
let coqPackages = mkCoqPackages coq; in
let mathcomp = coqPackages.mathcomp.overrideAttrs (o: {
    name = "coq-git-mathcomp-git";
    src = fetchTarball https://github.com/math-comp/math-comp/archive/master.tar.gz;
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

let unicoq = callPackage ./unicoq { inherit coq; }; in

let callPackage = newScope { inherit coq mathcomp bignums coqprime corn math-classes unicoq; }; in

# Environments for building CI libraries with this Coq
let projects = {
  bedrock2 = callPackage ./bedrock2.nix {};
  bignums = callPackage ./bignums.nix {};
  CoLoR = callPackage ./CoLoR.nix {};
  CompCert = callPackage ./CompCert.nix {};
  coq_dpdgraph = callPackage ./coq_dpdgraph.nix {};
  Corn = callPackage ./Corn.nix {};
  cross_crypto = callPackage ./cross_crypto.nix {};
  Elpi = callPackage ./Elpi.nix {};
  fiat_crypto = callPackage ./fiat_crypto.nix {};
  fiat_crypto_legacy = callPackage ./fiat_crypto_legacy.nix {};
  flocq = callPackage ./flocq.nix {};
  formal-topology = callPackage ./formal-topology.nix {};
  GeoCoq = callPackage ./GeoCoq.nix {};
  HoTT = callPackage ./HoTT.nix {};
  math_classes = callPackage ./math_classes.nix {};
  mathcomp = {};
  mtac2 = callPackage ./mtac2.nix {};
  oddorder = callPackage ./oddorder.nix {};
  VST = callPackage ./VST.nix {};
}; in

if !builtins.hasAttr project projects
then throw "Unknown project “${project}”; choose from: ${pkgs.lib.concatStringsSep ", " (builtins.attrNames projects)}."
else

let prj = projects."${project}"; in

stdenv.mkDerivation {
  name = "shell-for-${project}-in-${branch}";

  buildInputs = [ coq ] ++ (prj.buildInputs or []);

  configure = prj.configure or "true";
  make = prj.make or "make";
  clean = prj.clean or "make clean";

}
