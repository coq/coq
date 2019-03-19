{ stdenv, callPackage, branch, wd }:

let coq = callPackage wd { buildDoc = false; doInstallCheck = false; coq-version = "8.9"; }; in

coq.overrideAttrs (o: {
  name = "coq-local-${branch}";
  src = fetchGit "${wd}";
})
