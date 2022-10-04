{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build, either from nixpkgs
  ## of from the overlays located in `.nix/coq-overlays`
  attribute = "coq";

  ## If you want to select a different attribute
  ## to serve as a basis for nix-shell edit this
  shell-attribute = "coq-full";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "default";

  ## write one `bundles.name` attribute set per
  ## alternative configuration, the can be used to
  ## compute several ci jobs as well
  bundles.default = {

    coqPackages = {
      coqide.override.version = ./..;
      # The list, the order and the branches are taken from
      # dev/ci/ci-basic-overlays.sh
      mathcomp.override.version = "master";
      fourcolor.override.version = "master";
      odd-order.override.version = "master";
      mathcomp-zify.override.version = "master";
      mathcomp-finmap.override.version = "master";
      mathcomp-bigenough.override.version = "master";
      mathcomp-analysis.override.version = "master";
      # UniMath is not in nixpkgs
      unicoq.override.version = "master";
      # Mtac2 is not in nixpkgs
      math-classes.override.version = "master";
      corn.override.version = "master";
      stdpp.override.version = "master";
      iris.override.version = "master";
      autosubst.override.version = "master";
      # iris_example is not in nixpkgs
      # HoTT is not in nixpkgs
      coqhammer.override.version = "master";
      # GeoCoq is not in nixpkgs
      flocq.override.version = "master";
      # coq-performance-tests is not in nixpkgs
      # coq-tools is not in nixpkgs
      coquelicot.override.version = "master";
      CompCert.override.version = "master";
      VST.override.version = "master";
      # cross-crypto is not in nixpkgs
      # rewriter is not in nixpkgs
      # fiat_parsers is not in nixpkgs
      # fiat_crypto is not in nixpkgs
      dpdgraph.override.version = "coq-master";
      CoLoR.override.version = "master";
      tlc.override.version = "master-for-coq-ci";
      bignums.override.version = "master";
      coqprime.override.version = "master";
      # bbv is not in nixpkgs
      # bedrock2 is not in nixpkgs
      equations.override.version = "master";
      coq-elpi.override.version = "coq-master";
      hierarchy-builder.override.version = "coq-master";
      # engine_bench is not in nixpkgs
      # fcsl-pcm is not in nixpkgs
      coq-ext-lib.override.version = "master";
      simple-io.override.version = "master";
      QuickChick.override.version = "master";
      # reduction-effets is not in nixpkgs
      # menhirlib is not in nixpkgs
      aac-tactics.override.version = "master";
      paco.override.version = "master";
      paramcoq.override.version = "master";
      relation-algebra.override.version = "master";
      StructTact.override.version = "master";
      InfSeqExt.override.version = "master";
      Cheerios.override.version = "master";
      Verdi.override.version = "master";
      # verdi_raft is not in nixpkgs
      # stdlib2 is not in nixpkgs
      # argosy is not in nixpkgs
      # perennial is not in nixpkgs
      metacoq.override.version = "master";
      # SF is not in nixpkgs
      # deriving is not in nixpkgs
      category-theory.override.version = "master";
      itauto.override.version = "master";
      mathcomp-word.override.version = "master";
      # lean_importer is not in nixpkgs
    };

    # VsCoq is not in nixpkgs
    # Coqtail and Jasmin are: we could override them if this is worth.

  ## You can override Coq and other Coq coqPackages
  ## through the following attribute
  # coqPackages.coq.override.version = "8.11";

  ## In some cases, light overrides are not available/enough
  ## in which case you can use either
  # coqPackages.<coq-pkg>.overrideAttrs = o: <overrides>;
  ## or a "long" overlay to put in `.nix/coq-overlays
  ## you may use `nix-shell --run fetchOverlay <coq-pkg>`
  ## to automatically retrieve the one from nixpkgs
  ## if it exists and is correctly named/located

  ## You can override Coq and other Coq coqPackages
  ## throught the following attribute
  ## If <ocaml-pkg> does not support lights overrides,
  ## you may use `overrideAttrs` or long overlays
  ## located in `.nix/ocaml-overlays`
  ## (there is no automation for this one)
  #  ocamlPackages.<ocaml-pkg>.override.version = "x.xx";

  ## You can also override packages from the nixpkgs toplevel
  # <nix-pkg>.override.overrideAttrs = o: <overrides>;
  ## Or put an overlay in `.nix/overlays`

  ## you may mark a package as a CI job as follows
  #  coqPackages.<another-pkg>.ci.job = "test";
  ## It can then be built throught
  ## nix-build --argstr ci "default" --arg ci-job "test";

  };

  cachix.coq.authToken = "CACHIX_AUTH_TOKEN";
}
