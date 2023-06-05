Tests around the resolving of META files.

  $ touch plugin/plugin.cma plugin/plugin.cmxa plugin/plugin.cmxs

1) Explicitly given META file.

  $ coqdep -m plugin/META.plugin -I plugin -Q ./theory theory -dyndep opt theory/file.v
  theory/file.vo theory/file.glob theory/file.v.beautified theory/file.required_vo: theory/file.v plugin/META.plugin plugin/plugin.cmxs
  theory/file.vio: theory/file.v plugin/META.plugin plugin/plugin.cmxs

2) Resolved using ocamlfind (with absolute path, as in dune).

  $ export OCAMLPATH=$PWD/plugin
  $ coqdep -I plugin -Q ./theory theory -dyndep opt theory/file.v
  theory/file.vo theory/file.glob theory/file.v.beautified theory/file.required_vo: theory/file.v plugin/META.plugin plugin/plugin.cmxs
  theory/file.vio: theory/file.v plugin/META.plugin plugin/plugin.cmxs

3) Resolved using ocamlfind (with relative path).

  $ export OCAMLPATH=plugin
  $ coqdep -I plugin -Q ./theory theory -dyndep opt theory/file.v
  theory/file.vo theory/file.glob theory/file.v.beautified theory/file.required_vo: theory/file.v plugin/META.plugin plugin/plugin.cmxs
  theory/file.vio: theory/file.v plugin/META.plugin plugin/plugin.cmxs
