Testing the output directory of extraction
  $ ls
  a.v

  $ coqc a.v
  File "./a.v", line 2, characters 0-21:
  Warning: Setting extraction output directory by default to
  "$TESTCASE_ROOT".
  Use "Set Extraction Output Directory" to set a different directory for
  extracted files to appear in. [extraction-default-directory,extraction]
Extraction is able to create ouput directories as specified by the user

  $ ls . foo
  .:
  a.glob
  a.v
  a.vo
  a.vok
  a.vos
  bar.ml
  bar.mli
  foo
  
  foo:
  zar.ml
  zar.mli

