Files in this directory are intended to be loaded with the
`-compat-from Stdlib` command line option, in order to provide
compatibility features to mimick some behaviors of older versions. For
instance, this can disable warnings introduced in later versions.

When adding a file in this directory, please name it `StdlibXY.v` and
prepend `From Stdlib Require Export StdlibXY.` to the previous file.
When removing the last remaining content of some file, please also
remove the file altogether.
