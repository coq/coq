# Controlling the versions of plugins

The shell scripts in this folder each return (to stdout) the source URL and some extra
information for a specific plugin with a version appropriate for this version of Coq.

This mechanism is only intended for plugins and libraries which need a tight coupling to the version of Coq.

The shell scripts get the Coq version as first argument.
Examples for possible values are:

* git-v8.8.1
* git-master
* 8.5pl3
* 8.8.1
* /cygdrive/<some-folder>

Scripts can simply echo an URL, but more advanced processing is possible.

The output format is the same as the command line to the function build_prep in makecoq_mingw.sh. Here is an example:

```
#!/bin/sh
echo 'https://github.com/ppedrot/ltac2/archive' 'v8.8' 'zip' '1' 'ltac2-v8.8'
```

The arguments are:
* URL path without file name
* file name
* file extension
* number of path levels to strip from archive (optional, default is 1)
* module name, in case the file name just gives a version but no module name

## Handling master versions

In case a master version is returned, the module name should contain the SHA code of the revision downloaded.
Below is an example of how to achieve this (thanks to SkySkimmer):

```
BIGNUMS_SHA=$(git ls-remote 'https://github.com/coq/bignums' refs/heads/master | cut -f 1)

echo https://github.com/coq/bignums/archive "$BIGNUMS_SHA" zip 1 "bignums-$BIGNUMS_SHA"
```
