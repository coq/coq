The Coq documentation
=====================

The Coq documentation includes

- A Reference Manual
- A document presenting the Coq standard library

The documentation of the latest released version is available on the Coq
web site at [coq.inria.fr/documentation](http://coq.inria.fr/documentation).

Additionally, you can view the reference manual for the development version
at <https://coq.github.io/doc/master/refman/>, and the documentation of the
standard library for the development version at
<https://coq.github.io/doc/master/stdlib/>.

The reference manual is written is reStructuredText and compiled
using Sphinx. See [`sphinx/README.rst`](sphinx/README.rst)
to learn more about the format that is used.

The documentation for the standard library is generated from
the `.v` source files using coqdoc.

Dependencies
------------

### HTML documentation

To produce the complete documentation in HTML, you will need Coq dependencies
listed in [`INSTALL.md`](../INSTALL.md). Additionally, the Sphinx-based
reference manual requires Python 3, and the following Python packages:

  - sphinx >= 3.0.2
  - sphinx_rtd_theme >= 0.4.3
  - beautifulsoup4 >= 4.0.6
  - antlr4-python3-runtime >= 4.7.1
  - pexpect >= 4.2.1
  - sphinxcontrib-bibtex >= 0.4.2

To install them, you should first install pip and setuptools (for instance,
with `apt install python3-pip python3-setuptools` on Debian / Ubuntu) then run:

    pip3 install sphinx sphinx_rtd_theme beautifulsoup4 \
                 antlr4-python3-runtime==4.7.1 pexpect sphinxcontrib-bibtex

Nix users should get the correct development environment to build the
HTML documentation from Coq's [`default.nix`](../default.nix) (note this
doesn't include the LaTeX packages needed to build the full documentation).

You can check the dependencies using the `doc/tools/coqrst/checkdeps.py` script.

### Other formats

To produce the documentation in PDF and PostScript formats, the following
additional tools are required:

  - latex (latex2e)
  - pdflatex
  - dvips
  - makeindex
  - xelatex
  - latexmk

All of them are part of the TexLive distribution. E.g. on Debian / Ubuntu,
install them with:

    apt install texlive-full

Or if you want to use less disk space:

    apt install texlive-latex-extra texlive-fonts-recommended texlive-xetex \
                latexmk fonts-freefont-otf

### Setting the locale for Python

Make sure that the locale is configured on your platform so that Python encodes
printed messages with utf-8 rather than generating runtime exceptions
for non-ascii characters.  The `.UTF-8` in `export LANG=C.UTF-8` sets UTF-8 encoding.
The `C` can be replaced with any supported language code.  You can set the default
for a Docker build with `ENV LANG C.UTF-8`.  (Python may look at other
environment variables to determine the locale; see the
[Python documentation](https://docs.python.org/3/library/locale.html#locale.getdefaultlocale)).

Compilation
-----------

The current documentation targets are:

- `make refman-html`
  Build the HTML reference manual on `_build/default/doc/refman-html`

- `make refman-pdf`
  Build the PDF reference manual on `_build/default/doc/refman-pdf`

- `make stdlib-html`
  Build the documentation for Coq's standard library `_build/default/doc/stdlib/html`

- `make apidoc`
  Build the documentation for Coq's standard library `_build/default/_doc/_html`

To build the Sphinx documentation without stopping at the first
warning, change the value of the `SPHINXWARNOPT` variable (default is
`-W`). The following will build the Sphinx documentation without
stopping at the first warning, and store all the warnings in the file
`/tmp/warn.log`:

```
SPHINXWARNOPT="-w/tmp/warn.log" make refman-html
```

Installation
------------

The produced documents are stored in the described directories above,
you can install them just by copying the contents to the desired
directory.

In the future, the `coq-doc` and `coq-stdlib` opam packages will
install the documentation automatically.
