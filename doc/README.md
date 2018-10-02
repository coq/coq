The Coq documentation
=====================

The Coq documentation includes

- A Reference Manual
- A document presenting the Coq standard library

The documentation of the latest released version is available on the Coq
web site at [coq.inria.fr/documentation](http://coq.inria.fr/documentation).

Additionally, you can view the documentation for the current master version at
<https://gitlab.com/coq/coq/-/jobs/artifacts/master/file/_install_ci/share/doc/coq/sphinx/html/index.html?job=doc:refman>.

The reference manual is written is reStructuredText and compiled
using Sphinx. See [`sphinx/README.rst`](sphinx/README.rst)
to learn more about the format that is used.

The documentation for the standard library is generated from
the `.v` source files using coqdoc.

Dependencies
------------

### HTML documentation

To produce the complete documentation in HTML, you will need Coq dependencies
listed in [`INSTALL`](../INSTALL). Additionally, the Sphinx-based
reference manual requires Python 3, and the following Python packages:

  - sphinx
  - sphinx_rtd_theme
  - beautifulsoup4
  - antlr4-python3-runtime
  - pexpect
  - sphinxcontrib-bibtex

To install them, you should first install pip and setuptools (for instance,
with `apt install python3-pip python3-setuptools` on Debian / Ubuntu) then run:

    pip3 install sphinx sphinx_rtd_theme beautifulsoup4 antlr4-python3-runtime \
                 pexpect sphinxcontrib-bibtex

Nix users should get the correct development environment to build the
HTML documentation from Coq's [`default.nix`](../default.nix) (note this
doesn't include the LaTeX packages needed to build the full documentation).

### Other formats

To produce the documentation in PDF and PostScript formats, the following
additional tools are required:

  - latex (latex2e)
  - pdflatex
  - dvips
  - makeindex
  - xelatex
  - latexmk
  - xindy

All of them are part of the TexLive distribution. E.g. on Debian / Ubuntu,
install them with:

    apt install texlive-full

Or if you want to use less disk space:

    apt install texlive-latex-extra texlive-fonts-recommended texlive-xetex \
                latexmk xindy

Compilation
-----------

To produce all documentation about Coq in all formats, just run:

    ./configure           # (if you hadn't already)
    make doc


Alternatively, you can use some specific targets:

- `make doc-ps`
  to produce all PostScript documents

- `make doc-pdf`
  to produce all PDF documents

- `make doc-html`
  to produce all HTML documents

- `make refman`
  to produce the HTML and PDF versions of the reference manual

- `make refman-{html,pdf}`
  to produce only one format of the reference manual

- `make stdlib`
  to produce all formats of the Coq standard library


Also note the `-with-doc yes` option of `./configure` to enable the
build of the documentation as part of the default make target.

If you're editing Sphinx documentation, set SPHINXWARNERROR to 0
to avoid treating Sphinx warnings as errors.  Otherwise, Sphinx quits
upon detecting the first warning.  You can set this on the Sphinx `make`
command line or as an environment variable:

- `make refman SPHINXWARNERROR=0`

- ~~~
  export SPHINXWARNERROR=0
    ⋮
  make refman
  ~~~

Installation
------------

To install all produced documents, do:

    make install-doc

This will install the documentation in `/usr/share/doc/coq` unless you
specify another value through the `-docdir` option of `./configure` or the
`DOCDIR` environment variable.
