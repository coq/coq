##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""
Use CoqDoc to highlight Coq snippets
====================================

Pygment's Coq parser isn't the best; instead, use coqdoc to highlight snippets.
Only works for full, syntactically valid sentences; on shorter snippets, coqdoc
swallows parts of the input.

Works by reparsing coqdoc's output into the output that Sphinx expects from a
lexer.
"""

import os
import platform
from tempfile import mkstemp
from subprocess import check_output

from bs4 import BeautifulSoup
from bs4.element import NavigableString

COQDOC_OPTIONS = ['--body-only', '--no-glob', '--no-index', '--no-externals',
                  '-s', '--html', '--stdout', '--utf8', '--parse-comments']

COQDOC_SYMBOLS = ["->", "<-", "<->", "=>", "<=", ">=", "<>", "~", "/\\", "\\/", "|-", "*", "forall", "exists"]
COQDOC_HEADER = "".join("(** remove printing {} *)".format(s) for s in COQDOC_SYMBOLS)

def coqdoc(coq_code, coqdoc_bin=None):
    """Get the output of coqdoc on coq_code."""
    coqdoc_bin = coqdoc_bin or os.path.join(os.getenv("COQBIN", ""), "coqdoc")
    fd, filename = mkstemp(prefix="coqdoc_", suffix=".v")
    if platform.system().startswith("CYGWIN"):
        # coqdoc currently doesn't accept cygwin style paths in the form "/cygdrive/c/..."
        filename = check_output(["cygpath", "-w", filename]).decode("utf-8").strip()
    try:
        os.write(fd, COQDOC_HEADER.encode("utf-8"))
        os.write(fd, coq_code.encode("utf-8"))
        os.close(fd)
        return check_output([coqdoc_bin] + COQDOC_OPTIONS + [filename], timeout = 10).decode("utf-8")
    finally:
        os.remove(filename)

def first_string_node(node):
    """Return the first string node, or None if does not exist"""
    while node.children:
        node = next(node.children)
        if isinstance(node, NavigableString):
            return node

def lex(source):
    """Convert source into a stream of (css_classes, token_string)."""
    coqdoc_output = coqdoc(source)
    soup = BeautifulSoup(coqdoc_output, "html.parser")
    root = soup.find(class_='code')
    # strip the leading '\n'
    first = first_string_node(root)
    if first and first.string[0] == '\n':
        first.string.replace_with(first.string[1:])
    for elem in root.children:
        if isinstance(elem, NavigableString):
            yield [], elem
        elif elem.name == "span":
            if elem.string:
                cls = "coqdoc-{}".format(elem.get("title", "comment"))
                yield [cls], elem.string
            else:
                # handle multi-line comments
                children = list(elem.children)
                mlc = children[0].startswith("(*") and children[-1].endswith ("*)")
                for elem2 in children:
                    if isinstance(elem2, NavigableString):
                        cls = ["coqdoc-comment"] if mlc else []
                        yield cls, elem2
                    elif elem2.name == 'br':
                        pass
        elif elem.name == 'br':
            pass
        else:
            raise ValueError(elem)

def main():
    """Lex stdin (for testing purposes)"""
    import sys
    for classes, text in lex(sys.stdin.read()):
        print(repr(text) + "\t" ' '.join(classes))

if __name__ == '__main__':
    main()
