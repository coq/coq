#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Rebuild sphinx/README.rst from sphinx/README.template.rst."""

import re
from os import sys, path

SCRIPT_DIR = path.dirname(path.abspath(__file__))
if __name__ == "__main__" and __package__ is None:
    sys.path.append(path.dirname(SCRIPT_DIR))

import sphinx
from coqrst import coqdomain

README_ROLES_MARKER = "[ROLES]"
README_OBJECTS_MARKER = "[OBJECTS]"
README_DIRECTIVES_MARKER = "[DIRECTIVES]"

FIRST_LINE_BLANKS = re.compile("^(.*)\n *\n")
def format_docstring(template, obj, *strs):
    docstring = obj.__doc__.strip()
    strs = strs + (FIRST_LINE_BLANKS.sub(r"\1\n", docstring),)
    return template.format(*strs)

SPHINX_DIR = path.join(SCRIPT_DIR, "../../sphinx/")
README_PATH = path.join(SPHINX_DIR, "README.rst")
README_TEMPLATE_PATH = path.join(SPHINX_DIR, "README.template.rst")

def notation_symbol(d):
    return " :black_nib:" if issubclass(d, coqdomain.NotationObject) else ""

def regen_readme():
    objects_docs = [format_docstring("``.. {}::``{} {}", obj, objname, notation_symbol(obj))
                    for objname, obj in sorted(coqdomain.CoqDomain.directives.items())]

    roles = ([(name, cls)
              for name, cls in sorted(coqdomain.CoqDomain.roles.items())
              if not isinstance(cls, (sphinx.roles.XRefRole, coqdomain.IndexXRefRole))] +
             [(fn.role_name, fn)
              for fn in coqdomain.COQ_ADDITIONAL_ROLES])
    roles_docs = [format_docstring("``:{}:`` {}", role, name)
                  for (name, role) in roles]

    directives_docs = [format_docstring("``.. {}::`` {}", d, d.directive_name)
                       for d in coqdomain.COQ_ADDITIONAL_DIRECTIVES]

    with open(README_TEMPLATE_PATH, encoding="utf-8") as readme:
        contents = readme.read()

    with open(README_PATH, mode="w", encoding="utf-8") as readme:
        readme.write(contents
                     .replace(README_ROLES_MARKER, "\n\n".join(roles_docs))
                     .replace(README_OBJECTS_MARKER, "\n\n".join(objects_docs))
                     .replace(README_DIRECTIVES_MARKER, "\n\n".join(directives_docs)))

if __name__ == '__main__':
    regen_readme()
