##########################################################################
##         #      The Rocq Prover / The Rocq Development Team           ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""A Rocq domain for Sphinx.

Currently geared towards Rocq's manual, rather than Rocq source files, but one
could imagine extending it.

Refer to doc/sphinx/README.rst for the documentation of the coqrst domain.
"""

# pylint: disable=missing-type-doc, missing-param-doc
# pylint: disable=missing-return-type-doc, missing-return-doc
# pylint: disable=too-few-public-methods, too-many-ancestors, arguments-differ
# pylint: disable=import-outside-toplevel, abstract-method, too-many-lines

import os
import json
import re
import shlex
from itertools import chain
from dataclasses import dataclass
from collections import defaultdict

from docutils import nodes, utils
from docutils.transforms import Transform
from docutils.parsers.rst import Directive, directives
from docutils.parsers.rst.roles import code_role #, set_classes
from docutils.parsers.rst.directives.admonitions import BaseAdmonition

from sphinx import addnodes, version_info as sphinx_version
from sphinx.application import Sphinx
from sphinx.directives import ObjectDescription
from sphinx.domains import Domain, ObjType, Index
from sphinx.errors import ExtensionError
from sphinx.roles import XRefRole
from sphinx.util.docutils import ReferenceRole
from sphinx.util.logging import getLogger, get_node_location
from sphinx.util.nodes import set_source_info, set_role_source_info, make_refnode
from sphinx.writers.latex import LaTeXTranslator
from sphinx.builders.text import TextBuilder
from sphinx_markdown_builder.translator import MarkdownTranslator, pushing_context
from sphinx_markdown_builder.contexts import WrappedContext

from . import rocqdoc
from .repl import ansicolors
from .repl.rocqtop import RocqTop, RocqTopError
from .notations.parsing import ParseError
from .notations.sphinx import sphinxify
from .notations import object as object_notations
from .notations.plain import stringify_with_ellipses

# FIXME: Patch this in Sphinx
# https://github.com/rocq-prover/rocq/issues/12361
if sphinx_version >= (4, 5):
    from sphinx.writers.latex import CR

    def visit_desc_signature(self, node):
        hyper = ''
        if node.parent['objtype'] != 'describe' and node['ids']:
            for id in node['ids']:
                hyper += self.hypertarget(id)
        self.body.append(hyper)
        if not self.in_desc_signature:
            self.in_desc_signature = True
            self.body.append(CR + r'\pysigstartsignatures')
        if not node.get('is_multiline'):
            self._visit_signature_line(node)
        else:
            self.body.append(CR + r'\pysigstartmultiline')
else:
    def visit_desc_signature(self, node):
        hyper = ''
        if node.parent['objtype'] != 'describe' and node['ids']:
            for id in node['ids']:
                hyper += self.hypertarget(id)
        self.body.append(hyper)
        if not node.get('is_multiline'):
            self._visit_signature_line(node)
        else:
            self.body.append('%\n\\pysigstartmultiline\n')
LaTeXTranslator.visit_desc_signature = visit_desc_signature

PARSE_ERROR = """{}:{} Parse error in notation!
Offending notation: {}
Error message: {}"""

@dataclass
class SubdomainItemData:
    """Data stored for each object in a subdomain"""
    docname: str
    objtype: str
    targetid: str
    syntax: list[object_notations.TaggedNotationObject]

def notation_to_sphinx(notation, source, line, rawtext=None):
    """Parse notation and wrap it in an inline node"""
    try:
        node = nodes.inline(rawtext or notation, '', *sphinxify(notation), classes=['notation'])
        node.source, node.line = source, line
        return node
    except ParseError as e:
        raise ExtensionError(PARSE_ERROR.format(os.path.basename(source), line, notation, e.msg)) from e

def notation_to_string(notation):
    """Parse notation and format it as a string with ellipses."""
    try:
        return stringify_with_ellipses(notation)
    except ParseError as e:
        # FIXME source and line aren't defined below — see cc93f419e0
        raise ExtensionError(PARSE_ERROR.format(os.path.basename(source), line, notation, e.msg)) from e

def highlight_using_rocqdoc(sentence):
    """Lex sentence using rocqdoc, and yield inline nodes for each token"""
    tokens = rocqdoc.lex(utils.unescape(sentence, 1))
    for classes, value in tokens:
        yield nodes.inline(value, value, classes=classes)

def make_target(objtype, targetid):
    """Create a target to an object of type objtype and id targetid"""
    return "rocq:{}.{}".format(objtype, targetid)

def make_math_node(latex, docname, nowrap):
    node = nodes.math_block(latex, latex)
    node['label'] = None # Otherwise equations are numbered
    node['nowrap'] = nowrap
    node['docname'] = docname
    node['number'] = None
    return node

# To support any character in tacn, ... names.
# see https://github.com/rocq-prover/rocq/pull/13564
def make_id(tag):
    return tag.replace(" ", "-")

class RocqObject(ObjectDescription):
    """A generic Rocq object for Sphinx; all Rocq objects are subclasses of this.

    The fields and methods to override are listed at the top of this class'
    implementation.  Each object supports the :name: option, which gives an
    explicit name to link to.

    See the comments and docstrings in RocqObject for more information.
    """

    # The semantic domain in which this object lives (eg. “tac”, “cmd”, “chm”…).
    # It matches exactly one of the roles used for cross-referencing.
    subdomain = None # type: str

    # The suffix to use in indices for objects of this type (eg. “(tac)”)
    index_suffix = None # type: str

    # The annotation to add to headers of objects of this type
    # (eg. “Command”, “Theorem”)
    annotation = None # type: str

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._sig_names = None

    def _name_from_signature(self, signature, signode): # pylint: disable=no-self-use, unused-argument
        """Convert a signature into a name to link to.

        ‘Signature’ is Sphinx parlance for an object's header (think “type
        signature”); for example, the signature of the simplest form of the
        ``exact`` tactic is ``exact @id``.

        Generates a name for the directive.  Override this method to return None
        to avoid generating a name automatically.  This is a convenient way
        to automatically generate names (link targets) without having to write
        explicit names everywhere.

        """
        m = re.match(r"[a-zA-Z0-9_ ]+", signature)
        if m:
            return m.group(0).strip()

    def _render_signature(self, signature, signode):
        """Render a signature, placing resulting nodes into signode."""
        raise NotImplementedError(self)

    def _signature_to_syntax(self, signature: str) -> list[object_notations.TaggedNotationObject]:
        """Convert a signature into a syntax tree, used in generated plain JSON indices.

        By default, returns the signature as a literal string.

        """
        return [object_notations.Literal.new(object_notations.Literal(value=signature, subscript=None))]

    option_spec = {
        # Explicit object naming
        'name': directives.unchanged,
        # Silence warnings produced by report_undocumented_rocq_objects
        'undocumented': directives.flag,
        # noindex omits this object from its index
        'noindex': directives.flag
    }

    def subdomain_data(self) -> dict[str, SubdomainItemData]:
        if self.subdomain is None:
            raise ValueError()
        return self.env.domaindata['rocq']['objects'][self.subdomain]

    def _render_annotation(self, signode):
        if self.annotation:
            annot_node = nodes.inline(self.annotation, self.annotation, classes=['sigannot'])
            signode += addnodes.desc_annotation(self.annotation, '', annot_node)
            signode += nodes.Text(' ')

    def handle_signature(self, signature, signode):
        """Prefix signature with the proper annotation, then render it using
        ``_render_signature`` (for example, add “Command” in front of commands).

        :returns: the names given to the resulting node.
        """
        self._render_annotation(signode)
        self._render_signature(signature, signode)
        names = self._sig_names.get(signature)
        if names is None:
            name = self._name_from_signature(signature, signode) # pylint: disable=assignment-from-none
            # remove trailing ‘.’ found in commands, but not ‘...’ (ellipsis)
            if name is not None and name.endswith(".") and not name.endswith("..."):
                name = name[:-1]
            names = [name] if name else None
        return names

    def _warn_if_duplicate_name(self, objects: dict[str, SubdomainItemData], name: str, signode):
        """Check that two objects in the same domain don't have the same name."""
        if name in objects:
            MSG = 'Duplicate name {} (other is in {}) attached to {}'
            msg = MSG.format(name, self.env.doc2path(objects[name].docname), signode)
            self.state_machine.reporter.warning(msg, line=self.lineno)

    def _record_name(self, name, target_id, signature: str, signode):
        """Record a `name` in the current subdomain, mapping it to `target_id`.

        Warns if another object of the same name already exists; `signode` is
        used in the warning.
        """
        names_in_subdomain = self.subdomain_data()
        self._warn_if_duplicate_name(names_in_subdomain, name, signode)
        names_in_subdomain[name] = SubdomainItemData(self.env.docname, self.objtype, target_id, self._signature_to_syntax(signature))

    def _target_id(self, name):
        return make_target(self.objtype, make_id(name))

    def _add_target(self, signature: str, signode, name):
        """Register a link target ‘name’, pointing to signode."""
        targetid = self._target_id(name)
        if targetid not in self.state.document.ids:
            signode['ids'].append(targetid)
            signode['names'].append(name)
            signode['first'] = (not self.names)
            self._record_name(name, targetid, signature, signode)
        else:
            # We don't warn for duplicates in the SSReflect chapter, because
            # it's the style of this chapter to repeat all the defined
            # objects at the end.
            if self.env.docname != 'proof-engine/ssreflect-proof-language':
                self._warn_if_duplicate_name(self.subdomain_data(), name, signode)
        return targetid

    def _add_index_entry(self, name, target):
        """Add `name` (pointing to `target`) to the main index."""
        assert isinstance(name, str)
        # remove trailing . , found in commands, but not ... (ellipsis)
        trim = name.endswith(".") and not name.endswith("...")
        index_text = name[:-1] if trim else name
        if self.index_suffix:
            index_text += " " + self.index_suffix
        self.indexnode['entries'].append(('single', index_text, target, '', None))

    def add_target_and_index(self, names, signature: str, signode):
        """Attach a link target to `signode` and index entries for `names`.
        This is only called (from ``ObjectDescription.run``) if ``:noindex:`` isn't specified."""
        if names:
            for name in names:
                if isinstance(name, str) and name.startswith('_'):
                    continue
                target = self._add_target(signature, signode, name)
                self._add_index_entry(name, target)
            self.state.document.note_explicit_target(signode)

    def _prepare_names(self):
        """Construct ``self._sig_names``, a map from signatures to names.

        A node may have either one signature with no name, multiple signatures
        with one name per signatures, or one signature with multiple names.
        """
        sigs = self.get_signatures()
        names = self.options.get("name")
        if names is None:
            self._sig_names = {}
        else:
            names = [n.strip() for n in names.split(";")]
            if len(names) != len(sigs):
                if len(sigs) != 1: #Multiple names for one signature
                    ERR = ("Expected {} semicolon-separated names, got {}.  " +
                           "Please provide one name per signature line.")
                    raise self.error(ERR.format(len(names), len(sigs)))
                self._sig_names = { sigs[0]: names }
            else:
                self._sig_names = { sig: [name] for (sig, name) in zip(sigs, names) }

    def run(self):
        self._prepare_names()
        return super().run()

class DocumentableObject(RocqObject):

    def _warn_if_undocumented(self):
        document = self.state.document
        config = document.settings.env.config
        report = config.report_undocumented_rocq_objects
        if report and not self.content and "undocumented" not in self.options:
            # This is annoyingly convoluted, but we don't want to raise warnings
            # or interrupt the generation of the current node.  For more details
            # see https://github.com/sphinx-doc/sphinx/issues/4976.
            msg = 'No contents in directive {}'.format(self.name)
            node = document.reporter.info(msg, line=self.lineno)
            getLogger(__name__).info(node.astext())
            if report == "warning":
                raise self.warning(msg)

    def run(self):
        self._warn_if_undocumented()
        return super().run()

class PlainObject(DocumentableObject):
    """A base class for objects whose signatures should be rendered literally."""
    def _render_signature(self, signature, signode):
        signode += addnodes.desc_name(signature, signature)

class NotationObject(DocumentableObject):
    """A base class for objects whose signatures should be rendered as nested boxes.

    Objects that inherit from this class can use the notation grammar (“{+ …}”,
    “@…”, etc.) in their signature.
    """
    def _signature_to_syntax(self, signature: str) -> list[object_notations.TaggedNotationObject]:
        return object_notations.objectify(signature)

    def _render_signature(self, signature, signode):
        position = self.state_machine.get_source_and_line(self.lineno)
        tacn_node = notation_to_sphinx(signature, *position)
        signode += addnodes.desc_name(signature, '', tacn_node)

class GallinaObject(PlainObject):
    """ A Theorem object.
    See the documentation of the ".. thm::" object in doc/sphinx/README.rst.
    """
    subdomain = "thm"
    index_suffix = "(theorem)"
    annotation = "Theorem"

class VernacObject(NotationObject):
    """A Rocq command object.
    See the documentation of the ".. cmd::" object in doc/sphinx/README.rst.
    """
    subdomain = "cmd"
    index_suffix = "(command)"
    annotation = "Command"

    def _name_from_signature(self, signature, signode):
        m = re.match(r"[a-zA-Z0-9_ ]+", signature)
        return m.group(0).strip() if m else None

class VernacVariantObject(VernacObject):
    """An object for a variant of a Rocq command.
    See the documentation of the ".. cmdv::" object in doc/sphinx/README.rst.
    """
    index_suffix = "(command variant)"
    annotation = "Variant"

    def _name_from_signature(self, signature, signode):
        return None

class TacticObject(NotationObject):
    """An object for a tactic, or a tactic notation.
    See the documentation of the ".. tacn::" object in doc/sphinx/README.rst.
    """
    subdomain = "tacn"
    index_suffix = "(tactic)"
    annotation = "Tactic"

class AttributeObject(NotationObject):
    """An attribute object.
    See the documentation of the ".. attr::" object in doc/sphinx/README.rst.
    """
    subdomain = "attr"
    index_suffix = "(attribute)"
    annotation = "Attribute"

    def _name_from_signature(self, signature, signode):
        return notation_to_string(signature)

class TacticVariantObject(TacticObject):
    """An object for a variant of a tactic.
    See the documentation of the ".. tacv::" object in doc/sphinx/README.rst.
    """
    index_suffix = "(tactic variant)"
    annotation = "Variant"

    def _name_from_signature(self, signature, signode):
        return None

class OptionObject(NotationObject):
    """An object for a Rocq option (a setting with non-boolean value, e.g. a
    string or numeric value).
    See the documentation of the ".. opt::" object in doc/sphinx/README.rst.
    """
    subdomain = "opt"
    index_suffix = "(option)"
    annotation = "Option"

class FlagObject(NotationObject):
    """An object for a Rocq flag (i.e. a boolean setting).
    See the documentation of the ".. flag::" object in doc/sphinx/README.rst.
    """
    subdomain = "flag"
    index_suffix = "(flag)"
    annotation = "Flag"

class TableObject(NotationObject):
    """An object for a Rocq table, i.e. a setting that is a set of values.
    See the documentation of the ".. table::" object in doc/sphinx/README.rst.
    """
    subdomain = "table"
    index_suffix = "(table)"
    annotation = "Table"

class ProductionObject(RocqObject):
    """A grammar production.
    See the documentation of the ".. prodn::" object in doc/sphinx/README.rst.
    """
    subdomain = "prodn"
    #annotation = "Grammar production"

    # handle_signature is called for each line of input in the prodn::
    # 'signatures' accumulates them in order to combine the lines into a single table:
    signatures = None # FIXME this should be in init, shouldn't it?

    def _render_signature(self, signature, signode):
        raise NotImplementedError(self)

    SIG_ERROR = ("{}: Invalid syntax in ``.. prodn::`` directive"
                 + "\nExpected ``name ::= ...`` or ``name += ...``"
                 + " (e.g. ``pattern += constr:(@ident)``)\n"
                 + "  in `{}`")

    def handle_signature(self, signature, signode):
        parts = signature.split(maxsplit=1)
        if parts[0].strip() == "|" and len(parts) == 2:
            lhs = ""
            op = "|"
            rhs = parts[1].strip()
        else:
            parts = signature.split(maxsplit=2)
            if len(parts) != 3:
                loc = os.path.basename(get_node_location(signode))
                raise ExtensionError(ProductionObject.SIG_ERROR.format(loc, signature))
            lhs, op, rhs = (part.strip() for part in parts)
            if op not in ["::=", "+="]:
                loc = os.path.basename(get_node_location(signode))
                raise ExtensionError(ProductionObject.SIG_ERROR.format(loc, signature))

        parts = rhs.split("   ", maxsplit=1)
        rhs = parts[0].strip()
        tag = parts[1].strip() if len(parts) == 2 else ""

        self.signatures.append((lhs, op, rhs, tag))
        return [('token', lhs)] if op == '::=' else None

    def _add_index_entry(self, name, target):
        pass

    def _target_id(self, name):
        return make_id('grammar-token-{}'.format(name[1]))

    def _record_name(self, name, targetid, signature, signode):
        env = self.state.document.settings.env
        objects = env.domaindata['std']['objects']
        self._warn_if_duplicate_name(objects, name, signode)
        objects[name] = env.docname, targetid

    def run(self):
        self.signatures = []
        indexnode = super().run()[0]  # makes calls to handle_signature

        table = nodes.inline(classes=['prodn-table'])
        tgroup = nodes.inline(classes=['prodn-column-group'])
        for _ in range(4):
            tgroup += nodes.inline(classes=['prodn-column'])
        table += tgroup
        tbody = nodes.inline(classes=['prodn-row-group'])
        table += tbody

        # create rows
        for signature in self.signatures:
            lhs, op, rhs, tag = signature
            position = self.state_machine.get_source_and_line(self.lineno)

            row = nodes.inline(classes=['prodn-row'])
            entry = nodes.inline(classes=['prodn-cell-nonterminal'])
            if lhs != "":
                target_name = make_id('grammar-token-' + lhs)
                target = nodes.target('', '', ids=[target_name], names=[target_name])
                # putting prodn-target on the target node won't appear in the tex file
                inline = nodes.inline(classes=['prodn-target'])
                inline += target
                entry += inline
                entry += notation_to_sphinx('@'+lhs, *position)
            else:
                entry += nodes.literal('', '')
            row += entry

            entry = nodes.inline(classes=['prodn-cell-op'])
            entry += nodes.literal(op, op)
            row += entry

            entry = nodes.inline(classes=['prodn-cell-production'])
            entry += notation_to_sphinx(rhs, *position)
            row += entry

            entry = nodes.inline(classes=['prodn-cell-tag'])
            entry += nodes.literal(tag, tag)
            row += entry

            tbody += row

        return [indexnode, table] # only this node goes into the doc

class ExceptionObject(NotationObject):
    """An object for an error raised by a Rocq command or tactic.
    See the documentation of the ".. exn::" object in doc/sphinx/README.rst.
    """
    subdomain = "exn"
    index_suffix = "(error)"
    annotation = "Error"
    # Uses “exn” since “err” already is a CSS class added by “writer_aux”.

    # Generate names automatically
    def _name_from_signature(self, signature, signode):
        return notation_to_string(signature)

class WarningObject(NotationObject):
    """An object for a warning raised by a Rocq command or tactic..
    See the documentation of the ".. warn::" object in doc/sphinx/README.rst.
    """
    subdomain = "warn"
    index_suffix = "(warning)"
    annotation = "Warning"

    # Generate names automatically
    def _name_from_signature(self, signature, signode):
        loc = get_node_location(signode)
        raise ExtensionError("{}: Missing name for warning '{}'".format(loc, signature))

def NotationRole(role, rawtext, text, lineno, inliner, options={}, content=[]):
    #pylint: disable=unused-argument, dangerous-default-value
    """A role for any text using the notation syntax (``@id``, ``{+, …}``, etc.).
    See the documentation of the ":n:" role in doc/sphinx/README.rst.
    """
    notation = utils.unescape(text, 1)
    position = inliner.reporter.get_source_and_line(lineno)
    return [nodes.literal(rawtext, '', notation_to_sphinx(notation, *position, rawtext=rawtext))], []

def rocq_code_role(role, rawtext, text, lineno, inliner, options={}, content=[]):
    #pylint: disable=dangerous-default-value
    """A Rocq code role for Gallina and Ltac snippets.
    See the documentation of the ":g:" role in doc/sphinx/README.rst.
    """
    options['language'] = 'Coq'
    return code_role(role, rawtext, text, lineno, inliner, options, content)
    ## Too heavy:
    ## Forked from code_role to use our custom tokenizer; this doesn't work for
    ## snippets though: for example RocqDoc swallows the parentheses around this:
    ## “(a: A) (b: B)”
    # set_classes(options)
    # classes = ['code', 'rocq']
    # code = utils.unescape(text, 1)
    # node = nodes.literal(rawtext, '', *highlight_using_rocqdoc(code), classes=classes)
    # return [node], []

RocqCodeRole = rocq_code_role

class RocqtopDirective(Directive):
    """A reST directive to describe interactions with Rocq Top.
    See the documentation of the ".. rocqtop::" directive in doc/sphinx/README.rst.
    """
    has_content = True
    required_arguments = 1
    optional_arguments = 0
    final_argument_whitespace = True
    option_spec = { 'name': directives.unchanged }
    directive_name = "rocqtop"

    def run(self):
        # Uses a ‘container’ instead of a ‘literal_block’ to disable
        # Pygments-based post-processing (we could also set rawsource to '')
        content = '\n'.join(self.content)
        args = self.arguments[0].split()
        node = nodes.container(content, rocqtop_options = set(args),
                               classes=['rocqtop', 'literal-block'])
        self.add_name(node)
        return [node]

class RocqdocDirective(Directive):
    """A reST directive to display Rocq Doc-formatted source code.
    See the documentation of the ".. rocqdoc::" directive in doc/sphinx/README.rst.
    """
    # TODO implement this as a Pygments highlighter?
    has_content = True
    required_arguments = 0
    optional_arguments = 0
    final_argument_whitespace = True
    option_spec = { 'name': directives.unchanged }
    directive_name = "rocqdoc"

    def run(self):
        # Uses a ‘container’ instead of a ‘literal_block’ to disable
        # Pygments-based post-processing (we could also set rawsource to '')
        content = '\n'.join(self.content)
        node = nodes.inline(content, '', *highlight_using_rocqdoc(content))
        wrapper = nodes.container(content, node, classes=['rocqdoc', 'literal-block'])
        self.add_name(wrapper)
        return [wrapper]

class ExampleDirective(BaseAdmonition):
    """A reST directive for examples.
    See the documentation of the ".. example::" directive in doc/sphinx/README.rst.
    """
    node_class = nodes.admonition
    directive_name = "example"
    optional_arguments = 1

    def run(self):
        # ‘BaseAdmonition’ checks whether ‘node_class’ is ‘nodes.admonition’,
        # and uses arguments[0] as the title in that case (in other cases, the
        # title is unset, and it is instead set in the HTML visitor).
        assert len(self.arguments) <= 1
        self.arguments = [": ".join(['Example'] + self.arguments)]
        self.options['classes'] = ['admonition', 'note']
        return super().run()

class PreambleDirective(Directive):
    """A reST directive to include a TeX file.
    See the documentation of the ".. preamble::" directive in doc/sphinx/README.rst
    """
    has_content = False
    required_arguments = 1
    optional_arguments = 0
    final_argument_whitespace = True
    option_spec = {}
    directive_name = "preamble"

    def run(self):
        document = self.state.document
        env = document.settings.env

        if not document.settings.file_insertion_enabled:
            msg = 'File insertion disabled'
            return [document.reporter.warning(msg, line=self.lineno)]

        rel_fname, abs_fname = env.relfn2path(self.arguments[0])
        env.note_dependency(rel_fname)

        with open(abs_fname, encoding="utf-8") as ltx:
            latex = ltx.read()

        node = make_math_node(latex, env.docname, nowrap=False)
        node['classes'] = ["math-preamble"]
        set_source_info(self, node)
        return [node]

class InferenceDirective(Directive):
    """A reST directive to format inference rules.
    See the documentation of the ".. inference::" directive in doc/sphinx/README.rst
    """
    required_arguments = 1
    optional_arguments = 0
    has_content = True
    final_argument_whitespace = True
    directive_name = "inference"

    @staticmethod
    def prepare_latex_operand(op):
        # TODO: Could use a fancier inference class in LaTeX
        return '%\n\\hspace{3em}%\n'.join(op.strip().splitlines())

    def prepare_latex(self, content):
        parts = re.split('^ *----+ *$', content, flags=re.MULTILINE)
        if len(parts) != 2:
            raise self.error('Expected two parts in ‘inference’ directive, separated by a rule (----).')

        top, bottom = tuple(InferenceDirective.prepare_latex_operand(p) for p in parts)
        return "%\n".join(("\\frac{", top, "}{", bottom, "}"))

    def run(self):
        self.assert_has_content()

        title = self.arguments[0]
        content = '\n'.join(self.content)
        latex = self.prepare_latex(content)
        docname = self.state.document.settings.env.docname
        math_node = make_math_node(latex, docname, nowrap=False)

        tid = make_id(title)
        target = nodes.target('', '', ids=['inference-' + tid])
        self.state.document.note_explicit_target(target)

        term, desc = nodes.term('', title), nodes.description('', math_node)
        dli = nodes.definition_list_item('', term, desc)
        dl = nodes.definition_list(content, target, dli)
        set_source_info(self, dl)
        return [dl]

class AnsiColorsParser():
    """Parse ANSI-colored output from Rocqtop into Sphinx nodes."""

    # Rocqtop's output crashes ansi.py, because it contains a bunch of extended codes
    # This class is a fork of the original ansi.py, released under a BSD license in sphinx-contribs

    COLOR_PATTERN = re.compile('\x1b\\[([^m]+)m')

    def __init__(self):
        self.new_nodes, self.pending_nodes = [], []

    def _finalize_pending_nodes(self):
        self.new_nodes.extend(self.pending_nodes)
        self.pending_nodes = []

    def _add_text(self, raw, beg, end):
        if beg < end:
            text = raw[beg:end]
            if self.pending_nodes:
                self.pending_nodes[-1].append(nodes.Text(text))
            else:
                self.new_nodes.append(nodes.inline('', text))

    def colorize_str(self, raw):
        """Parse raw (an ANSI-colored output string from Rocqtop) into Sphinx nodes."""
        last_end = 0
        for match in AnsiColorsParser.COLOR_PATTERN.finditer(raw):
            self._add_text(raw, last_end, match.start())
            last_end = match.end()
            classes = ansicolors.parse_ansi(match.group(1))
            if 'ansi-reset' in classes:
                self._finalize_pending_nodes()
            else:
                node = nodes.inline()
                self.pending_nodes.append(node)
                node['classes'].extend(classes)
        self._add_text(raw, last_end, len(raw))
        self._finalize_pending_nodes()
        return self.new_nodes

class RocqtopBlocksTransform(Transform):
    """Filter handling the actual work for the rocqtop directive

    Adds rocqtop's responses, colorizes input and output, and merges consecutive
    rocqtop directives for better visual rendition.
    """
    default_priority = 10

    @staticmethod
    def is_rocqtop_block(node):
        return isinstance(node, nodes.Element) and 'rocqtop_options' in node

    @staticmethod
    def is_rocqtop_args_field(node):
        return isinstance(node, nodes.field) and node.children[0].rawsource == 'ROCQTOP_ARGS'

    @staticmethod
    def split_lines(source):
        r"""Split Rocq input into chunks, which may include single- or
        multi-line comments.  Nested comments are not supported.

        A chunk is a minimal sequence of consecutive lines of the input that
        ends with a '.' or a focusing brace, possibly followed by blanks and/or comments.

        >>> split_lines('A.\nB.''')
        ['A.\n', 'B.']

        >>> split_lines('A.\n\nB.''')
        ['A.\n', '\nB.']

        >>> split_lines('A.\n\nB.\n''')
        ['A.\n', '\nB.']

        >>> split_lines("SearchPattern (_ + _ = _ + _).\n"
        ...             "SearchPattern (nat -> bool).\n"
        ...             "SearchPattern (forall l : list _, _ l l).")
        ... # doctest: +NORMALIZE_WHITESPACE
        ['SearchPattern (_ + _ = _ + _).\n',
         'SearchPattern (nat -> bool).\n',
         'SearchPattern (forall l : list _, _ l l).']

        >>> split_lines('SearchHead le.\nSearchHead (@eq bool).')
        ['SearchHead le.\n', 'SearchHead (@eq bool).']

        >>> split_lines("(* *) x. (* *)\ny.\n")
        ['(* *) x. (* *)\n', 'y.']

        >>> split_lines("(* *) x (* \n *)\ny.\n")
        ['(* *) x (* \n *)\ny.']

        >>> split_lines("Check (* check *) list (* comment *)\n"
        ...             "nat. (* another *) (*and another *)"))
        ['Check (* check *) list (* comment *)\nnat. (* another *) (*and another *)']
        """
        comment = r"\(\*.*\*\)"
        # the end of a chunk is marked by
        # a period (\.) or a focusing brace (:\s*\{)
        # optional blanks or comments (?:[ \t]*|{comment})*
        # followed by a newline \n
        # We capture everything starting from the '.' to recover it afterwards
        blank = r"[ \t]"
        dot = r"\."
        focusing_brace = r":\s*\{"
        end_of_chunk = fr"((?:{dot}|{focusing_brace})(?:{blank}*|{comment})*\n)"
        splits = re.split(end_of_chunk, source.strip())
        return [''.join(splits[i:i+2]) for i in range(0, len(splits), 2)]

    @staticmethod
    def parse_options(node):
        """Parse options according to the description in RocqtopDirective."""

        options = node['rocqtop_options']

        # Behavior options
        opt_reset = 'reset' in options
        opt_fail = 'fail' in options
        opt_warn = 'warn' in options
        opt_restart = 'restart' in options
        opt_abort = 'abort' in options
        opt_extra = set([opt for opt in options if opt.startswith('extra-')])
        options = options - {'reset', 'fail', 'warn', 'restart', 'abort'}
        options = set([opt for opt in options if not (opt.startswith('extra-'))])

        unexpected_options = list(options - {'all', 'none', 'in', 'out'})
        if unexpected_options:
            loc = os.path.basename(get_node_location(node))
            raise ExtensionError("{}: Unexpected options for .. rocqtop:: {}".format(loc,unexpected_options))

        # Display options
        if len(options) != 1:
            loc = os.path.basename(get_node_location(node))
            raise ExtensionError("{}: Exactly one display option must be passed to .. rocqtop::".format(loc))

        opt_all = 'all' in options
        opt_input = 'in' in options
        opt_output = 'out' in options

        # if 'extra' is given and not a subset of env variable 'ROCQRST_EXTRA',
        # allow errors
        env_extra = os.environ.get('ROCQRST_EXTRA', '')
        opt_fail = opt_fail or (env_extra != 'all' and len(opt_extra - set(env_extra.split(','))) != 0)
        return {
            'reset': opt_reset,
            'fail': opt_fail,
            # if errors are allowed, then warnings too
            # and they should be displayed as warnings, not errors
            'warn': opt_warn or opt_fail,
            'restart': opt_restart,
            'abort': opt_abort,
            'input': opt_input or opt_all,
            'output': opt_output or opt_all
        }

    @staticmethod
    def block_classes(should_show, contents=None):
        """Compute classes to add to a node containing contents.

        :param should_show: Whether this node should be displayed"""
        is_empty = contents is not None and re.match(r"^\s*$", contents)
        return ['rocqtop-hidden'] if is_empty or not should_show else []

    @staticmethod
    def make_rawsource(pairs, opt_input, opt_output):
        blocks = []
        for sentence, output in pairs:
            output = AnsiColorsParser.COLOR_PATTERN.sub("", output).strip()
            if opt_input:
                blocks.append(sentence)
            if output and opt_output:
                blocks.append(re.sub("^", "    ", output, flags=re.MULTILINE) + "\n")
        return '\n'.join(blocks)

    def add_rocq_output_1(self, repl, node):
        options = self.parse_options(node)

        pairs = []

        if options['restart']:
            repl.sendone('Restart.')
            repl.sendone('Proof.')
        if options['reset']:
            repl.sendone('Reset Initial.')
            repl.send_initial_options()
        if options['fail']:
            repl.sendone('Unset Rocqtop Exit On Error.')
        if options['warn']:
            repl.sendone('Set Warnings "default".')
        for sentence in self.split_lines(node.rawsource):
            comment = re.compile(r"\s*\(\*.*?\*\)\s*", re.DOTALL)
            wo_comments = re.sub(comment, "", sentence)
            has_tac = wo_comments != "" and not wo_comments.isspace()
            output = repl.sendone(sentence) if has_tac else ""
            pairs.append((sentence, output))
        if options['abort']:
            repl.sendone('Abort All.')
        if options['fail']:
            repl.sendone('Set Rocqtop Exit On Error.')
        if options['warn']:
            repl.sendone('Set Warnings "+default".')

        dli = nodes.definition_list_item()
        for sentence, output in pairs:
            # Use Rocqdoc to highlight input
            in_chunks = highlight_using_rocqdoc(sentence)
            dli += nodes.term(sentence, '', *in_chunks, classes=self.block_classes(options['input']))
            if output:
                # Parse ANSI sequences to highlight output
                out_chunks = AnsiColorsParser().colorize_str(output)
                dli += nodes.definition(output, *out_chunks, classes=self.block_classes(options['output'], output))
        node.clear()
        node.rawsource = self.make_rawsource(pairs, options['input'], options['output'])
        node['classes'].extend(self.block_classes(options['input'] or options['output']))
        node += nodes.inline('', '', classes=['rocqtop-reset'] * options['reset'])
        node += nodes.definition_list(node.rawsource, dli)

    def add_rocqtop_output(self):
        """Add rocqtop's responses to a Sphinx AST

        Finds nodes to process using is_rocqtop_block."""
        arg_fields = self.document.traverse(RocqtopBlocksTransform.is_rocqtop_args_field)
        additional_args = [arg for field in arg_fields for arg in shlex.split(field.children[1].rawsource)]
        with RocqTop(color=True, args=additional_args) as repl:
            repl.send_initial_options()
            for node in self.document.traverse(RocqtopBlocksTransform.is_rocqtop_block):
                try:
                    self.add_rocq_output_1(repl, node)
                except RocqTopError as err:
                    import textwrap
                    MSG = ("{}: Error while sending the following to rocqtop:\n{}" +
                           "\n  rocqtop output:\n{}" +
                           "\n  Full error text:\n{}")
                    indent = "    "
                    loc = get_node_location(node)
                    le = textwrap.indent(str(err.last_sentence), indent)
                    bef = textwrap.indent(str(err.before), indent)
                    fe = textwrap.indent(str(err.err), indent)
                    raise ExtensionError(MSG.format(loc, le, bef, fe))

    @staticmethod
    def merge_rocqtop_classes(kept_node, discarded_node):
        discarded_classes = discarded_node['classes']
        if not 'rocqtop-hidden' in discarded_classes:
            kept_node['classes'] = [c for c in kept_node['classes']
                                    if c != 'rocqtop-hidden']

    @staticmethod
    def merge_consecutive_rocqtop_blocks(_app, doctree, _):
        """Merge consecutive divs wrapping lists of Rocq sentences; keep ‘dl’s separate."""
        for node in doctree.traverse(RocqtopBlocksTransform.is_rocqtop_block):
            if node.parent:
                rawsources, names = [node.rawsource], set(node['names'])
                for sibling in node.traverse(include_self=False, descend=False,
                                             siblings=True, ascend=False):
                    if RocqtopBlocksTransform.is_rocqtop_block(sibling):
                        RocqtopBlocksTransform.merge_rocqtop_classes(node, sibling)
                        rawsources.append(sibling.rawsource)
                        names.update(sibling['names'])
                        node.extend(sibling.children)
                        node.parent.remove(sibling)
                        sibling.parent = None
                    else:
                        break
                node.rawsource = "\n\n".join(rawsources)
                node['names'] = list(names)

    def apply(self):
        self.add_rocqtop_output()

class RocqSubdomainsIndex(Index):
    """Index subclass to provide subdomain-specific indices.

    Just as in the original manual, we want to have separate indices for each
    Rocq subdomain (tactics, commands, options, etc)"""

    name, localname, shortname, subdomains = None, None, None, [] # Must be overwritten

    def generate(self, docnames=None):
        content = defaultdict(list)
        items = chain(*(self.domain.data['objects'][subdomain].items()
                        for subdomain in self.subdomains))

        for itemname, data in sorted(items, key=lambda x: x[0].lower()):
            if docnames and data.docname not in docnames:
                continue

            entries = content[itemname[0].lower()]
            entries.append([itemname, 0, data.docname, data.targetid, '', '', ''])

        collapse = False
        content = sorted(content.items())
        return content, collapse

class RocqVernacIndex(RocqSubdomainsIndex):
    name, localname, shortname, subdomains = "cmdindex", "Command Index", "commands", ["cmd"]

class RocqTacticIndex(RocqSubdomainsIndex):
    name, localname, shortname, subdomains = "tacindex", "Tactic Index", "tactics", ["tacn"]

class RocqAttributeIndex(RocqSubdomainsIndex):
    name, localname, shortname, subdomains = "attrindex", "Attribute Index", "attributes", ["attr"]

class RocqOptionIndex(RocqSubdomainsIndex):
    name, localname, shortname, subdomains = "optindex", "Flags, options and Tables Index", "options", ["flag", "opt", "table"]

class RocqGallinaIndex(RocqSubdomainsIndex):
    name, localname, shortname, subdomains = "thmindex", "Gallina Index", "theorems", ["thm"]

class RocqExceptionIndex(RocqSubdomainsIndex):
    name, localname, shortname, subdomains = "exnindex", "Errors and Warnings Index", "errors", ["exn", "warn"]

class IndexXRefRole(XRefRole):
    """A link to one of our domain-specific indices."""
    lowercase = True
    innernodeclass = nodes.inline
    warn_dangling = True

    def process_link(self, env, refnode, has_explicit_title, title, target):
        if not has_explicit_title:
            index = RocqDomain.find_index_by_name(target)
            if index:
                title = index.localname
        return title, target

class StdGlossaryIndex(Index):
    name, localname, shortname = "glossindex", "Glossary", "terms"

    def generate(self, docnames=None):
        def ci_sort(entry):
            ((type, itemname), (docname, anchor)) = entry
            return itemname.lower()

        content = defaultdict(list)
        for ((type, itemname), (docname, anchor)) in sorted(self.domain.data['objects'].items(), key=ci_sort):
            if type == 'term':
                entries = content[itemname[0].lower()]
                entries.append([itemname, 0, docname, anchor, '', '', ''])
        return content.items(), False

def GrammarProductionRole(typ, rawtext, text, lineno, inliner, options={}, content=[]):
    """A grammar production not included in a ``prodn`` directive.
    See the documentation of the ":production:" role in doc/sphinx/README.rst
    """
    #pylint: disable=dangerous-default-value, unused-argument
    env = inliner.document.settings.env
    targetid = make_id('grammar-token-{}'.format(text))
    target = nodes.target('', '', ids=[targetid])
    inliner.document.note_explicit_target(target)
    code = nodes.literal(rawtext, text, role=typ.lower())
    node = nodes.inline(rawtext, '', target, code, classes=['inline-grammar-production'])
    set_role_source_info(inliner, lineno, node)
    env.domaindata['std']['objects']['token', text] = env.docname, targetid
    return [node], []

GrammarProductionRole.role_name = "production"


def GlossaryDefRole(typ, rawtext, text, lineno, inliner, options={}, content=[]):
    """A role to mark the definition of a glossary term inline in the text.
    See the documentation of the ":gdef:" role in doc/sphinx/README.rst
    """
    #pylint: disable=dangerous-default-value, unused-argument
    env = inliner.document.settings.env
    std = env.domaindata['std']['objects']
    m = ReferenceRole.explicit_title_re.match(text)
    if m:
        (text, term) = m.groups()
        text = text.strip()
    else:
        term = text
    key = ('term', term)

    if key in std:
        MSG = 'Duplicate object: {}; other is at {}'
        msg = MSG.format(term, env.doc2path(std[key][0]))
        inliner.document.reporter.warning(msg, line=lineno)

    targetid = make_id('term-{}'.format(term))
    std[key] = (env.docname, targetid)
    target = nodes.target('', '', ids=[targetid], names=[term])
    inliner.document.note_explicit_target(target)
    node = nodes.inline(rawtext, '', target, nodes.Text(text), classes=['term-defn'])
    set_role_source_info(inliner, lineno, node)
    return [node], []

GlossaryDefRole.role_name = "gdef"

class RocqDomain(Domain):
    """A domain to document Rocq code.

    Sphinx has a notion of “domains”, used to tailor it to a specific language.
    Domains mostly consist in descriptions of the objects that we wish to
    describe (for Rocq, this includes tactics, tactic notations, options,
    exceptions, etc.), as well as domain-specific roles and directives.

    Each domain is responsible for tracking its objects, and resolving
    references to them. In the case of Rocq, this leads us to define Rocq
    “subdomains”, which classify objects into categories in which names must be
    unique. For example, a tactic and a theorem may share a name, but two
    tactics cannot be named the same.
    """

    name = 'rocq'
    label = 'Rocq'

    object_types = {
        # ObjType (= directive type) → (Local name, *xref-roles)
        'cmd': ObjType('cmd', 'cmd'),
        'cmdv': ObjType('cmdv', 'cmd'),
        'tacn': ObjType('tacn', 'tacn'),
        'tacv': ObjType('tacv', 'tacn'),
        'opt': ObjType('opt', 'opt'),
        'flag': ObjType('flag', 'flag'),
        'table': ObjType('table', 'table'),
        'attr': ObjType('attr', 'attr'),
        'thm': ObjType('thm', 'thm'),
        'prodn': ObjType('prodn', 'prodn'),
        'exn': ObjType('exn', 'exn'),
        'warn': ObjType('warn', 'exn'),
        'index': ObjType('index', 'index', searchprio=-1)
    }

    directives = {
        # Note that some directives live in the same semantic subdomain; ie
        # there's one directive per object type, but some object types map to
        # the same role.
        'cmd': VernacObject,
        'cmdv': VernacVariantObject,
        'tacn': TacticObject,
        'tacv': TacticVariantObject,
        'opt': OptionObject,
        'flag': FlagObject,
        'table': TableObject,
        'attr': AttributeObject,
        'thm': GallinaObject,
        'prodn' : ProductionObject,
        'exn': ExceptionObject,
        'warn': WarningObject,
    }

    roles = {
        # Each of these roles lives in a different semantic “subdomain”
        'cmd': XRefRole(warn_dangling=True),
        'tacn': XRefRole(warn_dangling=True),
        'opt': XRefRole(warn_dangling=True),
        'flag': XRefRole(warn_dangling=True),
        'table': XRefRole(warn_dangling=True),
        'attr': XRefRole(warn_dangling=True),
        'thm': XRefRole(warn_dangling=True),
        'prodn' : XRefRole(warn_dangling=True),
        'exn': XRefRole(warn_dangling=True),
        'warn': XRefRole(warn_dangling=True),
        # This one is special
        'index': IndexXRefRole(),
        # These are used for highlighting
        'n': NotationRole,
        'g': RocqCodeRole
    }

    indices = [RocqVernacIndex, RocqTacticIndex, RocqOptionIndex, RocqGallinaIndex, RocqExceptionIndex, RocqAttributeIndex]

    data_version = 1
    initial_data = {
        # Collect everything under a key that we control, since Sphinx adds
        # others, such as “version”
        'objects' : { # subdomain → name → SubdomainItemData
            'cmd': {},
            'tacn': {},
            'opt': {},
            'flag': {},
            'table': {},
            'attr': {},
            'thm': {},
            'prodn' : {},
            'exn': {},
            'warn': {},
        }
    }

    @staticmethod
    def find_index_by_name(targetid):
        for index in RocqDomain.indices:
            if index.name == targetid:
                return index
        return None

    def get_objects(self):
        # Used for searching and object inventories (intersphinx)
        for _, objects in self.data['objects'].items():
            for name, data in objects.items():
                yield (name, name, data.objtype, data.docname, data.targetid, self.object_types[data.objtype].attrs['searchprio'])
        for index in self.indices:
            yield (index.name, index.localname, 'index', "rocq-" + index.name, '', -1)

    def merge_domaindata(self, docnames, otherdata):
        DUP = "Duplicate declaration: '{}' also defined in '{}'.\n"
        for subdomain, their_objects in otherdata['objects'].items():
            our_objects = self.data['objects'][subdomain]
            for name, data in their_objects.items():
                if data.docname in docnames:
                    if name in our_objects:
                        self.env.warn(data.docname, DUP.format(name, our_objects[name].docname))
                    our_objects[name] = data

    def resolve_xref(self, env, fromdocname, builder, role, targetname, node, contnode):
        # ‘target’ is the name that was written in the document
        # ‘role’ is where this xref comes from; it's exactly one of our subdomains
        if role == 'index':
            index = RocqDomain.find_index_by_name(targetname)
            if index:
                return make_refnode(builder, fromdocname, "rocq-" + index.name, '', contnode, index.localname)
        else:
            resolved = self.data['objects'][role].get(targetname)
            if resolved:
                return make_refnode(builder, fromdocname, resolved.docname, resolved.targetid, contnode, targetname)
        return None

    def clear_doc(self, docname_to_clear):
        for subdomain_objects in self.data['objects'].values():
            for name, data in list(subdomain_objects.items()):
                if data.docname == docname_to_clear:
                    del subdomain_objects[name]

def is_rocqtop_or_rocqdoc_block(node):
    return (isinstance(node, nodes.Element) and
       ('rocqtop' in node['classes'] or 'rocqdoc' in node['classes']))

def simplify_source_code_blocks_for_latex(app, doctree, fromdocname): # pylint: disable=unused-argument
    """Simplify rocqdoc and rocqtop blocks.

    In HTML mode, this does nothing; in other formats, such as LaTeX, it
    replaces rocqdoc and rocqtop blocks by plain text sources, which will use
    pygments if available.  This prevents the LaTeX builder from getting
    confused.
    """
    is_html = app.builder.tags.has("html")
    for node in doctree.traverse(is_rocqtop_or_rocqdoc_block):
        if is_html:
            node.rawsource = '' # Prevent pygments from kicking in
        elif 'rocqtop-hidden' in node['classes']:
            node.parent.remove(node)
        else:
            node.replace_self(nodes.literal_block(node.rawsource, node.rawsource, language="Coq"))

class IndicesMarkdownTranslator(MarkdownTranslator):
    @pushing_context
    def visit_caution(self, _node):
        self._push_box("CAUTION")

    def visit_admonition(self, node):
        self.add('\n\n')
    def depart_admonition(self, node):
        self.add('\n\n')

    # we do not create links in markdown
    def visit_reference(self, node):
        pass
    def visit_download_reference(self, node):
        pass


    @pushing_context
    def visit_desc_annotation(self, node):
        text = node.astext().strip()
        if text == "Error":
            self.add("*Possible error*:")
            raise nodes.SkipNode
        elif text == "Warning":
            self.add("*Possible warning*:")
            raise nodes.SkipNode
        self._push_context(WrappedContext("_"))

    def visit_subscript(self, node):
        self.add('(')
    def depart_subscript(self, node):
        self.add(')')


class IndicesBuilder(TextBuilder):
    """Custom sphinx builder to generate JSON files containing indices of individual custom directives.

    It is based on the TextBuilder to be able to generate the content of the documentation for each object."""
    name = 'indices'
    format = 'json'
    allow_parallel = False

    default_translator_class = IndicesMarkdownTranslator

    def init(self):
        super().init()
        self.rendered: dict[str, str] = {}

    def write_doc(self, docname: str, doctree: nodes.document) -> None:
        domain = self.env.get_domain('rocq')
        # find all nodes that are handled by our rocq domain
        for node in doctree.findall(lambda n: isinstance(n, nodes.Element) and n.get('objtype') in domain.object_types):
            # all IDs will be associated to this content
            all_target_ids = []
            for sig in node.traverse(addnodes.desc_signature):
                all_target_ids.extend(sig.get('ids', []))

            # the content is the next node
            content_node = node.next_node(addnodes.desc_content)

            if all_target_ids and content_node:
                # translate sphinx nodes to text and associate it to all IDs
                translator = self.create_translator(doctree, self)
                translator.visit_document(doctree)
                content_node.walkabout(translator)
                translator.depart_document(doctree)
                text = translator.astext().strip()
                # remove some leftover formatting
                text = text.replace('\u200b', '|').replace('\\\\textquotesingle{}', "").replace('\\textquotesingle{}', "")
                for tid in all_target_ids:
                    self.rendered[tid] = text

    def finish(self):
        domain = self.env.get_domain('rocq')

        domain_data: dict[str, dict[str, SubdomainItemData]] = domain.data['objects']
        for subdomain, collected in domain_data.items():
            output_data = {}
            for name, data in collected.items():
                output_data[name] = {
                    "documentation_path": data.docname,
                    "documentation_anchor": data.targetid,
                    "syntax": [[tag, notation.asdict()] for [tag, notation] in data.syntax],
                    "documentation": self.rendered.get(data.targetid, "")
                }

            with open(self.outdir / f"{subdomain}index.json", "w") as f:
                json.dump(output_data, f, indent=2)

ROCQ_ADDITIONAL_DIRECTIVES = [RocqtopDirective,
                             RocqdocDirective,
                             ExampleDirective,
                             InferenceDirective,
                             PreambleDirective]

ROCQ_ADDITIONAL_ROLES = [GrammarProductionRole,
                        GlossaryDefRole]

def setup(app):
    """Register the Rocq domain"""

    # A few sanity checks:
    subdomains = set(obj.subdomain for obj in RocqDomain.directives.values())
    found = set (obj for obj in chain(*(idx.subdomains for idx in RocqDomain.indices)))
    assert subdomains.issuperset(found), "Missing subdomains: {}".format(found.difference(subdomains))

    assert subdomains.issubset(RocqDomain.roles.keys()), \
        "Missing from RocqDomain.roles: {}".format(subdomains.difference(RocqDomain.roles.keys()))

    # Add domain, directives, and roles
    app.add_domain(RocqDomain)
    app.add_builder(IndicesBuilder)
    app.add_index_to_domain('std', StdGlossaryIndex)

    for role in ROCQ_ADDITIONAL_ROLES:
        app.add_role(role.role_name, role)

    for directive in ROCQ_ADDITIONAL_DIRECTIVES:
        app.add_directive(directive.directive_name, directive)

    app.add_transform(RocqtopBlocksTransform)
    app.connect('doctree-resolved', simplify_source_code_blocks_for_latex)
    app.connect('doctree-resolved', RocqtopBlocksTransform.merge_consecutive_rocqtop_blocks)

    # Add extra styles
    app.add_css_file("ansi.css")
    app.add_css_file("coqdoc.css")
    app.add_js_file("notations.js")
    app.add_css_file("notations.css")
    app.add_css_file("pre-text.css")

    # Tell Sphinx about extra settings
    app.add_config_value("report_undocumented_rocq_objects", None, 'env')

    # ``env_version`` is used by Sphinx to know when to invalidate
    # rocqdomain-specific bits in its caches.  It should be incremented when the
    # contents of ``env.domaindata['rocq']`` change.  See
    # `https://github.com/sphinx-doc/sphinx/issues/4460`.
    meta = { "version": "0.1",
             "env_version": 2,
             "parallel_read_safe": True }
    return meta
