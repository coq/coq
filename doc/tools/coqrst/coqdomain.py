# -*- coding: utf-8 -*-
##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2018       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""A Coq domain for Sphinx.

Currently geared towards Coq's manual, rather than Coq source files, but one
could imagine extending it.
"""

# pylint: disable=too-few-public-methods

import re
from itertools import chain
from collections import defaultdict

from docutils import nodes, utils
from docutils.transforms import Transform
from docutils.parsers.rst import Directive, directives
from docutils.parsers.rst.roles import code_role #, set_classes
from docutils.parsers.rst.directives.admonitions import BaseAdmonition

from sphinx import addnodes
from sphinx.roles import XRefRole
from sphinx.errors import ExtensionError
from sphinx.util.nodes import set_source_info, set_role_source_info, make_refnode
from sphinx.util.logging import getLogger
from sphinx.directives import ObjectDescription
from sphinx.domains import Domain, ObjType, Index
from sphinx.domains.std import token_xrefs
from sphinx.ext import mathbase

from . import coqdoc
from .repl import ansicolors
from .repl.coqtop import CoqTop
from .notations.sphinx import sphinxify
from .notations.plain import stringify_with_ellipses

def parse_notation(notation, source, line, rawtext=None):
    """Parse notation and wrap it in an inline node"""
    node = nodes.inline(rawtext or notation, '', *sphinxify(notation), classes=['notation'])
    node.source, node.line = source, line
    return node

def highlight_using_coqdoc(sentence):
    """Lex sentence using coqdoc, and yield inline nodes for each token"""
    tokens = coqdoc.lex(utils.unescape(sentence, 1))
    for classes, value in tokens:
        yield nodes.inline(value, value, classes=classes)

def make_target(objtype, targetid):
    """Create a target to an object of type objtype and id targetid"""
    return "coq:{}.{}".format(objtype, targetid)

def make_math_node(latex, docname, nowrap):
    node = mathbase.displaymath()
    node['latex'] = latex
    node['label'] = None # Otherwise equations are numbered
    node['nowrap'] = nowrap
    node['docname'] = docname
    node['number'] = None
    return node

class CoqObject(ObjectDescription):
    """A generic Coq object for Sphinx; all Coq objects are subclasses of this.

    The fields and methods to override are listed at the top of this class'
    implementation.  Each object supports the :name: option, which gives an
    explicit name to link to.

    See the comments and docstrings in CoqObject for more information.
    """

    # The semantic domain in which this object lives (eg. “tac”, “cmd”, “chm”…).
    # It matches exactly one of the roles used for cross-referencing.
    subdomain = None # type: str

    # The suffix to use in indices for objects of this type (eg. “(tac)”)
    index_suffix = None # type: str

    # The annotation to add to headers of objects of this type
    # (eg. “Command”, “Theorem”)
    annotation = None # type: str

    def _name_from_signature(self, signature): # pylint: disable=no-self-use, unused-argument
        """Convert a signature into a name to link to.

        ‘Signature’ is Sphinx parlance for an object's header (think “type
        signature”); for example, the signature of the simplest form of the
        ``exact`` tactic is ``exact @id``.

        Returns None by default, in which case no name will be automatically
        generated.  This is a convenient way to automatically generate names
        (link targets) without having to write explicit names everywhere.

        """
        return None

    def _render_signature(self, signature, signode):
        """Render a signature, placing resulting nodes into signode."""
        raise NotImplementedError(self)

    option_spec = {
        # Explicit object naming
        'name': directives.unchanged,
        # Silence warnings produced by report_undocumented_coq_objects
        'undocumented': directives.flag,
        # noindex omits this object from its index
        'noindex': directives.flag
    }

    def subdomain_data(self):
        if self.subdomain is None:
            raise ValueError()
        return self.env.domaindata['coq']['objects'][self.subdomain]

    def _render_annotation(self, signode):
        if self.annotation:
            annot_node = nodes.inline(self.annotation, self.annotation, classes=['sigannot'])
            signode += addnodes.desc_annotation(self.annotation, '', annot_node)
            signode += nodes.Text(' ')

    def handle_signature(self, signature, signode):
        """Prefix signature with the proper annotation, then render it using
        ``_render_signature`` (for example, add “Command” in front of commands).

        :returns: the name given to the resulting node, if any
        """
        self._render_annotation(signode)
        self._render_signature(signature, signode)
        name = self._names.get(signature)
        if name is None:
            name = self._name_from_signature(signature)
            # remove trailing ‘.’ found in commands, but not ‘...’ (ellipsis)
            if name is not None and name.endswith(".") and not name.endswith("..."):
                name = name[:-1]
        return name

    def _warn_if_duplicate_name(self, objects, name):
        """Check that two objects in the same domain don't have the same name."""
        if name in objects:
            MSG = 'Duplicate object: {}; other is at {}'
            msg = MSG.format(name, self.env.doc2path(objects[name][0]))
            self.state_machine.reporter.warning(msg, line=self.lineno)

    def _warn_if_duplicate_name(self, objects, name):
        """Check that two objects in the same domain don't have the same name."""
        if name in objects:
            MSG = 'Duplicate object: {}; other is at {}'
            msg = MSG.format(name, self.env.doc2path(objects[name][0]))
            self.state_machine.reporter.warning(msg, line=self.lineno)

    def _record_name(self, name, target_id):
        """Record a name, mapping it to target_id

        Warns if another object of the same name already exists.
        """
        names_in_subdomain = self.subdomain_data()
        self._warn_if_duplicate_name(names_in_subdomain, name)
        names_in_subdomain[name] = (self.env.docname, self.objtype, target_id)

    def _target_id(self, name):
        return make_target(self.objtype, nodes.make_id(name))

    def _add_target(self, signode, name):
        """Register a link target ‘name’, pointing to signode."""
        targetid = self._target_id(name)
        if targetid not in self.state.document.ids:
            signode['ids'].append(targetid)
            signode['names'].append(name)
            signode['first'] = (not self.names)
            self.state.document.note_explicit_target(signode)
            self._record_name(name, targetid)
        return targetid

    def _add_index_entry(self, name, target):
        """Add `name` (pointing to `target`) to the main index."""
        assert isinstance(name, str)
        if not name.startswith("_"):
            # remove trailing . , found in commands, but not ... (ellipsis)
            trim = name.endswith(".") and not name.endswith("...")
            index_text = name[:-1] if trim else name
            if self.index_suffix:
                index_text += " " + self.index_suffix
            self.indexnode['entries'].append(('single', index_text, target, '', None))

    def add_target_and_index(self, name, _, signode):
        """Attach a link target to `signode` and an index entry for `name`.
        This is only called (from ``ObjectDescription.run``) if ``:noindex:`` isn't specified."""
        if name:
            target = self._add_target(signode, name)
            self._add_index_entry(name, target)
            return target

    def _warn_if_undocumented(self):
        document = self.state.document
        config = document.settings.env.config
        report = config.report_undocumented_coq_objects
        if report and not self.content and "undocumented" not in self.options:
            # This is annoyingly convoluted, but we don't want to raise warnings
            # or interrupt the generation of the current node.  For more details
            # see https://github.com/sphinx-doc/sphinx/issues/4976.
            msg = 'No contents in directive {}'.format(self.name)
            node = document.reporter.info(msg, line=self.lineno)
            getLogger(__name__).info(node.astext())
            if report == "warning":
                raise self.warning(msg)

    def _prepare_names(self):
        sigs = self.get_signatures()
        names = self.options.get("name")
        if names is None:
            self._names = {}
        else:
            names = [n.strip() for n in names.split(";")]
            if len(names) != len(sigs):
                ERR = ("Expected {} semicolon-separated names, got {}.  " +
                       "Please provide one name per signature line.")
                raise self.error(ERR.format(len(names), len(sigs)))
            self._names = dict(zip(sigs, names))

    def run(self):
        self._warn_if_undocumented()
        self._prepare_names()
        return super().run()

class PlainObject(CoqObject):
    """A base class for objects whose signatures should be rendered literally."""
    def _render_signature(self, signature, signode):
        signode += addnodes.desc_name(signature, signature)

class NotationObject(CoqObject):
    """A base class for objects whose signatures should be rendered as nested boxes.

    Objects that inherit from this class can use the notation grammar (“{+ …}”,
    “@…”, etc.) in their signature.
    """
    def _render_signature(self, signature, signode):
        position = self.state_machine.get_source_and_line(self.lineno)
        tacn_node = parse_notation(signature, *position)
        signode += addnodes.desc_name(signature, '', tacn_node)

class GallinaObject(PlainObject):
    r"""A theorem.

    Example::

       .. thm:: Bound on the ceiling function

          Let :math:`p` be an integer and :math:`c` a rational constant. Then
          :math:`p \ge c \rightarrow p \ge \lceil{c}\rceil`.
    """
    subdomain = "thm"
    index_suffix = "(thm)"
    annotation = "Theorem"

class VernacObject(NotationObject):
    """A Coq command.

    Example::

       .. cmd:: Infix "@symbol" := @term ({+, @modifier}).

          This command is equivalent to :n:`…`.
    """
    subdomain = "cmd"
    index_suffix = "(cmd)"
    annotation = "Command"

    def _name_from_signature(self, signature):
        m = re.match(r"[a-zA-Z ]+", signature)
        if m:
            return m.group(0).strip()

class VernacVariantObject(VernacObject):
    """A variant of a Coq command.

    Example::

       .. cmd:: Axiom @ident : @term.

          This command links :token:`term` to the name :token:`term` as its specification in
          the global context. The fact asserted by :token:`term` is thus assumed as a
          postulate.

          .. cmdv:: Parameter @ident : @term.

             This is equivalent to :n:`Axiom @ident : @term`.
    """
    index_suffix = "(cmdv)"
    annotation = "Variant"

    def _name_from_signature(self, signature):
        return None

class TacticNotationObject(NotationObject):
    """A tactic, or a tactic notation.

    Example::

       .. tacn:: do @num @expr

          :token:`expr` is evaluated to ``v`` which must be a tactic value. …
    """
    subdomain = "tacn"
    index_suffix = "(tacn)"
    annotation = None

class TacticNotationVariantObject(TacticNotationObject):
    """A variant of a tactic.

    Example::

       .. tacn:: fail

          This is the always-failing tactic: it does not solve any goal. It is
          useful for defining other tacticals since it can be caught by
          :tacn:`try`, :tacn:`repeat`, :tacn:`match goal`, or the branching
          tacticals. …

          .. tacv:: fail @natural

             The number is the failure level. If no level is specified, it
             defaults to 0. …
    """
    index_suffix = "(tacnv)"
    annotation = "Variant"

class OptionObject(NotationObject):
    """A Coq option (a setting with non-boolean value, e.g. a string or numeric value).

    Example::

       .. opt:: Hyps Limit @num
          :name Hyps Limit

          Controls the maximum number of hypotheses displayed in goals after
          application of a tactic.
    """
    subdomain = "opt"
    index_suffix = "(opt)"
    annotation = "Option"

    def _name_from_signature(self, signature):
        return stringify_with_ellipses(signature)


class FlagObject(NotationObject):
    """A Coq flag (i.e. a boolean setting).

    Example::

       .. flag:: Nonrecursive Elimination Schemes

          Controls whether types declared with the keywords
          :cmd:`Variant` and :cmd:`Record` get an automatic declaration of
          induction principles.
    """
    subdomain = "flag"
    index_suffix = "(flag)"
    annotation = "Flag"

    def _name_from_signature(self, signature):
        return stringify_with_ellipses(signature)


class TableObject(NotationObject):
    """A Coq table, i.e. a setting that is a set of values.

    Example::

       .. table:: Search Blacklist @string
          :name: Search Blacklist

          Controls ...
    """
    subdomain = "table"
    index_suffix = "(table)"
    annotation = "Table"

    def _name_from_signature(self, signature):
        return stringify_with_ellipses(signature)

class ProductionObject(CoqObject):
    r"""A grammar production.

    This is useful if you intend to document individual grammar productions.
    Otherwise, use Sphinx's `production lists
    <http://www.sphinx-doc.org/en/stable/markup/para.html#directive-productionlist>`_.

    Unlike ``.. productionlist``\ s, this directive accepts notation syntax.


    Usage::

       .. prodn:: token += production
       .. prodn:: token ::= production

    Example::

        .. prodn:: term += let: @pattern := @term in @term
        .. prodn:: occ_switch ::= { {? + %| - } {* @num } }

    """
    subdomain = "prodn"
    #annotation = "Grammar production"

    def _render_signature(self, signature, signode):
        raise NotImplementedError(self)

    SIG_ERROR = ("Invalid syntax in ``.. prodn::`` directive"
                 + "\nExpected ``name ::= ...`` or ``name += ...``"
                 + " (e.g. ``pattern += constr:(@ident)``)")

    def handle_signature(self, signature, signode):
        nsplits = 2
        parts = signature.split(maxsplit=nsplits)
        if len(parts) != 3:
            raise ExtensionError(ProductionObject.SIG_ERROR)

        lhs, op, rhs = (part.strip() for part in parts)
        if op not in ["::=", "+="]:
            raise ExtensionError(ProductionObject.SIG_ERROR)

        self._render_annotation(signode)

        lhs_op = '{} {} '.format(lhs, op)
        lhs_node = nodes.literal(lhs_op, lhs_op)

        position = self.state_machine.get_source_and_line(self.lineno)
        rhs_node = parse_notation(rhs, *position)
        signode += addnodes.desc_name(signature, '', lhs_node, rhs_node)

        return ('token', lhs) if op == '::=' else None

    def _add_index_entry(self, name, target):
        pass

    def _target_id(self, name):
        # Use `name[1]` instead of ``nodes.make_id(name[1])`` to work around
        # https://github.com/sphinx-doc/sphinx/issues/4983
        return 'grammar-token-{}'.format(name[1])

    def _record_name(self, name, targetid):
        env = self.state.document.settings.env
        objects = env.domaindata['std']['objects']
        self._warn_if_duplicate_name(objects, name)
        objects[name] = env.docname, targetid

class ExceptionObject(NotationObject):
    """An error raised by a Coq command or tactic.

    This commonly appears nested in the ``.. tacn::`` that raises the
    exception.

    Example::

       .. tacv:: assert @form by @tactic

          This tactic applies :n:`@tactic` to solve the subgoals generated by
          ``assert``.

          .. exn:: Proof is not complete

             Raised if :n:`@tactic` does not fully solve the goal.
    """
    subdomain = "exn"
    index_suffix = "(err)"
    annotation = "Error"
    # Uses “exn” since “err” already is a CSS class added by “writer_aux”.

    # Generate names automatically
    def _name_from_signature(self, signature):
        return stringify_with_ellipses(signature)

class WarningObject(NotationObject):
    """An warning raised by a Coq command or tactic..

    Do not mistake this for ``.. warning::``; this directive is for warning
    messages produced by Coq.


    Example::

       .. warn:: Ambiguous path

          When the coercion :token:`qualid` is added to the inheritance graph, non
          valid coercion paths are ignored.
    """
    subdomain = "warn"
    index_suffix = "(warn)"
    annotation = "Warning"

    # Generate names automatically
    def _name_from_signature(self, signature):
        return stringify_with_ellipses(signature)

def NotationRole(role, rawtext, text, lineno, inliner, options={}, content=[]):
    #pylint: disable=unused-argument, dangerous-default-value
    """Any text using the notation syntax (``@id``, ``{+, …}``, etc.).

    Use this to explain tactic equivalences.  For example, you might write
    this::

       :n:`generalize @term as @ident` is just like :n:`generalize @term`, but
       it names the introduced hypothesis :token:`ident`.

    Note that this example also uses ``:token:``.  That's because ``ident`` is
    defined in the Coq manual as a grammar production, and ``:token:``
    creates a link to that.  When referring to a placeholder that happens to be
    a grammar production, ``:token:`…``` is typically preferable to ``:n:`@…```.
    """
    notation = utils.unescape(text, 1)
    position = inliner.reporter.get_source_and_line(lineno)
    return [nodes.literal(rawtext, '', parse_notation(notation, *position, rawtext=rawtext))], []

def coq_code_role(role, rawtext, text, lineno, inliner, options={}, content=[]):
    #pylint: disable=dangerous-default-value
    """Coq code.

    Use this for Gallina and Ltac snippets::

       :g:`apply plus_comm; reflexivity`
       :g:`Set Printing All.`
       :g:`forall (x: t), P(x)`
    """
    options['language'] = 'Coq'
    return code_role(role, rawtext, text, lineno, inliner, options, content)
    ## Too heavy:
    ## Forked from code_role to use our custom tokenizer; this doesn't work for
    ## snippets though: for example CoqDoc swallows the parentheses around this:
    ## “(a: A) (b: B)”
    # set_classes(options)
    # classes = ['code', 'coq']
    # code = utils.unescape(text, 1)
    # node = nodes.literal(rawtext, '', *highlight_using_coqdoc(code), classes=classes)
    # return [node], []

CoqCodeRole = coq_code_role

class CoqtopDirective(Directive):
    r"""A reST directive to describe interactions with Coqtop.

    Usage::

       .. coqtop:: options…

          Coq code to send to coqtop

    Example::

       .. coqtop:: in reset undo

          Print nat.
          Definition a := 1.

    The blank line after the directive is required.  If you begin a proof,
    include an ``Abort`` afterwards to reset coqtop for the next example.

    Here is a list of permissible options:

    - Display options

      - ``all``: Display input and output
      - ``in``: Display only input
      - ``out``: Display only output
      - ``none``: Display neither (useful for setup commands)

    - Behavior options

      - ``reset``: Send a ``Reset Initial`` command before running this block
      - ``undo``: Send an ``Undo n`` (``n`` = number of sentences) command after
        running all the commands in this block

    ``coqtop``\ 's state is preserved across consecutive ``.. coqtop::`` blocks
    of the same document (``coqrst`` creates a single ``coqtop`` process per
    reST source file).  Use the ``reset`` option to reset Coq's state.
    """
    has_content = True
    required_arguments = 0
    optional_arguments = 1
    final_argument_whitespace = True
    option_spec = { 'name': directives.unchanged }
    directive_name = "coqtop"

    def run(self):
        # Uses a ‘container’ instead of a ‘literal_block’ to disable
        # Pygments-based post-processing (we could also set rawsource to '')
        content = '\n'.join(self.content)
        args = self.arguments[0].split() if self.arguments else ['in']
        if 'all' in args:
            args.extend(['in', 'out'])
        node = nodes.container(content, coqtop_options = list(set(args)),
                               classes=['coqtop', 'literal-block'])
        self.add_name(node)
        return [node]

class CoqdocDirective(Directive):
    """A reST directive to display Coqtop-formatted source code.

    Usage::

       .. coqdoc::

          Coq code to highlight

    Example::

       .. coqdoc::

          Definition test := 1.
    """
    # TODO implement this as a Pygments highlighter?
    has_content = True
    required_arguments = 0
    optional_arguments = 0
    final_argument_whitespace = True
    option_spec = { 'name': directives.unchanged }
    directive_name = "coqdoc"

    def run(self):
        # Uses a ‘container’ instead of a ‘literal_block’ to disable
        # Pygments-based post-processing (we could also set rawsource to '')
        content = '\n'.join(self.content)
        node = nodes.inline(content, '', *highlight_using_coqdoc(content))
        wrapper = nodes.container(content, node, classes=['coqdoc', 'literal-block'])
        self.add_name(wrapper)
        return [wrapper]

class ExampleDirective(BaseAdmonition):
    """A reST directive for examples.

    This behaves like a generic admonition; see
    http://docutils.sourceforge.net/docs/ref/rst/directives.html#generic-admonition
    for more details.

    Optionally, any text immediately following the ``.. example::`` header is
    used as the example's title.

    Example::

       .. example:: Adding a hint to a database

          The following adds ``plus_comm`` to the ``plu`` database:

          .. coqdoc::

             Hint Resolve plus_comm : plu.
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
    r"""A reST directive to include a TeX file.

    Mostly useful to let MathJax know about `\def`s and `\newcommand`s.  The
    contents of the TeX file are wrapped in a math environment, as MathJax
    doesn't process LaTeX definitions otherwise.

    Usage::

       .. preamble:: preamble.tex
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
    r"""A reST directive to format inference rules.

    This also serves as a small illustration of the way to create new Sphinx
    directives.

    Usage::

       .. inference:: name

          newline-separated premises
          --------------------------
          conclusion

    Example::

       .. inference:: Prod-Pro

          \WTEG{T}{s}
          s \in \Sort
          \WTE{\Gamma::(x:T)}{U}{\Prop}
          -----------------------------
          \WTEG{\forall~x:T,U}{\Prop}
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

        tid = nodes.make_id(title)
        target = nodes.target('', '', ids=['inference-' + tid])
        self.state.document.note_explicit_target(target)

        term, desc = nodes.term('', title), nodes.description('', math_node)
        dli = nodes.definition_list_item('', term, desc)
        dl = nodes.definition_list(content, target, dli)
        set_source_info(self, dl)
        return [dl]

class AnsiColorsParser():
    """Parse ANSI-colored output from Coqtop into Sphinx nodes."""

    # Coqtop's output crashes ansi.py, because it contains a bunch of extended codes
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
        """Parse raw (an ANSI-colored output string from Coqtop) into Sphinx nodes."""
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

class CoqtopBlocksTransform(Transform):
    """Filter handling the actual work for the coqtop directive

    Adds coqtop's responses, colorizes input and output, and merges consecutive
    coqtop directives for better visual rendition.
    """
    default_priority = 10

    @staticmethod
    def is_coqtop_block(node):
        return isinstance(node, nodes.Element) and 'coqtop_options' in node

    @staticmethod
    def split_sentences(source):
        """Split Coq sentences in source. Could be improved."""
        return re.split(r"(?<=(?<!\.)\.)\s+", source)

    @staticmethod
    def parse_options(options):
        """Parse options according to the description in CoqtopDirective."""
        opt_undo = 'undo' in options
        opt_reset = 'reset' in options
        opt_all, opt_none = 'all' in options, 'none' in options
        opt_input, opt_output = opt_all or 'in' in options, opt_all or 'out' in options

        unexpected_options = list(set(options) - set(('reset', 'undo', 'all', 'none', 'in', 'out')))
        if unexpected_options:
            raise ValueError("Unexpected options for .. coqtop:: {}".format(unexpected_options))
        elif (opt_input or opt_output) and opt_none:
            raise ValueError("Inconsistent options for .. coqtop:: ‘none’ with ‘in’, ‘out’, or ‘all’")
        elif opt_reset and opt_undo:
            raise ValueError("Inconsistent options for .. coqtop:: ‘undo’ with ‘reset’")

        return opt_undo, opt_reset, opt_input and not opt_none, opt_output and not opt_none

    @staticmethod
    def block_classes(should_show, contents=None):
        """Compute classes to add to a node containing contents.

        :param should_show: Whether this node should be displayed"""
        is_empty = contents is not None and re.match(r"^\s*$", contents)
        if is_empty or not should_show:
            return ['coqtop-hidden']
        else:
            return []

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

    def add_coqtop_output(self):
        """Add coqtop's responses to a Sphinx AST

        Finds nodes to process using is_coqtop_block."""
        with CoqTop(color=True) as repl:
            for node in self.document.traverse(CoqtopBlocksTransform.is_coqtop_block):
                options = node['coqtop_options']
                opt_undo, opt_reset, opt_input, opt_output = self.parse_options(options)

                if opt_reset:
                    repl.sendone("Reset Initial.")
                pairs = []
                for sentence in self.split_sentences(node.rawsource):
                    pairs.append((sentence, repl.sendone(sentence)))
                if opt_undo:
                    repl.sendone("Undo {}.".format(len(pairs)))

                dli = nodes.definition_list_item()
                for sentence, output in pairs:
                    # Use Coqdoq to highlight input
                    in_chunks = highlight_using_coqdoc(sentence)
                    dli += nodes.term(sentence, '', *in_chunks, classes=self.block_classes(opt_input))
                    # Parse ANSI sequences to highlight output
                    out_chunks = AnsiColorsParser().colorize_str(output)
                    dli += nodes.definition(output, *out_chunks, classes=self.block_classes(opt_output, output))
                node.clear()
                node.rawsource = self.make_rawsource(pairs, opt_input, opt_output)
                node['classes'].extend(self.block_classes(opt_input or opt_output))
                node += nodes.inline('', '', classes=['coqtop-reset'] * opt_reset)
                node += nodes.definition_list(node.rawsource, dli)

    @staticmethod
    def merge_coqtop_classes(kept_node, discarded_node):
        discarded_classes = discarded_node['classes']
        if not 'coqtop-hidden' in discarded_classes:
            kept_node['classes'] = [c for c in kept_node['classes']
                                    if c != 'coqtop-hidden']

    @staticmethod
    def merge_consecutive_coqtop_blocks(app, doctree, _):
        """Merge consecutive divs wrapping lists of Coq sentences; keep ‘dl’s separate."""
        for node in doctree.traverse(CoqtopBlocksTransform.is_coqtop_block):
            if node.parent:
                rawsources, names = [node.rawsource], set(node['names'])
                for sibling in node.traverse(include_self=False, descend=False,
                                             siblings=True, ascend=False):
                    if CoqtopBlocksTransform.is_coqtop_block(sibling):
                        CoqtopBlocksTransform.merge_coqtop_classes(node, sibling)
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
        self.add_coqtop_output()

class CoqSubdomainsIndex(Index):
    """Index subclass to provide subdomain-specific indices.

    Just as in the original manual, we want to have separate indices for each
    Coq subdomain (tactics, commands, options, etc)"""

    name, localname, shortname, subdomains = None, None, None, [] # Must be overwritten

    def generate(self, docnames=None):
        content = defaultdict(list)
        items = chain(*(self.domain.data['objects'][subdomain].items()
                        for subdomain in self.subdomains))

        for itemname, (docname, _, anchor) in sorted(items, key=lambda x: x[0].lower()):
            if docnames and docname not in docnames:
                continue

            entries = content[itemname[0].lower()]
            entries.append([itemname, 0, docname, anchor, '', '', ''])

        collapse = False
        content = sorted(content.items())
        return content, collapse

class CoqVernacIndex(CoqSubdomainsIndex):
    name, localname, shortname, subdomains = "cmdindex", "Command Index", "commands", ["cmd"]

class CoqTacticIndex(CoqSubdomainsIndex):
    name, localname, shortname, subdomains = "tacindex", "Tactic Index", "tactics", ["tacn"]

class CoqOptionIndex(CoqSubdomainsIndex):
    name, localname, shortname, subdomains = "optindex", "Flags, options and Tables Index", "options", ["flag", "opt", "table"]

class CoqGallinaIndex(CoqSubdomainsIndex):
    name, localname, shortname, subdomains = "thmindex", "Gallina Index", "theorems", ["thm"]

class CoqExceptionIndex(CoqSubdomainsIndex):
    name, localname, shortname, subdomains = "exnindex", "Errors and Warnings Index", "errors", ["exn", "warn"]

class IndexXRefRole(XRefRole):
    """A link to one of our domain-specific indices."""
    lowercase = True,
    innernodeclass = nodes.inline
    warn_dangling = True

    def process_link(self, env, refnode, has_explicit_title, title, target):
        if not has_explicit_title:
            index = CoqDomain.find_index_by_name(target)
            if index:
                title = index.localname
        return title, target

def GrammarProductionRole(typ, rawtext, text, lineno, inliner, options={}, content=[]):
    """A grammar production not included in a ``productionlist`` directive.

    Useful to informally introduce a production, as part of running text.

    Example::

       :production:`string` indicates a quoted string.

    You're not likely to use this role very commonly; instead, use a
    `production list
    <http://www.sphinx-doc.org/en/stable/markup/para.html#directive-productionlist>`_
    and reference its tokens using ``:token:`…```.
    """
    #pylint: disable=dangerous-default-value, unused-argument
    env = inliner.document.settings.env
    targetid = 'grammar-token-{}'.format(text)
    target = nodes.target('', '', ids=[targetid])
    inliner.document.note_explicit_target(target)
    code = nodes.literal(rawtext, text, role=typ.lower())
    node = nodes.inline(rawtext, '', target, code, classes=['inline-grammar-production'])
    set_role_source_info(inliner, lineno, node)
    env.domaindata['std']['objects']['token', text] = env.docname, targetid
    return [node], []

GrammarProductionRole.role_name = "production"

class CoqDomain(Domain):
    """A domain to document Coq code.

    Sphinx has a notion of “domains”, used to tailor it to a specific language.
    Domains mostly consist in descriptions of the objects that we wish to
    describe (for Coq, this includes tactics, tactic notations, options,
    exceptions, etc.), as well as domain-specific roles and directives.

    Each domain is responsible for tracking its objects, and resolving
    references to them. In the case of Coq, this leads us to define Coq
    “subdomains”, which classify objects into categories in which names must be
    unique. For example, a tactic and a theorem may share a name, but two
    tactics cannot be named the same.
    """

    name = 'coq'
    label = 'Coq'

    object_types = {
        # ObjType (= directive type) → (Local name, *xref-roles)
        'cmd': ObjType('cmd', 'cmd'),
        'cmdv': ObjType('cmdv', 'cmd'),
        'tacn': ObjType('tacn', 'tacn'),
        'tacv': ObjType('tacv', 'tacn'),
        'opt': ObjType('opt', 'opt'),
        'flag': ObjType('flag', 'flag'),
        'table': ObjType('table', 'table'),
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
        'tacn': TacticNotationObject,
        'tacv': TacticNotationVariantObject,
        'opt': OptionObject,
        'flag': FlagObject,
        'table': TableObject,
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
        'thm': XRefRole(warn_dangling=True),
        'prodn' : XRefRole(warn_dangling=True),
        'exn': XRefRole(warn_dangling=True),
        'warn': XRefRole(warn_dangling=True),
        # This one is special
        'index': IndexXRefRole(),
        # These are used for highlighting
        'n': NotationRole,
        'g': CoqCodeRole
    }

    indices = [CoqVernacIndex, CoqTacticIndex, CoqOptionIndex, CoqGallinaIndex, CoqExceptionIndex]

    data_version = 1
    initial_data = {
        # Collect everything under a key that we control, since Sphinx adds
        # others, such as “version”
        'objects' : { # subdomain → name → docname, objtype, targetid
            'cmd': {},
            'tacn': {},
            'opt': {},
            'flag': {},
            'table': {},
            'thm': {},
            'prodn' : {},
            'exn': {},
            'warn': {},
        }
    }

    @staticmethod
    def find_index_by_name(targetid):
        for index in CoqDomain.indices:
            if index.name == targetid:
                return index

    def get_objects(self):
        # Used for searching and object inventories (intersphinx)
        for _, objects in self.data['objects'].items():
            for name, (docname, objtype, targetid) in objects.items():
                yield (name, name, objtype, docname, targetid, self.object_types[objtype].attrs['searchprio'])
        for index in self.indices:
            yield (index.name, index.localname, 'index', "coq-" + index.name, '', -1)

    def merge_domaindata(self, docnames, otherdata):
        DUP = "Duplicate declaration: '{}' also defined in '{}'.\n"
        for subdomain, their_objects in otherdata['objects'].items():
            our_objects = self.data['objects'][subdomain]
            for name, (docname, objtype, targetid) in their_objects.items():
                if docname in docnames:
                    if name in our_objects:
                        self.env.warn(docname, DUP.format(name, our_objects[name][0]))
                    our_objects[name] = (docname, objtype, targetid)

    def resolve_xref(self, env, fromdocname, builder, role, targetname, node, contnode):
        # ‘target’ is the name that was written in the document
        # ‘role’ is where this xref comes from; it's exactly one of our subdomains
        if role == 'index':
            index = CoqDomain.find_index_by_name(targetname)
            if index:
                return make_refnode(builder, fromdocname, "coq-" + index.name, '', contnode, index.localname)
        else:
            resolved = self.data['objects'][role].get(targetname)
            if resolved:
                (todocname, _, targetid) = resolved
                return make_refnode(builder, fromdocname, todocname, targetid, contnode, targetname)

    def clear_doc(self, docname_to_clear):
        for subdomain_objects in self.data['objects'].values():
            for name, (docname, _, _) in list(subdomain_objects.items()):
                if docname == docname_to_clear:
                    del subdomain_objects[name]

def is_coqtop_or_coqdoc_block(node):
    return (isinstance(node, nodes.Element) and
       ('coqtop' in node['classes'] or 'coqdoc' in node['classes']))

def simplify_source_code_blocks_for_latex(app, doctree, fromdocname): # pylint: disable=unused-argument
    """Simplify coqdoc and coqtop blocks.

    In HTML mode, this does nothing; in other formats, such as LaTeX, it
    replaces coqdoc and coqtop blocks by plain text sources, which will use
    pygments if available.  This prevents the LaTeX builder from getting
    confused.
    """
    is_html = app.builder.tags.has("html")
    for node in doctree.traverse(is_coqtop_or_coqdoc_block):
        if is_html:
            node.rawsource = '' # Prevent pygments from kicking in
        elif 'coqtop-hidden' in node['classes']:
            node.parent.remove(node)
        else:
            node.replace_self(nodes.literal_block(node.rawsource, node.rawsource, language="Coq"))

COQ_ADDITIONAL_DIRECTIVES = [CoqtopDirective,
                             CoqdocDirective,
                             ExampleDirective,
                             InferenceDirective,
                             PreambleDirective]

COQ_ADDITIONAL_ROLES = [GrammarProductionRole]

def setup(app):
    """Register the Coq domain"""

    # A few sanity checks:
    subdomains = set(obj.subdomain for obj in CoqDomain.directives.values())
    assert subdomains.issuperset(chain(*(idx.subdomains for idx in CoqDomain.indices)))
    assert subdomains.issubset(CoqDomain.roles.keys())

    # Add domain, directives, and roles
    app.add_domain(CoqDomain)

    for role in COQ_ADDITIONAL_ROLES:
        app.add_role(role.role_name, role)

    for directive in COQ_ADDITIONAL_DIRECTIVES:
        app.add_directive(directive.directive_name, directive)

    app.add_transform(CoqtopBlocksTransform)
    app.connect('doctree-resolved', simplify_source_code_blocks_for_latex)
    app.connect('doctree-resolved', CoqtopBlocksTransform.merge_consecutive_coqtop_blocks)

    # Add extra styles
    app.add_stylesheet("fonts.css")
    app.add_stylesheet("ansi.css")
    app.add_stylesheet("coqdoc.css")
    app.add_javascript("notations.js")
    app.add_stylesheet("notations.css")
    app.add_stylesheet("pre-text.css")

    # Tell Sphinx about extra settings
    app.add_config_value("report_undocumented_coq_objects", None, 'env')

    # ``env_version`` is used by Sphinx to know when to invalidate
    # coqdomain-specific bits in its caches.  It should be incremented when the
    # contents of ``env.domaindata['coq']`` change.  See
    # `https://github.com/sphinx-doc/sphinx/issues/4460`.
    meta = { "version": "0.1",
             "env_version": 2,
             "parallel_read_safe": True }
    return meta
