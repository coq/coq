.. _flags-options-tables:

Flags, Options and Tables
-----------------------------

Coq has many settings to control its behavior.  Setting types include flags, options
and tables:

* A *flag* has a boolean value, such as :flag:`Asymmetric Patterns`.
* An *option* generally has a numeric or string value, such as :opt:`Firstorder Depth`.
* A *table* contains a set of strings or qualids.
* In addition, some commands provide settings, such as :cmd:`Extraction Language`.

.. FIXME Convert "Extraction Language" to an option.

Flags, options and tables are identified by a series of identifiers, each with an initial
capital letter.

.. cmd:: Set @setting_name {? {| @int | @string } }
   :name: Set

   .. insertprodn setting_name setting_name

   .. prodn::
      setting_name ::= {+ @ident }

   If :n:`@setting_name` is a flag, no value may be provided; the flag
   is set to on.
   If :n:`@setting_name` is an option, a value of the appropriate type
   must be provided; the option is set to the specified value.

   This command supports the :attr:`local`, :attr:`global` and :attr:`export` attributes.
   They are described :ref:`here <set_unset_scope_qualifiers>`.

   .. warn:: There is no flag or option with this name: "@setting_name".

      This warning message can be raised by :cmd:`Set` and
      :cmd:`Unset` when :n:`@setting_name` is unknown.  It is a
      warning rather than an error because this helps library authors
      produce Coq code that is compatible with several Coq versions.
      To preserve the same behavior, they may need to set some
      compatibility flags or options that did not exist in previous
      Coq versions.

.. cmd:: Unset @setting_name
   :name: Unset

   If :n:`@setting_name` is a flag, it is set to off.  If :n:`@setting_name` is an option, it is
   set to its default value.

   This command supports the :attr:`local`, :attr:`global` and :attr:`export` attributes.
   They are described :ref:`here <set_unset_scope_qualifiers>`.

.. cmd:: Add @setting_name {+ {| @qualid | @string } }

   Adds the specified values to the table :n:`@setting_name`.

.. cmd:: Remove @setting_name {+ {| @qualid | @string } }

   Removes the specified value from the table :n:`@setting_name`.

.. cmd:: Test @setting_name {? for {+ {| @qualid | @string } } }

   If :n:`@setting_name` is a flag or option, prints its current value.
   If :n:`@setting_name` is a table: if the `for` clause is specified, reports
   whether the table contains each specified value, otherise this is equivalent to
   :cmd:`Print Table`.  The `for` clause is not valid for flags and options.

   .. exn:: There is no flag, option or table with this name: "@setting_name".

      This error message is raised when calling the :cmd:`Test`
      command (without the `for` clause), or the :cmd:`Print Table`
      command, for an unknown :n:`@setting_name`.

   .. exn:: There is no qualid-valued table with this name: "@setting_name".
            There is no string-valued table with this name: "@setting_name".

      These error messages are raised when calling the :cmd:`Add` or
      :cmd:`Remove` commands, or the :cmd:`Test` command with the
      `for` clause, if :n:`@setting_name` is unknown or does not have
      the right type.

.. cmd:: Print Options

   Prints the current value of all flags and options, and the names of all tables.

.. cmd:: Print Table @setting_name

   Prints the values in the table :n:`@setting_name`.

.. cmd:: Print Tables

   A synonym for :cmd:`Print Options`.

.. _set_unset_scope_qualifiers:

Locality attributes supported by :cmd:`Set` and :cmd:`Unset`
````````````````````````````````````````````````````````````

The :cmd:`Set` and :cmd:`Unset` commands support the :attr:`local`,
:attr:`global` and :attr:`export` locality attributes:

* no attribute: the original setting is *not* restored at the end of
  the current module or section.
* :attr:`local` (an alternative syntax is to use the ``Local``
  prefix): the setting is applied within the current module or
  section.  The original value of the setting is restored at the end
  of the current module or section.
* :attr:`export` (an alternative syntax is to use the ``Export``
  prefix): similar to :attr:`local`, the original value of the setting
  is restored at the end of the current module or section.  In
  addition, if the value is set in a module, then :cmd:`Import`\-ing
  the module sets the option or flag.
* :attr:`global` (an alternative syntax is to use the ``Global``
  prefix): the original setting is *not* restored at the end of the
  current module or section.  In addition, if the value is set in a
  file, then :cmd:`Require`\-ing the file sets the option.

Newly opened modules and sections inherit the current settings.

.. note::

   The use of the :attr:`global` attribute with the :cmd:`Set` and
   :cmd:`Unset` commands is discouraged.  If your goal is to define
   project-wide settings, you should rather use the command-line
   arguments ``-set`` and ``-unset`` for setting flags and options
   (cf. :ref:`command-line-options`).
