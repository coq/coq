.. There are multiple issues with sphinxcontrib-bibtex that we have to work around:
   - The list of cited entries is computed right after encountering
     `.. bibliography`, so the file containing that command has to come last
     alphabetically:
     https://sphinxcontrib-bibtex.readthedocs.io/en/latest/usage.html#unresolved-citations-across-documents
   - `.. bibliography::` puts the bibliography on its own page with its own
     title in LaTeX, but includes it inline without a title in HTML:
     https://sphinxcontrib-bibtex.readthedocs.io/en/latest/usage.html#mismatch-between-output-of-html-and-latex-backends

.. _bibliography:

==============
 Bibliography
==============

.. bibliography:: biblio.bib
   :cited:
