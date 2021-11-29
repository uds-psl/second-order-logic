"Undecidability, Incompleteness, and Completeness of Second-Order Logic in Coq"

Compilation:
- tested with Coq versions 8.13.1 and 8.13.2 and Equations package 1.2.3+8.13
- if you use opam, these can be installed with "opam install coq.8.13.2" and "opam install coq-equations.1.2.3+8.13"
- run "make" in folder "coq", should take less than 5 min

Website:
- every statement (and other highlighted text) in "paper.pdf" is hyperlinked with coqdoc HTML in "coq/website"
- relative links only (not hosted on website for anonymity), needs to be accessed from the PDF in the same folder as this readme
- HTML can be recompiled by running "make website" in folder "coq"
- there is an issue with the relative links on MacOS machines depending on the PDF viewer in use, a variant that certainly works is opening the PDF with Google Chrome
