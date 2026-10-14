# LinA-Epig
Amateur Computational epigraphy on Linear A.

Two Common Lisp tools over `corpus.sexp`, 1722 Linear A documents converted from lineara.xyz (John Younger's transliterations of GORILA).

## `linear-a.lisp`: corpus toolkit
Transliteration, annotation of the few understood elements (KU-RO "total", KI-RO "deficit", logograms, numerals), word frequencies, concordance, and **arithmetic auditing of tablet totals**: the method by which KU-RO's meaning was identified. For example it flags HT13, whose entries sum to 131 while the scribe wrote 130½.

```sh
sbcl --script linear-a.lisp          # demo
sbcl --load linear-a.lisp            # REPL, then in-package :linear-a
(concordance "KU-RO")
(word-frequencies :site "Zakros")
(audit-totals :site "Haghia Triada")
(show-document "HT13")
```

## `sigla-query.lisp`: SigLA's typed query language
A reimplementation of SigLA's (Salgarella & Castellan) typed λ-term search: queries are s-expression λ-terms over Document / Word / Sign primitives, type-checked with unification (polymorphic `exists`, `count`, ...), compiled to closures and run over the corpus. Also: SigLA word patterns (`ku-ro`, `ku-`, `-ro`, `ku--ro`, `ku-?-ro`), typed holes with suggestions, and parsing SigLA URLs.

```sh
sbcl --script sigla-query.lisp       # demo
(typecheck '(λ (d) (exists (λ (w) (matches "ku--ro" w)) (words d))))
(run-query '(λ (d) (= (site d) "Zakros")) :group-by 'site)
(search-words "-ro")
```
