(lang dune 2.7)
(name semio)
(version 1.0)
(using menhir 1.0)
(generate_opam_files true)

(authors "Bill Duff <wduff11@gmail.com>")
(maintainers "Bill Duff <wduff11@gmail.com>")
(homepage "https://semio.com")
(bug_reports "https://semio.dev/issues")

(package
 (name semio)
 (synopsis "Implementation of semio, a programming language.")
 (depends
  (abbot (>= 1.0))
  (abbot_runtime (>= 1.0))
  (core (>= v0.14.0))
  (menhir (>= 20201201))
  (ocamlgraph (>= 2.0.0))
  (ppx_jane (>= v0.14.0))))
