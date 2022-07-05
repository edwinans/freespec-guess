(lang dune 2.9)

(using coq 0.2)

(name freespec-guess)

(generate_opam_files true)

(source
 (github edwinans/freespec-guess))

(license MIT)

(authors "Edwin Ansari")

(maintainers "edwin.ocaml@gmail.com")

(package
 (name freespec-guess)
 (synopsis "Guess game in Coq using FreeSpec & coqffi")
 (description
  "A simple proof of concept of the FreeSpec framework: certified guess game containing side effects")
 (depends
  (dune
   (>= 2.5))
  (coq
   (= 8.13.2))
  (coq-freespec-core
   (>= 0.3))
  (coq-freespec-exec
   (>= 0.3))
  (coq-coqffi
   (>= 1.0.0))
  (coq-simple-io
   (>= 1.5))))
