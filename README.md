# freespec-guess
Simple proof of concept of [FreeSpec](https://github.com/edwinans/FreeSpec) and [coqffi](https://github.com/coq-community/coqffi) -- The Guess game.

This example is produced with the help of Thomas Letan ([**@lthms**](https://github.com/lthms)).

## Build
```
opam switch create . ocaml-base-compiler.4.11.1 --repositories "default,coq-released,coq-extra-dev" --description=freespec-guess
```

You need to have told Opam what `coq-released` and `coq-extra-dev`
are.  If you have not done it before, you can [read
here](https://github.com/coq/opam-coq-archive) how to setup it
correctly.  
`opam repo add coq-released https://coq.inria.fr/opam/released`

### Install Dependencies
`opam install . --deps-only`

## Run
To run the guess game:  
`dune build`  
`dune exec bin/main.exe`
