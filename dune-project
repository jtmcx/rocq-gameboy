(lang dune 3.21)
(using rocq 0.11)

(name rocq-gameboy)
(generate_opam_files)

(package
  (name rocq-gameboy)
  (synopsis "A GameBoy emulator written in Rocq")
  (license ISC)
  (depends
    (ocaml (>= 4.14))
    (dune (>= 3.21))
    rocq-core
    coq-itree
    coq-ext-lib
    coq-paco))
