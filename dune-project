(lang dune 3.24)

(name fictol)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name fictol)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml
  dune
  (llvm (>= 18))       ; adjust to the version you target
  stdint
  ounit2
  extlib)
 (tags
  ("add topics" "to describe" your project)))

; (using menhir 3.0)
; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
