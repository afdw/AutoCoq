(lang dune 3.8)

(name autocoq-plugin)

(generate_opam_files true)

(source
 (github afdw/AutoCoq))

(authors "Anton Danilkin")

(maintainers "Anton Danilkin")

(using coq 0.8)

(package
 (name autocoq-plugin)
 (synopsis "AutoCoq Coq plugin")
 (description "AutoCoq Coq plugin")
 (depends ocaml dune coq-core))
