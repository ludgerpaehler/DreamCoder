(lang dune 3.0)

(name dreamcoder)
(using menhir 2.1)
(generate_opam_files true)

(package
 (name dreamcoder)
 (synopsis "Dreamcoder package")
 (description "")
 (depends
   core
   core_unix
   re2
   yojson
   vg
   cairo2
   ocaml-protoc
   zmq
   core_kernel
   ppx_deriving
   ppx_jane
   ppx_inline_test
   ppx_expect
 )

 )
