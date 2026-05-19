(lang dune 3.21)
(using rocq 0.11)

(name DArith)

(generate_opam_files true)

(source
 (github CharlesAverill/DArith))

(authors
 "Charles Averill <charlesaverill20@gmail.com>")

(maintainers
 "Charles Averill <charlesaverill20@gmail.com>")

(license MIT)

(documentation https://github.com/CharlesAverill/DArith)

(package
 (name DArith)
 (synopsis "Dual numbers in Rocq")
 (description "A library of theorems regarding the commutative ring of dual numbers")
 (depends
   (dune (>= 3.21.0))
   (rocq (>= 9.0.0))))
