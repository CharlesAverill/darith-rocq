# DArith

A library of theorems regarding the commutative ring of dual numbers
and their application in automatic differentiation.

## Building

```bash
# Install Dependencies
opam switch create rocq 4.14.2
opam pin add rocq-runtime 9.1.0
opam install rocq-prover dune

# Clone and build
git clone https://github.com/CharlesAverill/DArith && cd DArith
dune build
```
