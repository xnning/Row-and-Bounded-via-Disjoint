# Coq Formalization Artifact

The artifact contains the Coq formalization of submission
"On The Expressive Power of Disjoint Polymorphism". We document
in detail how to build and compile the Coq proofs, as well as the proof
structure and organization.

## Structure

- `./elaborations`: All lemmas related to elaborations.
- `./operational-semantics`: All lemmas related to coherence in operational semantics.

### Differences

- Elaboration focuses only on type-preservation lemmas, while
  Operational-semantics contains the elaboration from Fi+ to Fco, and the
  coherence lemma for elaboration.
- Operational-semantics contains more files related to logical relation and
  contextually equivalence.
- Operational-semantics contains only the predicative subset of the systems, as
  the logical relation is only defined for Fi+'s predicative subset.
  
Other lemmas should be the same in these two versions.

## Building Instructions

Our Coq proofs are verified in **Coq 8.8.2**. We rely on two Coq libraries:
[`metalib`](https://github.com/plclub/metalib) for the locally nameless
representation in our proofs; and
[`coq-equations`](https://github.com/mattam82/Coq-Equations) for defining
logical relations using pattern matching.

### Prerequisites

1. Install Coq 8.8.2. The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.8.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq), then install `metalib`:
   1. Open terminal
   2. `git clone https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   4. `make install`

3. Install `coq-equations.1.0+8.8`, refer to [here](https://github.com/mattam82/Coq-Equations#installation).
   1. `opam repo add coq-released https://coq.inria.fr/opam/released`
   2. `opam install coq-equations.1.0+8.8`

### Build and Compile the Proofs

1. Type `make` in the terminal to build and compile the proofs (under one folder).

2. You should see something like the following:
   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQC file1.v
   COQC file2.v
   ......
   COQC filen.v
   ```
