# vRelA sArma
This repository contains a correctness proof for a mapping scheme between the Release-Acquire memory model and a simplified Arm model, based on the works of [Risotto](https://dl.acm.org/doi/10.1145/3567955.3567962) and [Lasagne](https://dl.acm.org/doi/10.1145/3519939.3523719). In the spirit of their culinary naming convention, this proof has been named "Vrela Sarma" (hot, stuffed cabbage rolls), a traditional Serbian[^1] dish, enjoyed by many during the winter months.

[^1]: If this classification upset you, remember that it can be traditional in both our countries, peacefully and concurrently.

![Vrela Sarma](sarma.png)

## Overview

Concurrent programs allow multiple threads to access and modify shared memory. Since the execution order of instructions from different threads is unpredictable, one might consider all possible thread interleavings to understand the possible outcomes of a program. However, in reality, certain behaviors cannot be explained using this approach. These outcomes can be better understood using various memory consistency models, which dictate how out-of-order executions can affect the behavior of a program.

In some cases, we need to map between systems with different consistency models, such as when translating programming language primitives to an underlying architecture. This can be problematic when the target model is weaker than the source model, as it may lead to program behaviors in the target program that were not present in the source program. To prevent this, we must prove that the mapping scheme correctly transforms a program.

Using axiomatic semantics, we demonstrate that the proposed mapping guarantees correct behavior in the target program, while also ensuring the correctness of the source program. Specifically, we prove the following theorem, which is derived the aforemention works.

> *Consider P_t to be a program in the simplified Arm model that was mapped from a program P_s in the Release-Acquire model. For each well-formed, consistent target execution X_t of P_t there exists a consistent source execution X_s such that Behav(X_t) = Behav(X_s), where Behav(X) ≜ {⟨e.loc, e.val⟩ | e ∈ X.W ∧ [{e}]; X.mo = ∅ }.*

In the theorem we give the formal definition of execution behavior. Informally, it is defined as the final values of all shared memory locations.

## Code Navigation
The code consists of several parts that can be found in the `theories/` directory. The main components are:
- `Main.v` - The main mapping correctness proof.
- `model/` - Memory model definitions.
    - `Event.v` - Functions, predicates, lemmas and data structures for events.
    - `Execution.v` - Functions, predicates, lemmas and data structures for executions.
    - `RelAcq.v` - The release-acquire consistency model.
    - `SimplArm.v` - The simplified Arm consistency model.
- `proofs/` - Subparts of mapping proof.
    -  `util/` - Auxiliary files for the main proofs.
        - `SrcDst.v` - Hypotheses about the destination and specification of the source
        - `ObMap` - Mapping from the coherence relation in release-acquire to the ordered-before relation in simplied Arm.
        - `Relations` - Mapping of relations from the source to the destination.
        - `Misc` - Some auxiliary proofs.
    - `WellFormed` - Well-formedness of the source, following from well-formedness of the destination.
    - `Mapping` - Proof that source maps to the destination using the specified program transformations.
    - `Consistent` - Proof that the source is consistent in the release-acquire model.
    - `Behavior` - Proof that the source and destination have the same behavior.

## Building the project
This project was developed with Coq version 8.18.0 and depends on the [Hahn](https://github.com/vafeiadis/hahn) library. Make sure you have opam install. Then, you can install the dependency and build the project using the following commands:

```bash
./configure
make
```