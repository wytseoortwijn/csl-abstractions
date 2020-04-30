---
layout: home
---

# CSL with process-algebraic abstractions
This repository hosts the formalisation and soundness proofs of the CSL program logic extended with process-algebraic program abstractions and fractional permissions, accompanying the Applied Sciencies journal article *"An Abstraction Technique for Verifying Shared-Memory Concurrency"*. 

This work is a generalisation of the work in [Wytse Oortwijn](https://www.pm.inf.ethz.ch/people/personal/woortwijn-pers.html){:target="_blank"}'s PhD Thesis titled [*Deductive Techniques for Model-Based Concurrency Verification*](https://doi.org/10.3990/1.9789036548984){:target="_blank"}, and combines Chapters 5 and 7 into a single logical framework. Moreover, it extends an earlier VMCAI'20 article titled [*"Practical Abstractions for Automated Verification of Shared-Memory Concurrency"*](https://doi.org/10.1007/978-3-030-39322-9_19){:target="_blank"}, which covers Chapter 5 of Wytse's Thesis.

The program logic has proof rules for verifying whether a program adheres to a process-algebraic abstraction, that specifies how segments of the program heap are allowed to evolve over time. Moreover, these abstractions allow proving (safety) properties over the evolution of the heap that are difficult to establish without the use of program abstractions (e.g., due to advanced program constructs like handling threads and locks).

This logic can be used to reason about concurrent and distributed, possibly non-terminating, software. The soundness proof is mechanised with the Coq proof assistant, version 8.11.0.



## Structure and documentation

The main files are:

- [**Prelude.v**](Prelude.html){:target="_blank"}: Defines the syntactic and semantic domains on which the formalisation is build, e.g., `Var`, `Val` and `ProcVar`. Also contains some preliminary definitions and results.
- [**Process.v**](Process.html){:target="_blank"}: The theory of process-algebraic program abstractions. Contains the syntax and semantics of the process algebra language, a definition of bisimulation, a proof that bisimilarity is an equivalence relation as well as a congruence for all connectives in the language, and soundness of an axiomatisation for the process language.
- [**Programs.v**](Programs.html){:target="_blank"}: The syntax and semantics of the programming language. Also contains the fault semantics, ghost semantics, and hybrid processes.
- [**Permissions.v**](Permissions.html){:target="_blank"}: Contains properties on (validity and disjointness of) fractional permissions.
- [**Heaps.v**](Heaps.html){:target="_blank"}: Contains definitions and properties on program heaps and permission heaps.
- [**ProcMap.v**](ProcMap.html){:target="_blank"}: Contains definitions and properties on process maps.
- [**Assertions.v**](Assertions.html){:target="_blank"}: Defines the syntax and semantics of the assertion language. Also contains logical entailment as well as soundness proofs of the entailment rules of the logic.
- [**Soundness.v**](Soundness.html){:target="_blank"}: Defines adequacy (i.e., what it means for a program to execute safely), the semantic meaning of Hoare triples, and contains the actual soundness proof of the program logic.

If one wishes to study the formalisation it is recommended to study the files in the order shown above, and perhaps to only skim over **Heap.v** and **ProcMap.v** and revisit them whenever needed.

The other files in the formalisation are (in alphabetical order):

- [**HeapSolver.v**](HeapSolver.html){:target="_blank"}: Contains tactics that provide more proof automation for working with heaps.
- [**PermSolver.v**](PermSolver.html){:target="_blank"}: Contains tactics that provide more proof automation for working with fractional permissions.
- [**ProcMapSolver.v**](ProcMapSolver.html){:target="_blank"}: Contains tactics that provide more proof automation for working with process maps.

