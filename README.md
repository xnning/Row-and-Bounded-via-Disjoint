# Row and Bounded Polymorphism via Disjoint Polymorphism

This is the artifact of the paper [Row and Bounded Polymorphism via Disjoint
Polymorphism](https://xnning.github.io/papers/row-bounded.pdf) at [ECOOP
2020](https://2020.ecoop.org/).

> Polymorphism and subtyping are important features in mainstream OO languages.
> The most common way to integrate the two is via F<: style bounded
> quantification. A closely related mechanism is row polymorphism, which provides
> an alternative to subtyping, while still enabling many of the same applications.
> Yet another approach is to have type systems with intersection types and
> polymorphism. A recent addition to this design space are calculi with disjoint
> intersection types and disjoint polymorphism. With all these alternatives it is
> natural to wonder how they are related.
> 
> This paper provides an answer to this question. We show that disjoint
> polymorphism can recover forms of both row polymorphism and bounded
> polymorphism, while retaining key desirable properties, such as type-safety and
> decidability. Furthermore, we identify the extra power of disjoint polymorphism
> which enables additional features that cannot be easily encoded in calculi with
> row polymorphism or bounded quantification alone. Ultimately we expect that our
> work is useful to inform language designers about the expressive power of those
> common features, and to simplify implementations and metatheory of feature-rich
> languages with polymorphism and subtyping.

- [artifact.pdf](./artifact.pdf): Instructions of the artifact
- [CoqProofs](./CoqProofs): Coq proofs
- [paper.pdf](./artifact.pdf): Full paper with Appendix
