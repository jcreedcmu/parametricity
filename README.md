Parametricity Agda Experiments
==============================

This repository is me thinking through some reading on internalized parametricity.
The high points are:

- [Interval/Axioms.agda](Interval/Axioms.agda) which postulates the
existence of an "interval type" $T$ with shape $S$, which is chosen in such a way that
the type $D$ bridge-discrete with respect to $T$. For $T$ to be "of shape $S$" means
that it is the same as $S$ with just a little bit of extra cohesion.

- [Interval/Gel.agda](Interval/Gel.agda) constructs a Gel type as a pushout. It proves
that `(t : T) → Gel R t` is the same thing as an element of the relation `R`.

- [Interval/Gel.agda](Interval/Endpoints.agda) shows that the fibers of the Gel type
at the endpoints are isomorphic to the chosen arms of the relevant relation.

- [Interval/Functoriality.agda](Interval/Functoriality.agda) shows that uniform maps
`(t : T) → Gel R₁ t → Gel R₂ t` are the same thing as relation homomorphisms
from `R₁` to `R₂`.
