Parametricity Agda Experiments
==============================

This repository is me thinking through some reading on internalized parametricity.
The high points are [Interval/Axioms.agda](Interval/Axioms.agda) which postulates the
existence of an "interval type" $T$ with shape $S$, which is chosen in such a way that
the type $D$ bridge-discrete with respect to $T$. For $T$ to be "of shape $S$" means
that it is the same as $S$ with just a little bit of extra cohesion. The intent
is that maps $T \to \mathsf{Set}$ are then roughly equivalent (modulo some conerns
about discreteness) to $S$-ary relations.
