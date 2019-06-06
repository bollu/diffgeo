# Formalizing Diffgeo in Coq using infinitesimal analysis

Since a lot of the constructions in differential geometry arise from universal
properties, most of them can be done by "type chasing": If the types fit,
then the construction works out. Examples include:

- Pushforwards
- Pullbacks
- Directional Derivatives

It would be nice to see how much something like `sledgehammer` can automatically
fill in.

So, let's build Diffgeo in Coq! But do we _really_ want to go through the suffering
of constructing reals with Dedekind cuts or cauchy sequences? I for one don't
enjoy analysis nearly enough to put myself through that.

Enter __infinitesimal analysis___ - A clean axiomatisation of real numbers
that crucially relies on living in constructive logic to create infinitesimals
such as `dx`, and provides axioms to perform "physicist-style" proofs
rigorously!

## References

- [Synthetic Differential Geometry (Blog post by Andrej Bauer)][sgd blog]
- First steps in syntehtic computability (Math inside the effective topos).
- Axiomatize R and then move on.



[sgd blog]: http://math.andrej.com/2008/08/13/intuitionistic-mathematics-for-physics/
