# Agda-Metis [![Build Status](https://travis-ci.org/jonaprieto/agda-metis.svg?branch=master)](https://travis-ci.org/jonaprieto/agda-metis) [![DOI](https://zenodo.org/badge/84973849.svg)](https://zenodo.org/badge/latestdoi/84973849)

The *agda-metis* library is a formalisation in [Agda][agda] to reconstruct
syntactically the [Metis] inference rules for propositional logic. This library
works jointly with [Agda-Prop][agda-prop]. Both libraries are intended to
support output from the [Athena][athena] tool.

### Prerequisites

* [agda] 2.5.3+
* [agda-prop]

To install the required libraries see [Agda documentation](http://agda.readthedocs.io/en/latest/tools/package-system.html#installing-libraries).

### Installation

1. Clone this repository:

```
$ git clone https://github.com/jonaprieto/agda-metis.git
$ cd agda-metis
```

2. In order to test the installation of [agda-metis][agda-metis]
you can run some tests.

```
$ make test
```

### References

* Hurd, J. (2003). *First-order Proof Tactics In Higher-order Logic Theorem Provers*. Design and Application of Strategies/Tactics in Higher Order Logics, Number NASA/CP-2003-212448 in NASA Technical Reports, 56–68. Retrieved from http://www.gilith.com/research/papers

* Böhme, S., & Weber, T. (2010). *Fast LCF-Style Proof Reconstruction for Z3*. In M. Kaufmann & L. C. Paulson (Eds.), Interactive Theorem Proving: First International Conference, ITP 2010, Edinburgh, UK, July 11-14, 2010. Proceedings (pp. 179–194). Berlin, Heidelberg: Springer Berlin Heidelberg. https://doi.org/10.1007/978-3-642-14052-5_14

* Kanso, K., & Setzer, A. (2016).*A Light-weight Integration Of Automated And Interactive Theorem Proving*. Mathematical Structures in Computer Science, 26(1), 129–153. https://doi.org/10.1017/S0960129514000140

[haskell]: http://www.haskell.org
[issue]: http://github.com/jonaprieto/athena/issues/new
[tstp]:    http://www.cs.miami.edu/~tptp/TPTP/QuickGuide/
[metis]:   http://github.com/gilith/metis
[agda]:    http://github.com/agda/agda
[agda-prop]: http://github.com/jonaprieto/agda-prop
[agda-metis]: http://github.com/jonaprieto/agda-metis
[agda-stdlib]: http://github.com/agda/agda-stdlib
[problems]: http://github.com/jonaprieto/prop-pack
[athena]: http://github.com/jonaprieto/athena
