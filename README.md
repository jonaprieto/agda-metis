# Agda-Metis [![Build Status](https://travis-ci.org/jonaprieto/agda-metis.svg?branch=master)](https://travis-ci.org/jonaprieto/agda-metis) [![DOI](https://zenodo.org/badge/84973849.svg)](https://zenodo.org/badge/latestdoi/84973849)

This library aims to provide the necessary functions and theorems to reconstruct
proofs found by the automatic theorem prover, [Metis](https://github.com/gilith/metis).

### Requirements

* [Agda](https://github.com/agda/agda) version 2.5.1+
* [Agda Standard Library](https://github.com/agda/agda-stdlib/)
* [Agda-Prop Library](http://github.com/jonaprieto/agda-prop/)

### Installation

Clone this repository:

```
$ git clone http://github.com/jonaprieto/agda-metis.git
```

Add the path of this library to your library manager file, usually
located in `~/.agda/libraries`. For instance, my file looks like:

```bash
$ cat $HOME/.agda/libraries
/home/jonaprieto/agda-stdlib/standard-library.agda-lib
/home/jonaprieto/agda-prop/agda-prop.agda-lib
/home/jonaprieto/agda-metis/agda-metis.agda-lib
```

Find more information about installing libraries in Agda
[here](http://agda.readthedocs.io/en/latest/tools/package-system.html#installing-libraries).


### References

- Joe Leslie-Hurd. *Metis, an Automatic Theorem Prover.*
  http://www.gilith.com/software/metis/index.html and https://github.com/gilith/metis.

- Jonathan Prieto-Cubides and Alejandro Gomez-Londoño. 
  [*A proof tool for translating TSTP proofs to Agda code*](https://github.com/jonaprieto/tstp2agda/tree/deep)

