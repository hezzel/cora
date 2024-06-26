# cora

[![DOI](https://zenodo.org/badge/207259740.svg)](https://zenodo.org/doi/10.5281/zenodo.10460327)

Cora is an analysis tool for constrained higher-order term rewriting.
At the moment several techniques for termination analysis are implemented, and
in the future we hope to expand to other properties.

## Build Instructions

Currently,
we support only UNIX-like systems.
So you can build and run cora on linux or macOS (including M series macs).
**Windows is not supported**.

The build dependencies are listed below.

- ``jdk >= 22.0.1``, we recommend [openjdk-21](https://openjdk.org/projects/jdk/21/). 
  - Make sure that jdk is properly installed and that ``JAVA_PATH`` is properly set.
- ``gradle >= 8.8``
  - Gradle will then download the following additional dependencies from the [maven](https://central.sonatype.com) repositories.
    - ``guava:33.2.1-jre``
    - ``junit:jupiter:5.10.2``
- ``z3 >= 4.13.0``, check the [z3 git repository](https://github.com/Z3Prover/z3) 
for more details on how to install it on your system.
Z3 is also available in most package managers for linux distributions and also on brew (in macOS).
  - Cora does not use the ``z3`` java bindings. 
  The command ``z3`` should be available on your ``PATH``.

To build cora, simply run:

```bash
./gradlew build
```

## Installation
We have provided a make file for it.
Just run ```make``` and then ```make install```.
Cora will be installed at ``~/.cora``.

If you would like to run it from anywhere, please add the following line to your bash profile:

```bash
export PATH="$HOME/.cora/bin:$PATH"
```

Commonly, this is either ``~/.bashrc`` or ``~/.zshrc`` depending on which bash you are using.

### Running cora on an input file

You can invoke ``cora`` using files present in ``./benchmarks``.
For instance,
to run ``cora`` in the file ``./benchmarks/esop2024/factunit.lcstrs``,
we execute the following command (from the root of this artifact).

```bash
cora ./benchmarks/esop2024/factunit.lcstrs
```

If everything is fine, the output should be:

```bash
cora inputs/fact.lcstrs
YES
We consider the LCSTRS with only rule scheme Calc:

  Signature: comp   :: (Int → ret) → (Int → Int) → Int → ret
             error  :: ret
             fact   :: Int → (Int → ret) → ret
             return :: Int → ret

  Rules: comp(f, g, x) → f(g(x))
         fact(n, k) → error | n < 0
         fact(n, k) → k(1) | n = 0
         fact(n, k) → fact(n - 1, comp(k, [*](n))) | n > 0

The system is accessible function passing by a sort ordering that equates all sorts.

We start by computing the following initial DP problem:

  P1. (1) fact#(n, k) ➡ comp#(k, [*](n), X{9}) | n > 0
      (2) fact#(n, k) ➡ fact#(n - 1, comp(k, [*](n))) | n > 0

***** We apply the Graph Processor on P1.

There is only one SCC, so all DPs not inside the SCC can be removed:

  P2. (1) fact#(n, k) ➡ fact#(n - 1, comp(k, [*](n))) | n > 0

***** We apply the Integer Function Processor on P2.

We use the following integer mapping:

  J(fact#) = arg_1

We thus have:

  (1) n > 0 ⊨ n > n - 1 (and n ≥ 0)

All DPs are strictly oriented, and may be removed.  Hence, this DP problem is finite.
```

The very first line tells if ``cora`` could successfully find a termination proof.

- ``YES`` output means a proof was found; and
- ``MAYBE`` output means no proof was found but non-termination is not proved.

### Runtime arguments

Running ``cora`` without any file given as argument 
will produce the complete lis of options on how to run it.

```bash
cora
```

## Running cora from a docker image

We provided a docker file in the root of this artifact.
In order to run ``cora`` from the docker image, please proceed as follows.

- First make sure docker is properly installed on your system.
  - You can get installation instructions for your system at
  [https://docs.docker.com/get-docker/](https://docs.docker.com/get-docker/).
- The next step is to build the docker image. Proceed as follows:
```bash
  docker build --no-cache -t cora .
```
- We then run the docker image as follows:
```bash
docker run -i -it cora
```

The ``cora`` command will be available in this docker image. 
Benchmarks can be found at ``/benchmarks``.
