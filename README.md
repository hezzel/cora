# cora

Cora is an analysis tool for constrained higher-order term rewriting.
At the moment only one technique is implemented (constrained HORPO), but this is
planned to be expanded in the future.

## Folder structure

This artifact is organized as follows:

```
├── Dockerfile
├── README.md
├── app
├── cora_distribution
├── gradle
├── gradlew
├── gradlew.bat
├── resources
└── settings.gradle.kts
```
Important folders are:
the ``app`` folder contains the source code and
``cora_distribution`` contains the binaries and scripts to run the experiments.

## Running the cora distribution

### Requirements:

- ``java`` runtime ``jre >= 1.8``
- the command ``z3`` should be available system-wide, so make sure ``z3``
is properly installed in your system.
  - Please check [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3) 
  for installation instructions for your system.

### Running cora on an input file
You can invoke ``cora`` using files present in ``./cora_distribution/benchmarks/``.
For instance,
to run ``cora`` in the file ``./cora_distribution/benchmarks/extra_examples/map.strs``,
we execute the following command (from the root of this artifact).

```bash
cd cora_distribution
./bin/app ./benchmarks/extra_examples/ex_06_fact.lctrs
```

If everything is fine, the output should be:

```bash
./bin/cora inputs/fact.lcstrs
YES

comp : (Int ⇒ Int) ⇒ (Int ⇒ Int) ⇒ Int ⇒ Int
fact : Int ⇒ (Int ⇒ Int) ⇒ Int
fact2 : Int ⇒ Int
All the standard theory symbols are also included.

comp(f, g, x) → f(g(x))
fact(n, k) → k(1) | n ≤ 0
fact(n, k) → fact(n - 1, comp(k, *(n))) | n > 0
fact2(n) → 1 | n ≤ 0
fact2(n) → n * fact2(n - 1) | n > 0
calc : f(x1,...,xk) → y [f(x1,...,xk) = y] for f ∈ Σ_{theory}

Constrained HORPO succeedings in orienting all rules, using the following settings:
  Precedence (all non-mentioned symbols have precedence -1 for theory symbols and 0 for other symbols):
    * : -1
    + : -1
    comp : 0
    fact : 1
    fact2 : 1
  Status (all non-mentioned symbols have status Lex):
    fact : Lex
  Well-founded theory orderings:
    ⊐_{Bool} = {(true,false)}
    ⊐_{Int} = {(x,y) | x > -1000 ∧ x > y }
```

The very first line tells if ``cora`` could successfully find a termination proof.

- ``YES`` output means a proof was found; and
- ``MAYBE`` output means no proof was found but non-termination is not proved.
- At the moment ``cora`` doesn't prove non-termination.

Notice that we navigated inside the distribution folder,
this is necessary for properly running of cora, as it needs the ``smtsolver`` executable
to be present.
It calls the smt solver externally.
Please make sure that whenever manually invoking ``cora``,
you are in the correct folder.

### Operating Systems

Cora has been tested on Unix-like systems:
Linux and macOS.
**It will not run on Windows.**

## Running cora from docker

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
- Finally, the contents of ``cora_distribution`` lies in ``/opt/cora`` inside the docker image.
```bash
cd /opt/cora
```
The scripts are ``run_exp_all.sh run_exp_extra.sh  run_exp_paper.sh``.
They execute all experiments, only extra experiments, and only the paper examples,
respectively.

## Building cora from source

In this version ``cora`` utilizes preview features of java-21.
So the latest version of jdk is needed.

### Build Dependencies

- ``jdk >= 21.0.1``, for instance
  [openjdk-21](https://openjdk.org/projects/jdk/21/).
- ``gradle >= 8.5``

Having the requirements above installed, to build ``cora`` just do:

```bash
./gradlew build
```
