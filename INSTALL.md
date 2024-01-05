# Installatition Instructions

Information here is also present in the README.md file.

## Distribution

This artifact already contains binaries to run it directly, without
the need for building it.
Check the folder ``cora_distribution``.
You can install ``cora`` locally on your system by simply copying the distribution to anywhere you want and by adding the ``bin`` folder to your path.

### Build Dependencies

- ``jdk >= 21.0.1``, for instance
  [openjdk-21](https://openjdk.org/projects/jdk/21/).
- ``gradle >= 8.5``

Having the requirements above installed, to build ``cora`` just do:

```bash
./gradlew build
```

The distribution is built by gradlew inside ``./app/build/distributions``
there will be an ``app.zip`` file.
Unzip it and that is the binaries.

## Typical run of cora.

A typical run of cora should proceed as follows.

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
