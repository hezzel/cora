# Status

We would like to apply for the following badges:

- Available:
    the artifact is hosted in zenodo.
- Functional:
    the artifact is functional and all the experiments and claims from the paper was verified.
    The code base contains documentation for the apis used and necessary for solving the problems in the paper, mainly the horpo termination module and terms module.
- Reusable:
    The core of this submission is the HORPO module (in app/src/main/java/cora/termination/Horpo.java),
    which has a very straightforward API:
    * Horpo.applicable(TRS trs)
    indicates whether a TRS satisfies the requirements to try to apply HORPO in the first place
    (that is, if the given TRS is an LCSTRS as described in the paper)
    * Horpo.run(TRS trs)
    executes Horpo, and returns either null if termination could not be confirmed, or detailed
    information on the precedence and sort orderings.

    The HORPO code is well-documented and closely follows the definition in section 4.3 of the paper,
    and the explanation of the implementation in section 5.  Hence, it can easily be reused for
    implementations of other Horpo versions, and adapted to work with different term libraries.
