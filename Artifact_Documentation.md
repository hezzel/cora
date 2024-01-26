# Artifact Documentation

- Claims stated in the paper and supported by cora.
  - The paper makes the claim that all examples in the paper are handled. 
  This is indeed the case. You can check this by running the script ``run_exp_paper.sh``.
- Claims stated in the paper and not supported by cora.
  - The only other claim the paper makes regarding the artifact is a description of how the code for HORPO works. You can see the details in app/src/main/java/termination/horpo.java (the implementation closely follows the description in the paper).
- Expected running time of each experiments.
  - Each experiment takes about ``1s`` to run. 
  The total time to run all provided experiments is no longer than 1m.
