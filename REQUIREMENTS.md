# Requirements

This file describes the requirements for running cora in both host machine and docker image.
This information is also present in the README.md file.

- Software
  - OS
    - linux
    - macOs
    - Windows **is not supported**.
  - ``java``
    - runtime ``jre >= 21`` for running the application
    - building ``jdk >= 21``
  - the command ``z3`` should be available system-wide, so make sure ``z3``
    is properly installed in your system.
    - Please check [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3)
        for installation instructions for your system.
  - docker (for building/running the docker image)
  - Dockerfile is the docker file needed to build the docker image
- Hardware
There are no specific hardware requirement.
A reasonable laptop, reasonable meaning:
  - at least 2 cores
  - more or less 4gb of ram
is already enough.
- The build script requires an active internet connection.
