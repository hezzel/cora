# Getting Started Guide - Artifact Evaluation

<description of cora and how it works?>

## Running from docker container
Please use either linux or macOS (Intel/ARM).

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

So to run the experiments, proceed as follows:
```bash
./run_exp_all.sh
```

That will execute all experiments.
