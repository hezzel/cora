FROM amazoncorretto:21-alpine-full

RUN mkdir /opt/cora
RUN apk add z3
RUN apk add bash

COPY ./cora_distribution/bin /opt/cora/bin
COPY ./cora_distribution/lib /opt/cora/lib
COPY ./cora_distribution/benchmarks /opt/cora/benchmarks
COPY ./cora_distribution/smtsolver /opt/cora/smtsolver
COPY ./cora_distribution/run_exp_all.sh /opt/cora
COPY ./cora_distribution/run_exp_extra.sh /opt/cora
COPY ./cora_distribution/run_exp_paper.sh /opt/cora

RUN chmod oug+x /opt/cora/run_exp_all.sh
RUN chmod oug+x /opt/cora/run_exp_extra.sh
RUN chmod oug+x /opt/cora/run_exp_paper.sh
