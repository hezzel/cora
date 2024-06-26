FROM amazoncorretto:22-alpine-full

# Prepare the linux distribution
RUN mkdir /opt/cora
RUN apk add z3
RUN apk add bash unzip make

# Copy cora to this image and set its executable to the bin folder
COPY ./app/build/distributions/app.zip /tmp
RUN unzip -oq /tmp/app.zip -d /opt/cora
RUN ln -s /opt/cora/app/bin/app /bin/cora
COPY ./benchmarks /benchmarks
