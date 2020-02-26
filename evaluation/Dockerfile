FROM debian:latest

# YourKit setup instructions taken from https://www.yourkit.com/docs/java/help/docker.jsp
RUN set -x \
    && apt-get update \
    && apt-get install -y apt-transport-https gnupg wget unzip \
    && echo 'deb https://dl.bintray.com/sbt/debian /' >> /etc/apt/sources.list.d/sbt.list \
    && apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823 \
    && apt-get update \
    && apt-get install -y openjdk-8-jdk-headless sbt

# Uncomment the below to enable YourKit profiling
#RUN set -x \
#    && wget -q https://www.yourkit.com/download/docker/YourKit-JavaProfiler-2019.1-docker.zip -P /tmp/ \
#    && unzip /tmp/YourKit-JavaProfiler-2019.1-docker.zip -d /usr/local \
#    && rm /tmp/YourKit-JavaProfiler-2019.1-docker.zip
#EXPOSE 10001

# To profile inside the Docker container, uncomment the -agentpath option in build.sbt
# and run the container with option `-p 10001:10001`

# To connect to the port inside the container, start it like this:
# docker run -p 8080:8080 <image-id>
#EXPOSE 8080

ADD . evaluation/

RUN set -x \
    && cd evaluation \
    && sbt compile
