FROM debian:latest

# YourKit setup instructions taken from https://www.yourkit.com/docs/java/help/docker.jsp
RUN set -x \
    && apt-get update \
    && apt-get install -y apt-transport-https gnupg wget unzip \
    && echo 'deb https://dl.bintray.com/sbt/debian /' >> /etc/apt/sources.list.d/sbt.list \
    && apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823 \
    && apt-get update \
    && apt-get install -y openjdk-8-jdk sbt \
    && wget -q https://www.yourkit.com/download/docker/YourKit-JavaProfiler-2019.1-docker.zip -P /tmp/ \
    && unzip /tmp/YourKit-JavaProfiler-2019.1-docker.zip -d /usr/local \
    && rm /tmp/YourKit-JavaProfiler-2019.1-docker.zip

# To connect to the port inside the container, start it like this:
# docker run -p 10001:10001 -p 8080:8080 <image-id>
EXPOSE 10001
EXPOSE 8080

ADD . evaluation/

RUN set -x \
    && cd evaluation \
    && sbt compile

# To profile inside the Docker container:
# sbt run -J-agentpath:/usr/local/YourKit-JavaProfiler-2019.1/bin/linux-x86-64/libyjpagent.so=port=10001,listen=all
