FROM debian:latest
RUN set -x \
    && apt-get update \
    && apt-get install -y apt-transport-https gnupg \
    && echo 'deb https://dl.bintray.com/sbt/debian /' >> /etc/apt/sources.list.d/sbt.list \
    && apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823 \
    && apt-get update \
    && apt-get install -y openjdk-8-jdk sbt
ADD . evaluation/
RUN set -x \
    && cd evaluation \
    && sbt run
