A highly-available move operation for replicated trees
======================================================

This repository contains work on move operations in conflict-free replicated data types (CRDTs),
by Martin Kleppmann, Dominic P. Mulligan, Victor B. F. Gomes, and Alastair R. Beresford.

For background and details, please see these two papers:

* Martin Kleppmann, Dominic P. Mulligan, Victor B. F. Gomes, and Alastair R. Beresford.
  A highly-available move operation for replicated trees and distributed filesystems.
  Not yet formally published, but the LaTeX source is available in `paper/move-op.tex`.
* Martin Kleppmann. Moving elements in list CRDTs. 7th Workshop on Principles and Practice
  of Consistency for Distributed Data ([PaPoC](https://papoc-workshop.github.io/2020/)), April 2020.
  ([PDF](https://martin.kleppmann.com/papers/list-move-papoc20.pdf),
  [doi:10.1145/3380787.3393677](https://dl.acm.org/doi/abs/10.1145/3380787.3393677),
  [workshop presentation](https://martin.kleppmann.com/2020/04/27/papoc-list-move.html))


Proofs
------

The [Isabelle/HOL](http://isabelle.in.tum.de/) formalisation and proof of correctness can be found
in the following files:

* `proof.pdf` contains a PDF rendering of the whole proof.
* `Move.thy` contains the definition of the move algorithm for trees, a proof that a tree node
  has at most one parent, and a proof that the move operation is commutative.
* `Move_Acyclic.thy` contains a proof that the tree contains no cycles.
* `Move_SEC.thy` contains a proof that the algorithm provides Strong Eventual Consistency,
  as formalised in [our proof framework](https://dl.acm.org/doi/10.1145/3133933).
* `Move_Code.thy` contains an alternative definition of the algorithm that is efficiently
  executable, and a proof that it is equivalent to the earlier, more abstract algorithm.

To check the proofs, [download Isabelle](https://isabelle.in.tum.de/) and install it.
The `Move_SEC` theory depends on the definition of Strong Eventual Consistency in the
[Isabelle Archive of Formal Proofs](https://www.isa-afp.org/entries/CRDT.html). Download a
[release](https://www.isa-afp.org/download.html) of the AfP and
[configure your Isabelle installation to use it](https://www.isa-afp.org/using.html).

You can either run the Isabelle GUI interactively, or you can run it from the command line.
This is how you run it on Mac OS (adjust the path to your Isabelle installation):

    /Applications/Isabelle2019.app/Isabelle/bin/isabelle build -D .

The Isabelle-generated Scala source is written to `evaluation/src/main/scala/Move_Code.scala`,
where it is picked up by the evaluation (see below).


Papers
------

There are two papers in the `paper` directory:

* *A highly-available move operation for replicated trees and distributed filesystems* is in `paper/move-op.tex`
* *Moving elements in list CRDTs* is in `paper/list-move.tex`

To build PDFs of the papers with LaTeX: 

    cd paper
    make move-op.pdf list-move.pdf


Evaluation
----------

In `evaluation/src/main/scala/TestReplica.scala` there is a simple network server and client
that is used to evaluate the performance of the algorithm. To build it, you need
[sbt](https://www.scala-sbt.org/) installed; then you can run:

    cd evaluation
    sbt compile

**Note:** annoyingly, the Isabelle-generated code contains classes whose name differs only in
case. For this reason, it cannot be compiled and run on a case-insensitive filesystem (macOS,
Windows): the class files generated by the compiler would clash. You need to build it on Linux
instead. For people running other OSes, there is a Docker setup in `evaluation/Dockerfile`
that installs sbt and compiles the source. After
[installing Docker](https://www.docker.com/get-started) you can run this:

    # Run this in the root directory of this repository,
    # not in the `evaluation` directory
    docker build -t move-op:latest evaluation
    docker run -it --rm move-op /bin/bash

    # Then run this inside the container to watch source files for changes:
    cd evaluation && sbt ~compile

    # Edit a file outside of the container, and then copy it into the
    # container to compile it, like this:
    docker cp evaluation/src/main/scala/TestReplica.scala 10c36574237a:/evaluation/src/main/scala
    # Replace 10c36574237a with the running container ID (see `docker ps`)

To run on AWS, log into the AWS Management Console in
[us-west-1](https://us-west-1.console.aws.amazon.com/console/home?region=us-west-1),
[eu-west-1](https://eu-west-1.console.aws.amazon.com/console/home?region=eu-west-1), and
[ap-southeast-1](https://ap-southeast-1.console.aws.amazon.com/console/home?region=ap-southeast-1) respectively.
In each region, launch a `c5.large` instance running Ubuntu 18.04.
(Hint: using the *request spot instance* feature can be considerably cheaper,
but the user interface is a nightmare.)

Configure their security groups so that you can log in via SSH (TCP port 22),
and so that the three instances can talk to each other on TCP port 8080.

Modify the script `evaluation/run-all.sh` to contain the IP addresses of your
instances, and the location of the SSH private keys on your filesystem.
Manually log in to each of the instances as shown in that script, and run the
following one-off setup on each:

    sudo apt-get update && sudo apt-get upgrade -y && sudo apt-get install -y apt-transport-https gnupg wget unzip
    echo "deb https://dl.bintray.com/sbt/debian /" | sudo tee -a /etc/apt/sources.list.d/sbt.list
    sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823
    sudo apt-get update && sudo apt-get install -y openjdk-8-jdk-headless sbt
    git clone https://github.com/trvedata/move-op.git && cd move-op/evaluation && sbt compile

Once that setup is done, you can run the script `evaluation/run-all.sh` from
your local machine to perform a test run on all three instances concurrently.
It takes one argument: the interval between successive move operations generated
on each replica, in microseconds.

The script logs into the instances by SSH, updates the configuration, runs the
experiment, and copies the logs off the instances into `evaluation/data/logs/*.log.gz`.
Each test run lasts for 10 minutes and then automatically shuts down.

Those logs are then analysed by the script in `evaluation/data/processing_times.sh`.
