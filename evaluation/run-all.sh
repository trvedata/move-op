#!/bin/bash
set -e

# Run this script with one argument: the interval between generated move
# operations, in microseconds, on each replica.
INTERVAL="${1?Please specify interval between operations (in microseconds)}"

# If false, runs in CRDT mode. If true, runs in leader-based mode.
USE_LEADER=false

# To run the experiments, log in to the AWS EC2 console and start up a c5.large
# instance running Ubuntu 18.04 in each of the three regions us-west-1, eu-west-1,
# and ap-southeast-1. Then fill in their IP addresses here:
US_WEST_1=13.52.240.53
EU_WEST_1=52.48.156.251
AP_SOUTHEAST_1=54.169.188.185

# Set up the security groups such that you can log in to the VMs by SSH (TCP port 22),
# and that they can all connect to each other on TCP port 8080.
# Then, to set up the VMs, log in to each by SSH and run the following:

# sudo apt-get update && sudo apt-get upgrade -y && sudo apt-get install -y apt-transport-https gnupg wget unzip
# echo "deb https://dl.bintray.com/sbt/debian /" | sudo tee -a /etc/apt/sources.list.d/sbt.list
# sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823
# sudo apt-get update && sudo apt-get install -y openjdk-8-jdk-headless sbt
# git clone https://github.com/trvedata/move-op.git && cd move-op/evaluation && sbt compile

# Once that setup is done, the following commands run the test script on the
# three instances concurrently, and then copy the log files off the instances
# into evaluation/data/logs/*.log.gz. Those logs are then analysed by the
# script evaluation/data/processing_times.sh.

if [ "$USE_LEADER" = "true" ]; then
    LOGDIR="data/logs-leader"
    # Define us-west-1 to be the leader
    ssh -i ~/.ec2/martin-aws-us-west-1.pem ubuntu@$US_WEST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL $USE_LEADER 0 &
    ssh -i ~/.ec2/martin-aws-eu-west-1.pem ubuntu@$EU_WEST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL $USE_LEADER 1 $US_WEST_1 &
    ssh -i ~/.ec2/martin-aws-ap-southeast-1.pem ubuntu@$AP_SOUTHEAST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL $USE_LEADER 2 $US_WEST_1 &
else
    LOGDIR="data/logs"
    ssh -i ~/.ec2/martin-aws-us-west-1.pem ubuntu@$US_WEST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL $USE_LEADER 1 $EU_WEST_1 $AP_SOUTHEAST_1 &
    ssh -i ~/.ec2/martin-aws-eu-west-1.pem ubuntu@$EU_WEST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL $USE_LEADER 2 $US_WEST_1 $AP_SOUTHEAST_1 &
    ssh -i ~/.ec2/martin-aws-ap-southeast-1.pem ubuntu@$AP_SOUTHEAST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL $USE_LEADER 3 $US_WEST_1 $EU_WEST_1 &
    wait
fi

cd "$(dirname "$0")"
mkdir -p "$LOGDIR"

scp -i ~/.ec2/martin-aws-us-west-1.pem ubuntu@$US_WEST_1:/home/ubuntu/move-op/evaluation/$LOGDIR/interval_$INTERVAL.log $LOGDIR/interval_${INTERVAL}_us_west_1.log
scp -i ~/.ec2/martin-aws-eu-west-1.pem ubuntu@$EU_WEST_1:/home/ubuntu/move-op/evaluation/$LOGDIR/interval_$INTERVAL.log $LOGDIR/interval_${INTERVAL}_eu_west_1.log
scp -i ~/.ec2/martin-aws-ap-southeast-1.pem ubuntu@$AP_SOUTHEAST_1:/home/ubuntu/move-op/evaluation/$LOGDIR/interval_$INTERVAL.log $LOGDIR/interval_${INTERVAL}_ap_southeast_1.log

gzip $LOGDIR/interval_${INTERVAL}_us_west_1.log $LOGDIR/interval_${INTERVAL}_eu_west_1.log $LOGDIR/interval_${INTERVAL}_ap_southeast_1.log
